(* Vim users execute the following loads *)
(*
app load ["HolKernel", "Parse", "boolLib" ,"bossLib"];
app load ["wordsTheory", "bitstringTheory"];
app load ["bir_auxiliaryTheory", "bir_immTheory", "bir_valuesTheory"];
app load ["bir_imm_expTheory", "bir_mem_expTheory",  "bir_symb_envTheory"];
app load ["bir_programTheory", "bir_expTheory", "bir_envTheory"];
app load ["llistTheory", "wordsLib"];
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory;
open bir_programTheory;
open llistTheory wordsLib;

open bir_envTheory bir_symb_envTheory;

val _ = new_theory "bir_symb_exec";


(* ------------------------------------------------------------------------- *)
(* Datatypes                                                                 *)
(* ------------------------------------------------------------------------- *)


(* *
 * Symbolic State contains of:
 * PC: current program counter 
 * environment: Mapping vars to expressions 
 * memory: Mapping memory addresses to expressions
 * pred: expression representing the path condition
 * bsst_status : a status bit (mainly used for errors) 
 * *)
val _ = Datatype `bir_symb_state_t = <|
  bsst_pc           : bir_programcounter_t; 
  bsst_environ      : bir_var_environment_t; (* Mapping Vars to Exps *)
  bsst_pred         : bool; (* Path predicate *)
  bsst_status       : bir_status_t;
 |>`;
    

val CONJ_def = Define `
    CONJ a b = a ∧ b`;

(* ------------------------------------------------------------------------- *)
(* Symbolic State                                                            *)
(* ------------------------------------------------------------------------- *)


(* Initially, Environment is empty and predicate set to True *)
val bir_symb_state_init_def = Define `bir_symb_state_init p env = <|
    bsst_pc         := bir_pc_first p;
    bsst_environ    := env;
    bsst_pred       := T;  (* Invent real Booleans later on *)
    bsst_status     := BST_Running |>`;


val bir_symb_state_set_failed_def = Define `
    bir_symb_state_set_failed st = 
    st with bsst_status := BST_Failed`;

val bir_symb_state_is_terminated_def = Define `
    bir_symb_state_is_terminated st = 
        if st.bsst_status = BST_Running then F else T`;

(* ------------------------------------------------------------------------- *)
(* Eval certain expressions  This is TODO                                    *)
(* However, should be mostly the same as concrete evaluation                 *)        
(* ------------------------------------------------------------------------- *)
(*
val bir_symb_eval_exp_def = Define `
    (bir_symb_eval_exp (BExp_Const n) env = BVal_Imm n) /\
    
    (bir_symb_eval_exp (BExp_Den v ) env = bir_env_read v env) ∧
    
    (bir_symb_eval_exp (BExp_Cast ct e ty) env = (
        bir_symb_eval_cast ct (bir_symb_eval e env) ty )) ∧
    
    (bir_symb_eval_exp (BExp_UnaryExp et e) env = (
        bir_symb_eval_unary_exp et (bir_symb_eval_exp  env))) ∧
    
    (bir_symb_eval_exp (BExp_BinPred pt e1 e2) env = (
        bir_symb_eval_bin_pred pt 
            (bir_symb_eval_exp e1 env) 
            (bir_symb_eval_exp e2 env)) ∧

    (bir_symb_eval_exp (BExp_MemEq e1 e1) env = 
        bir_symb_eval_memeq 
            (bir_symb_eval_exp e1 env) (bir_symb_eval_exp e2 env)) ∧

    (bir_symb_eval_exp (BExp_IfThenElse c et ef) env = 
        bir_symb_eval_ifthenelse 
            (bir_symb_eval_exp c enc) 
                (bir_symb_evl_exp et env) (bir_symb_eval_exp ef env)) ∧

    (bir_symb_eval_exp (BExp_Load mem_e a_e en ty) env = 
        bir_symb_eval_load 
            (bir_symb_eval_exp mem_e env) (bir_symb_eval_exp) en ty) ∧

    (bir_symb_eval_exp (BExp_Store mem_e a_e en v_e) env = 
        bir_symb_eval_store (bir_symb_eval_exp mem_e env) 
            (bir_symb_eval_exp a_e env) en (bir_symb_eval_exp v_e env))`;
 *)
(* ------------------------------------------------------------------------- *)
(* Symbolic Execution Semantics                                              *)
(* ------------------------------------------------------------------------- *)

(* We can have symbolic label expressions, these are to be 
 * "solved" with SAT solver and every possible solution to be considered *)
val bir_symb_eval_label_exp_def = Define `
    (bir_symb_eval_label_exp (BLE_Label l) env = SOME l) ∧
    (bir_symb_eval_label_exp (BLE_Exp e) env = 
        case bir_eval_exp e env of
        | BVal_Imm i => SOME (BL_Address i)
        | _ => NONE)`;
 
(********************)
(* Jumps/Halt       *)
(********************)

(* direct jump *)
val bir_symb_exec_stmt_jmp_to_label_def = Define`
    bir_symb_exec_stmt_jmp_to_label p (l: bir_label_t) (st: bir_symb_state_t) = 
    if (MEM l (bir_labels_of_program p)) then 
      st with bsst_pc := bir_block_pc l
    else (st with bsst_status := (BST_JumpOutside l))`;
    

(* We ignore symbolic/indirect jump targets currently! *)  
val bir_symb_exec_stmt_jmp_def = Define `
    bir_symb_exec_stmt_jmp 
        (p: 'a bir_program_t) (le: bir_label_exp_t) (st: bir_symb_state_t) = 
    case bir_eval_label_exp le st.bsst_environ of 
    | NONE   => bir_symb_state_set_failed st 
    | SOME l => bir_symb_exec_stmt_jmp_to_label p l st`;

(* End of execution *)
val bir_symb_exec_stmt_halt_def = Define `
    bir_symb_exec_stmt_halt ex (st: bir_symb_state_t) = 
    (st with bsst_status := BST_Halted (bir_eval_exp ex st.bsst_environ))`;

(* Conditional, so "fork":
 * Return a list containing of two states with 
 * updated path predicate accordingly 
 * TODO: rewrite with Roberto's method to solve conditional jump
 *)
val bir_symb_exec_stmt_cjmp_def = Define `
    bir_symb_exec_stmt_cjmp  p (BExp_Den (BVar reg BType_Bool)) l1 l2 st = 
    case (bir_env_lookup reg st.bsst_environ) of 
      SOME (ty, NONE)   => [bir_symb_state_set_failed st]
    | SOME (ty, SOME v) => 
        case (bir_dest_bool_val v) of 
         SOME b => 
          let st_true  = bir_symb_exec_stmt_jmp p l1 st in
          let st_false = bir_symb_exec_stmt_jmp p l2 st in
            [st_true  with bsst_pred := CONJ  st_true.bsst_pred b;
             st_false with bsst_pred := CONJ st_false.bsst_pred (~b)]
        | NONE =>  [bir_symb_state_set_failed st]
    | NONE              => [bir_symb_state_set_failed st]`; 


(* Execute "End" (Jump/Halt) Statement *)
val bir_symb_exec_stmtE_def = Define `
    (bir_symb_exec_stmtE p (BStmt_Jmp l) st = [bir_symb_exec_stmt_jmp p l st]) /\ 
    (bir_symb_exec_stmtE p (BStmt_CJmp e l1 l2 ) st =
         bir_symb_exec_stmt_cjmp p e l1 l2 st ) ∧ 
    (bir_symb_exec_stmtE p (BStmt_Halt ex) st = [bir_symb_exec_stmt_halt ex st])`;


(********************)
(* Declare / Assign *)
(********************)

(* *
 * only declare when unbound
 * Is this specified in BIL? 
 * *)
val bir_symb_exec_stmt_declare_def = Define `
    bir_symb_exec_stmt_declare var_name var_type st = 
    if (bir_env_varname_is_bound st.bsst_environ var_name) then 
      (st with bsst_status := BST_Failed)
    else (
        case (bir_env_update var_name (bir_declare_initial_value var_type) var_type
          st.bsst_environ) of 
           | SOME env =>  (st with bsst_environ := env)
           | NONE => st with bsst_status := BST_Failed
    )
`;


(* Assign only when variable is bound
 * Is this specified in BIL? *)
val bir_symb_exec_stmt_assign_def = Define `
    bir_symb_exec_stmt_assign v ex st = 
    case (bir_symb_env_write v (bir_eval_exp ex st.bsst_environ) st.bsst_environ) of 
    | SOME env => (st with bsst_environ := env)
    | NONE => st with bsst_status := BST_Failed`;

(* Is there something interesting here? *)
val bir_symb_exec_stmt_assert_def = Define `
    bir_symb_exec_stmt_assert v ex st = 
    let
      env_o = bir_symb_env_write v (bir_eval_exp ex st.bsst_environ) st.bsst_environ
    in 
      case env_o of 
      | SOME env => (st with bsst_environ := env)
      | NONE => bir_symb_state_set_failed st`;

(* Basic Statement execution *)
val bir_symb_exec_stmtB_def = Define `
    (bir_symb_exec_stmtB (BStmt_Declare v) st  
        = bir_symb_exec_stmt_declare (bir_var_name v) (bir_var_type v) st) ∧
    (bir_symb_exec_stmtB (BStmt_Assign v ex) st 
        = bir_symb_exec_stmt_assign v ex st) ∧
    (* 
    (bir_symb_exec_stmtB (BStmt_Assert ex) st 
        =  bir_symb_exec_stmt_assert ex st) ∧ *)
    (* Ignore all other statement so far *)
    (bir_symb_exec_stmtB (_)  st  = st)`;

(* Execute one statement *)
val bir_symb_exec_stmt_def = Define`
    (bir_symb_exec_stmt (p: 'a bir_program_t) (BStmtB (bst: 'a bir_stmt_basic_t)) (st: bir_symb_state_t) 
        = [bir_symb_exec_stmtB bst st]) ∧
    (bir_symb_exec_stmt p (BStmtE (bst: bir_stmt_end_t)) st 
        = (bir_symb_exec_stmtE p bst st))
    `;


(* ---------------------------------------------------- *)
(* Execute a program                                    *)
(* -----------------------------------------------------*)

(* Execute a Basic Block  *)
val bir_symb_exec_stmtB_list_def = Define `
    (bir_symb_exec_stmtB_list (p: 'a bir_program_t) (st: bir_symb_state_t)
        [] = st) ∧
    (bir_symb_exec_stmtB_list p st (stmt :: stmt_list) = 
        bir_symb_exec_stmtB_list p (bir_symb_exec_stmtB stmt st) stmt_list)`;


val bir_symb_exec_blk_def = Define `
    (bir_symb_exec_blk 
        (p: 'a bir_program_t) (blk: 'a bir_block_t) (st: bir_symb_state_t ) = 
        bir_symb_exec_stmtE p (blk.bb_last_statement) 
            (bir_symb_exec_stmtB_list p st (blk.bb_statements))
    )`;
        
val bir_symb_exec_first_blk_def = Define`
    (bir_symb_exec_first_blk 
        (BirProgram (blk_list : ('a bir_block_t) list)) (st: bir_symb_state_t) = 
        bir_symb_exec_blk (BirProgram blk_list) (HD blk_list) st)`;

(* Execute each BB  in a program *)

val bir_symb_exec_label_block_def = Define`
    bir_symb_exec_label_block (p: 'a bir_program_t) (st: bir_symb_state_t) = 
    case (bir_get_program_block_info_by_label p st.bsst_pc.bpc_label) of 
    | NONE => [bir_symb_state_set_failed st] 
    | SOME (_, blk) => bir_symb_exec_blk p blk st`;
    

(* We build something similar to a CFG where each node 
 * is a sysmbolic state representing the execution of one BB
 * Remark: Each BB has exactly 
 * Zero (Leaf) , One (UnNode)  or Two (BinNode) children nodes *)
val _ = Datatype `bir_symb_tree_t = 
  | Leaf bir_symb_state_t 
  | BinNode bir_symb_tree_t bir_symb_state_t bir_symb_tree_t
  | UnNode bir_symb_tree_t bir_symb_state_t`;




val bir_symb_exec_init_symb_tree_def = Define `
    bir_symb_exec_init_symb_tree (st: bir_symb_state_t) 
     = Leaf st`;



(* only execute one node *)
val bir_symb_exec_node_def = Define `
    (bir_symb_exec_node (p: 'a bir_program_t) (Leaf st) = 
        case st.bsst_status of 
        | BST_Running => 
            case (bir_symb_exec_label_block p st) of 
            | [st'] => UnNode  (Leaf st') st
            | [st'; st''] => 
                BinNode (Leaf st') st (Leaf st'')
            | _ => Leaf st (* Should not happen *)
        | _ => Leaf st) /\
    (bir_symb_exec_node p (BinNode ltree st rtree) = 
        BinNode (bir_symb_exec_node p ltree) st (bir_symb_exec_node p rtree)) /\
    (bir_symb_exec_node p (UnNode tree st) = 
        UnNode (bir_symb_exec_node p tree) st)`;


(* Execute n steps  *)
(* 
val bir_symb_exec_build_tree_def = Define `
    (bir_symb_exec_build_tree (p: 'a bir_program_t) (Leaf st) (n:num) = 
    case n of 
       | 0 => (Leaf st)
       | _ => 
        (case st.bsst_status of 
        | BST_Running => 
            (case (bir_symb_exec_label_block p st) of 
            | [st'] => UnNode  (Leaf st') st
            | [st'; st''] => 
                BinNode 
                    (bir_symb_exec_node p (Leaf st') (n-1)) 
                    st 
                    (bir_symb_exec_node p(Leaf st'') (n-1)))
        | BST_Halted _ => Leaf st
        | BST_Faild => Leaf st           
        | BST_AssumptionViolated => Leaf st
        | BST_AssertionViolated => Leaf st
        | BST_JumpOutside _ => Leaf st)) ∧ 
    (bir_symb_exec_build_tree p (BinNode ltree st rtree) n = 
    case n of 
       | 0 => (BinNode ltree st rtree)
       | _ =>  BinNode 
            (bir_symb_exec_build_tree p ltree (n-1)) st 
            (bir_symb_exec_build_tree p rtree (n-1))) ∧
    (bir_symb_exec_build_tree p (UnNode tree st) n = 
    case n of 
       | 0 => (UnNode tree st)
       | _ => UnNode (bir_symb_exec_node p tree (n-1))  st
    )`;
 *)
(* get rid of the three redundatnt base cases *)
val bir_symb_exec_build_tree_def = Define `
    (bir_symb_exec_build_tree (p: 'a bir_program_t) tree 0 = tree ) ∧
    (bir_symb_exec_build_tree (p: 'a bir_program_t) tree (n: num) = 
        case tree of 
        | Leaf st =>
            (case st.bsst_status of 
             | BST_Running => 
                (case (bir_symb_exec_label_block p st) of 
                 | [st'] => 
                     UnNode  (bir_symb_exec_build_tree p (Leaf st') (n-1)) st
                 | [st'; st''] => 
                    BinNode 
                        (bir_symb_exec_build_tree p (Leaf st') (n-1)) 
                        st 
                        (bir_symb_exec_build_tree p(Leaf st'') (n-1)))
             | BST_Halted _ => Leaf st
             | BST_Faild => Leaf st           
             | BST_AssumptionViolated => Leaf st
             | BST_AssertionViolated => Leaf st
             | BST_JumpOutside _ => Leaf st)
             
         | UnNode tree' st => UnNode (bir_symb_exec_build_tree p tree' (n-1)) st
         | BinNode ltree st rtree => BinNode
            (bir_symb_exec_build_tree p ltree (n-1)) st
            (bir_symb_exec_build_tree p rtree (n-1)))`;


val _ = export_theory();
