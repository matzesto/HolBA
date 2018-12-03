(* Vim users execute the following loads *)
(*
app load ["HolKernel", "Parse", "boolLib" ,"bossLib"];
app load ["wordsTheory", "bitstringTheory"];
app load ["bir_auxiliaryTheory", "bir_immTheory", "bir_valuesTheory"];
app load ["bir_imm_expTheory", "bir_mem_expTheory",  "bir_symb_envTheory"];
app load ["bir_programTheory", "bir_expTheory"];
app load ["llistTheory", "wordsLib"];
*)


open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_valuesTheory;
open bir_imm_expTheory bir_mem_expTheory bir_envTheory;
open bir_expTheory;
open bir_programTheory;
open llistTheory wordsLib;
open bir_symb_envTheory;

val _ = new_theory "bir_symbexec";



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
  bsst_environ      : bir_symb_environment_t; (* Mapping Vars to Exps *)
  bsst_pred         : bir_exp_t; (* Potentially define own Datatype *)
  bsst_status       : bir_status_t;
 
 |>`;
    



(* ------------------------------------------------------------------------- *)
(* Symbolic State                                                            *)
(* ------------------------------------------------------------------------- *)


(* Initially, Environment is empty and predicate set to True *)
val bir_symb_state_init_def = Define `bir_symb_state_init p = <|
    bsst_pc         := bir_pc_first p;
    bsst_environ    := bir_symb_empty_env;
    bsst_pred       := BExp_Const (Imm1 1w);  (* Invent real Booleans later on *)
    bsst_status     := BST_Running |>`;


val bir_symb_state_set_failed_def = Define `
    bir_symb_state_set_failed st = 
    st with bsst_status := BST_Failed`;



(* ------------------------------------------------------------------------- *)
(* Eval certain expressions                                                  *)
(* --------------------------------------------------------------------------*)

val bir_symb_eval_label_exp_def = Define `
    (bir_symb_eval_label_exp (Concrete imm) (env: bir_symb_environment_t) 
        = SOME (BL_Address imm)) ∧
    (bir_symb_eval_label_exp (Symbolic exp) env = NONE)`; (* Tricky case *)


val bir_symb_eval_exp_def = Define `
    (bir_symb_eval_exp (BExp_Const n) env = BVal_Imm n) /\
    
    (bir_symb_eval_exp (BExp_Den v ) env = bir_symb_env_read v env) ∧
    
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

(* ------------------------------------------------------------------------- *)
(* Symbolic Execution Semantics                                              *)
(* ------------------------------------------------------------------------- *)


 
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
    case bir_symb_eval_label_exp le st.bsst_environ of 
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
    bir_symb_exec_stmt_cjmp p ex l1 l2 (st: bir_symb_state_t) = 
    let st_true     = bir_symb_exec_stmt_jmp p l1 st in
    let st_false    = bir_symb_exec_stmt_jmp p l2 st in
    [st_true with bsst_pred  := BExp_BinExp BIExp_And (st_true.bsst_pred)  ex;
      st_false with bsst_pred := BExp_BinExp BIExp_And (st_false.bsst_pred) 
                                    (BExp_UnaryExp BIExp_Not ex);
    ]`;


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
    case (bir_env_write v (bir_eval_exp ex st.bsst_environ) st.bsst_environ) of 
    | SOME env => (st with bsst_environ := env)
    | NOEN => st with bsst_status := BST_Failed
`;


(* Basic Statement execution *)
val bir_symb_exec_stmtB_def = Define `
    (bir_symb_exec_stmtB (BStmt_Declare v) st  
        = bir_symb_exec_stmt_declare (bir_var_name v) (bir_var_type v) st) ∧
    (bir_symb_exec_stmtB (BStmt_Assign v ex) st 
        = bir_symb_exec_stmt_assign v ex st) ∧
    (* Ignore all other statement so far *)
    (bir_symb_exec_stmtB (_)  st  = st)`;

(* Execute one statement *)
val bir_symb_exec_stmt_def = Define`
    (bir_symb_exec_stmt (p: 'a bir_program_t) (BStmtB (bst: 'a bir_stmt_basic_t)) (st: bir_symb_state_t) 
        = [bir_symb_exec_stmtB bst st]) ∧
    (bir_symb_exec_stmt p (BStmtE (bst: bir_stmt_end_t)) st 
        = (bir_symb_exec_stmtE p bst st))
    `;
val _ = export_theory();
