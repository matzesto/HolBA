(* 
Vim Plugin users only:
load "finite_mapSyntax";
load "finite_mapSyntax";
load "finite_mapLib";

*)

open HolKernel boolLib bossLib;
open finite_mapTheory finite_mapSyntax finite_mapLib;
open listSyntax;
open bir_envSyntax bir_envTheory;
open bir_programSyntax bir_programTheory;
open bir_typing_progTheory;
open optionTheory;


(**
 * This is more experimental
 * Don't assume it to be correct!
 **)


val _ = new_theory("bir_symbinit");

val bir_check_symbol_def = Define `
    (bir_check_symbol v (BEnv env) =
      case bir_env_lookup (bir_var_name v) (BEnv env) of
      | SOME _ => (BEnv env)
      | NONE   => (BEnv (env |+ ((bir_var_name v), (bir_var_type v), NONE))))`;

val test_exec_vars_def = Define `
    test_exec_vars (p: 'a bir_program_t) (state: bir_state_t) =
    case (bir_get_current_statement p state.bst_pc) of
    | NONE => NONE
    | SOME (BStmtB stmt)  =>
      case stmt of
      | (BStmt_Assign v ex) => SOME (v)
      | (BStmt_Declare v) => SOME (v)
      | _ => NONE
    | _ => NONE
`;

(* Variable in state with NONE denotes symbolic,
 * TODO: check wether this collides with something 
 * Is it more efficient to lookup before adding? *)
val bir_add_symbolic_var_def = Define `
    bir_add_symbolic_var (BEnv env) (BVar name ty) = 
        BEnv (env |+ (name, ty, NONE ))`;


val bir_add_symbolic_var_stmt_def = Define `
    ( bir_add_symbolic_var_stmt env (BStmt_Declare v) = 
        bir_add_symbolic_var env v ) /\
    ( bir_add_symbolic_var_stmt env (BStmt_Assign v _) = 
        bir_add_symbolic_var env v)`;

val bir_add_symbolic_vars_stmts_def = Define `
    ( bir_add_symbolic_vars_stmts [] env = env) /\
    ( bir_add_symbolic_vars_stmts (stmt::stmtlst) env = 
        bir_add_symbolic_vars_stmts stmtlst (bir_add_symbolic_var_stmt env stmt)    
    )`;

val bir_add_symbolic_vars_block_def = Define `
    bir_add_symbolic_vars_block env (block: 'a bir_block_t) = 
        bir_add_symbolic_vars_stmts (block.bb_statements) env`;

val bir_add_symbolic_vars_prog_def = Define `
    bir_add_symbolic_vars_prog  (blck_lst) env = 
    case blck_lst of 
    | [] => env
    | (blck::blck_lst') => 
        bir_add_symbolic_vars_prog (blck_lst')
            (bir_add_symbolic_vars_block env blck)`;

val init_state_def = Define `
    init_state (BirProgram blck_lst) env = 
    bir_add_symbolic_vars_prog blck_lst env`;


val _ = export_theory();
