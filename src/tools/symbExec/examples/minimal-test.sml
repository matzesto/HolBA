(* 
Vim Plugin users only:
load "finite_mapSyntax";
load "finite_mapSyntax";
load "finite_mapLib";

load "minimalBinaryTheory";
app load ["bir_symbexecTheory", "bir_symbinitTheory"];
*)

open HolKernel boolLib bossLib;
open finite_mapTheory finite_mapSyntax finite_mapLib;
open minimalBinaryTheory;
open listSyntax;
open bir_envSyntax bir_envTheory;
open bir_programSyntax bir_programTheory;
open bir_typing_progTheory;
open optionTheory;
open bir_symbexecTheory bir_symbinitTheory;


(*
 * This file can and should be used to play around with the code
 * To try other binaries, either change and recompile the "minimal" binary 
 * Or add another one.
 *
 * Please don't assume it's compiling here :-)
 *)


(* The binary we want to analyze *)
val minimal_prog = ((snd o dest_comb o concl) minimal_arm8_THM);
val minimal_blocks = (fst o dest_list o dest_BirProgram) minimal_prog;


(* For the beginning, we only care about the first block *)
val first_block = hd minimal_blocks;

(* destruct block *)
val (a, b, c) = dest_bir_block first_block;
val (l, ty) = listSyntax.dest_list b;


val st = EVAL ``bir_state_init ^minimal_prog``;

val empty_state = ``<|
    bst_pc      := <| bpc_label:= BL_Address (Imm64 0x400570w); bpc_index:= 0 |>;
    bst_environ := BEnv (FEMPTY |+ ("SP_EL0", ((BType_Imm Bit64), SOME (BVal_Imm (Imm64 0x1337w)))));
    bst_status  := BST_Running |>``;


val pc = ``<| bpc_label := BL_Address (Imm64 0x400570w); bpc_index := 0 |>``;
val e = EVAL ``bir_get_current_statement ^minimal_prog ^pc``;
val e = EVAL ``bir_state_is_terminated ^empty_state``;



(* This should act as an example on how to use rewriting, 
 * is is certainly NOT correct! 
 * *)

val e = EVAL ``bir_exec_step ^minimal_prog ^empty_state``;

(* If the values equal, so do their types: NOT correct *)
val bir_value_type_equal_THM = store_thm ("bir_value_types_equal_THM",
``!v. ~(?v'. ((BVal_Imm (Imm64 v) = v' ) /\ (~(   SOME (BType_Imm Bit64) = type_of_bir_val v'   ))))``, 
cheat);


val a = REWRITE_RULE [bir_value_type_equal_THM] e;



(* Introduce symbolic variable if var not in environment *)
val bir_check_symbol_def = Define `
    (bir_check_symbol v (BEnv env) =
      case bir_env_lookup (bir_var_name v) (BEnv env) of
      | SOME _ => (BEnv env)
      | NONE   => (BEnv (env |+ ((bir_var_name v), (bir_var_type v), NONE))))`;


(* Introduce fresh symbol when trying to use non-available variable *)
val symb_check_symbol_def = Define `
    symb_check_symbol st v =
        case bir_env_lookup (bir_var_name v) state.bst_environ of
        | SOME _ => st
        | NONE   => st with bst_environ := (BEnv (st.bst_environ |+ ( bir_var_name v, (bir_var_type 

val exec_first_statement_def = Define `
    exec_first_statement prog =
    let state = bir_state_init prog in
    bir_exec_step prog state`;


val e = EVAL ``exec_first_statement ^minimal_prog``;


val st = EVAL ``bir_state_init ^minimal_prog``;
val e = EVAL ``bir_init_state ^minimal_prog``;


val empty_state = ``<|
    bst_pc      := <| bpc_label:= BL_Address (Imm64 0x400570w); bpc_index:= 0 |>;
    bst_environ := BEnv FEMPTY;
    bst_status  := BST_Running |>``;


val e = EVAL ``init_state ^minimal_prog ^empty_state.bst_environ``;
