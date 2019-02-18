(*
app load ["HolKernel", "Parse", "boolLib", "bossLib", "finite_mapTheory"];
app load ["bir_envTheory", "bir_valuesTheory"];
 *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory;
open bir_envTheory;
open bir_valuesTheory;
open listTheory;

(* --------------------------------------------------------------------- *)
(* Symbolic Environment:                                                 *)
(* Same as Concrete Environment, with initially all                      *)
(* variables / flags set to symbols                                      *)
(* ----------------------------------------------------------------------*)

val _ = new_theory "bir_symb_env";

val _ = Datatype `bir_symb_var_environment_t = 
  BEnv (string |-> (bir_type_t # (bir_exp_t)))`;
  

(* -----------------------------------------------------*)
(* Symbolic environment maps Vars to expressions        *)
(* ---------------------------------------------------- *)


val fmap_update_replace_def = Define `
    fmap_update_replace (map: 'a |-> 'b) (a,  b) = 
    case (FLOOKUP map a) of 
    | NONE  => FUPDATE map (a, b)
    | SOME v => FUPDATE (map \\  a ) (a, b)`;


val bir_symb_env_read_def  = Define `
    (bir_symb_env_read v (BEnv env) = 
        case (FLOOKUP  env (bir_var_name v)) of 
        | NONE => ARB
        | SOME (ty, e) => e)`;

val bir_symb_env_read_def = Define `
    bir_symb_env_read v (BEnv env) = 

val bir_symb_env_update_def = Define `
    bir_symb_env_update varname vo ty (BEnv env) = 
    BEnv (fmap_update_replace env (varname, (ty, vo)))`;

val bir_symb_env_write_def = Define `
    bir_symb_env_write v va env = 
    if bir_env_check_type v env then 
      SOME (bir_symb_env_update (bir_var_name v) (SOME va) (bir_var_type v) env)
    else NONE`;

val _ = export_theory ();
