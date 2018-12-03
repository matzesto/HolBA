(*
app load ["HolKernel", "Parse", "boolLib", "bossLib", "finite_mapTheory"];
app load ["bir_envTheory", "bir_symb_expTheory", "bir_valuesTheory"];
 *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory;
open bir_envTheory;
open bir_valuesTheory;
(*
 * Symbolic Environment:
 * Same as Concrete Environment, with initially all variables mapped to symbols
 *)

val _ = new_theory "bir_symb_env";


(* Initialize all the Registers / Variables we have *)
val r0 = mk_var("r0",   Type `:word64`);
val r1 = mk_var("r1",   Type `:word64`);
val r2 = mk_var("r2",   Type `:word64`);
val r3 = mk_var("r3",   Type `:word64`);
val r4 = mk_var("r4",   Type `:word64`);
val r5 = mk_var("r5",   Type `:word64`);
val r6 = mk_var("r6",   Type `:word64`);
val r7 = mk_var("r7",   Type `:word64`);
val r8 = mk_var("r8",   Type `:word64`);
val r9 = mk_var("r9",   Type `:word64`);
val r10 = mk_var("r10", Type `:word64`);
val r11 = mk_var("r11", Type `:word64`);
val r12 = mk_var("r12", Type `:word64`);
val lr= mk_var("lr",    Type `:word64`);
val sp_main = mk_var("sp_main", Type `:word64`);
val sp_process = mk_var("sp_process", Type `:word64`);

val reg_list = 
  [("R0", r0), ("R1", r1), ("R2", r2), ("R3", r3), ("R4", r4), 
   ("R5", r5), ("R6", r6), ("R7", r7), ("R8", r8), ("R9", r9), 
   ("R10", r10),("R11", r11), ("R12", r12), ("LR", lr), ("SP_main", sp_main), 
   ("SP_process", sp_process)];

(* Just put the symols in the environment *)
val bir_symb_env_init_update_def = Define `
    bir_symb_env_init_update varname vo ty (BEnv env) = 
    (BEnv (env |+ (varname, (ty, vo))))`;

val bir_symb_env_init_def = Define `
    (bir_symb_env_init []  (BEnv env) = (BEnv env)) ∧
    (bir_symb_env_init ((name, var)::regs) (BEnv env) = bir_symb_env_init regs
        (BEnv (env |+ (name, (BType_Imm Bit64, SOME (BVal_Imm(Imm64 var)))))))`;


EVAL ``bir_symb_env_init (^reg_list) (BEnv FEMPTY)``;
        
val env = EVAL ``bir_symb_env_init_update "R0" (SOME (BVal_Imm(Imm64 ^r0))) (BType_Imm Bit64) (BEnv FEMPTY) ``;

val _ = export_theory ();
