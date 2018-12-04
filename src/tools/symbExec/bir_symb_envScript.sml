(*
app load ["HolKernel", "Parse", "boolLib", "bossLib", "finite_mapTheory"];
app load ["bir_envTheory", "bir_valuesTheory"];
 *)

open HolKernel Parse boolLib bossLib;
open finite_mapTheory;
open bir_envTheory;
open bir_valuesTheory;
open listTheory;
(*
 * Symbolic Environment:
 * Same as Concrete Environment, with initially all variables mapped to symbols
 *)

val _ = new_theory "bir_symb_env";


(* Initialize all the Registers / Variables we have *)
val R0 = mk_var("R0",   Type `:word64`);
val R1 = mk_var("R1",   Type `:word64`);
val R2 = mk_var("R2",   Type `:word64`);
val R3 = mk_var("R3",   Type `:word64`);
val R4 = mk_var("R4",   Type `:word64`);
val R5 = mk_var("R5",   Type `:word64`);
val R6 = mk_var("R6",   Type `:word64`);
val R7 = mk_var("R7",   Type `:word64`);
val R8 = mk_var("R8",   Type `:word64`);
val R9 = mk_var("R9",   Type `:word64`);
val R10 = mk_var("R10", Type `:word64`);
val R11 = mk_var("R11", Type `:word64`);
val R12 = mk_var("R12", Type `:word64`);
val LR = mk_var("LR",    Type `:word64`);
val SP_main = mk_var("SP_main", Type `:word64`);
val SP_process = mk_var("SP_process", Type `:word64`);



val bir_symb_init_env_def = Define `
    bir_symb_init_env 
        (R0, R1, R2, R3, R4, R5, R6, R7, 
         R8, R9, R10, R11, R12, LR, SP_main, SP_process) = 
    BEnv (
        FEMPTY |+ ("R0", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R0))))
        |+ ("R1", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R1))))
        |+ ("R2", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R2))))
        |+ ("R3", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R3))))
        |+ ("R4", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R4))))
        |+ ("R5", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R5))))
        |+ ("R6", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R6))))
        |+ ("R7", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R7))))
        |+ ("R8", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R8))))
        |+ ("R9", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R9))))
        |+ ("R10", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R10))))
        |+ ("R11", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R11))))
        |+ ("R12", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^R12))))
        |+ ("LR", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^LR))))
        |+ ("SP_main", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^SP_main))))
        |+ ("SP_process", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 ^SP_process))))
        )
    `;




val foo = EVAL  ``bir_symb_init_env
    (^R0, ^R1, ^R2, ^R3, ^R4, ^R5, ^R6, ^R7, ^R8, ^R9, ^R10, ^R11, ^R12, ^LR, ^SP_main,
     ^SP_process)``;

val _ = export_theory ();
