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

val bir_symb_init_env_def = Define`
    bir_symb_init_env
        (* Registers *)
        (R0, R1, R2, R3, R4, R5, R6, R7, 
         R8, R9, R10, R11, R12, LR, SP_main, SP_process)
        (* Flags *)
        (ProcState_N, ProcState_Z, ProcState_C, ProcState_V) = 
    BEnv (FEMPTY 
        |+ ("R0", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R0))))
        |+ ("R1", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R1))))
        |+ ("R2", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R2))))
        |+ ("R3", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R3))))
        |+ ("R4", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R4))))
        |+ ("R5", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R5))))
        |+ ("R6", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R6))))
        |+ ("R7", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R7))))
        |+ ("R8", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R8))))
        |+ ("R9", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R9))))
        |+ ("R10", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R10))))
        |+ ("R11", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R11))))
        |+ ("R12", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 R12))))
        |+ ("LR", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 LR))))
        |+ ("SP_main", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 SP_main))))
        |+ ("SP_process", (BType_Imm Bit64, SOME (BVal_Imm(Imm64 SP_process))))
        |+ ("ProcState_N", (BType_Bool, SOME (BVal_Imm (Imm1 ProcState_N))))
        |+ ("ProcState_Z", (BType_Bool, SOME (BVal_Imm (Imm1 ProcState_Z))))
        |+ ("ProcState_C", (BType_Bool, SOME (BVal_Imm (Imm1 ProcState_C))))
        |+ ("ProcState_V", (BType_Bool, SOME (BVal_Imm (Imm1 ProcState_V))))
        )`;

val _ = export_theory ();
