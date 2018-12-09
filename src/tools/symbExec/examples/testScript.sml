open HolKernel;
(*
load "bir_expTheory";
load "minimalBinaryTheory";
load "bir_symb_envTheory";
load "bir_symb_execTheory";
 *)
open bir_expTheory;
open minimalBinaryTheory;
open bir_symb_execTheory bir_symb_envTheory;


val _ = new_theory "test";




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

val ProcState_N = mk_var("ProcState_N", Type `:word1`);
val ProcState_Z = mk_var("ProcState_Z", Type `:word1`);
val ProcState_C = mk_var("ProcState_C", Type `:word1`);
val ProcState_V = mk_var("ProcState_V", Type `:word1`);

val exp0 = ``BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64)) 
                (BExp_BinExp BIExp_Minus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 16w)))``;

val cjmp_exp = 
  ``BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
        (BLE_Label (BL_Address (Imm64 0x400570w)))
        (BLE_Label (BL_Address (Imm64 0x400570w)))``;

(* TEST *)
fun init_env () = 
    (rhs o concl o EVAL) 
    ``bir_symb_init_env 
    (^R0, ^R1, ^R2, ^R3, ^R4, ^R5, ^R6, ^R7, ^R8, ^R9, ^R10, ^R11, ^R12, ^LR,
      ^SP_main, ^SP_process) (^ProcState_N, ^ProcState_Z, ^ProcState_C,
       ^ProcState_V)``;

val minimal_prog = ((snd o dest_comb o concl) minimal_arm8_THM);
val env = init_env();

val state = (rhs o concl o EVAL) ``bir_symb_state_init ^minimal_prog ^env``;

         
val exp = ``(BExp_BinExp BIExp_Plus
    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
    (BExp_Const (Imm64 8w)))``;


EVAL ``bir_symb_exec_stmtE ^minimal_prog  ^cjmp_exp ^state``;

val _ = export_theory();
