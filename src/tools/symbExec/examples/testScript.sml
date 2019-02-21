open HolKernel;
(*
load "bir_expTheory";
load "minimalBinaryTheory";
load "bir_symb_envTheory";
load "bir_symb_execTheory";
 *)
open bir_expTheory;
open minimalBinaryTheory;
open bir_symb_execTheory 
open bir_symb_envTheory;
open bir_valuesTheory;
open bir_immTheory;
open bir_mem_expTheory;
open finite_mapTheory;
open bitstringTheory;
open stringLib;

val _ = new_theory "test";



(*  mem = [mem with R0 = R1 + 20w] *)         
val assign_store_exp = 
 ``BStmt_Assign (BVar "R0" (BType_Imm Bit64))
    (BExp_Store 
        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
        (BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "R0" (BType_Imm Bit64)))
            (BExp_Const (Imm64 20w))) BEnd_LittleEndian
        (BExp_Cast BIExp_LowCast
            (BExp_Den (BVar "R1" (BType_Imm Bit64)))
            Bit32))``;

val assert_exp = 
  ``[BStmt_Assert
        (BExp_Aligned Bit64 2
            (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
             
     BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
       (BExp_Store
        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
        (BExp_BinExp BIExp_Plus
           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
           (BExp_Const (Imm64 8w))) BEnd_LittleEndian
        (BExp_Cast BIExp_LowCast
           (BExp_Den (BVar "R0" (BType_Imm Bit64)))
           Bit32))]``;


val minimal_prog = ((snd o dest_comb o concl) minimal_arm8_THM);
val env = init_env();
val state = (rhs o concl o EVAL) ``bir_symb_state_init ^minimal_prog ^env``;

EVAL ``bir_symb_exec_first_blk ^minimal_prog ^state``;

val _ = export_theory(;
