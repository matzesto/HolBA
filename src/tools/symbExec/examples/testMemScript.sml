load "bir_symb_memTheory";
open bir_symb_memTheory;
open bir_expTheory;
open wordsLib;
open simpLib
open boolSimps;
open boolTheory;


val b = mk_var("b", Type `:word64`)
val c = mk_var("c", Type `:word64`)


(* Store concrete value in concrete address *)
val f = ``
    bir_symb_eval_store 
        (BVal_SymbMem Bit64 Bit8 (K 0w)) (BVal_Imm (Imm64 0x1234w))
        BEnd_LittleEndian (BVal_Imm (Imm64  0x2345w))``;
EVAL f;

(* Store symbolic value at concrete address *)
val a = mk_var("a", Type `:word64`);
val f = ``
    bir_symb_eval_store
        (BVal_SymbMem Bit64 Bit8 (K 0w)) (BVal_Imm (Imm64 0x1234w))
        BEnd_LittleEndian (BVal_Imm (Imm64 ^a))``;
EVAL f;

(* Read symbolic value from concrete address *)
val a = mk_var("a", Type `:word64`);
val f = ``
    let mem = 
     (bir_symb_eval_store
        (BVal_SymbMem Bit64 Bit8 (K 0w)) (BVal_Imm (Imm64 0x1234w))
        BEnd_LittleEndian (BVal_Imm (Imm64 ^a)))
    in 
      (bir_symb_eval_load mem (BVal_Imm (Imm64 0x1234w))
      BEnd_LittleEndian Bit64)``;

EVAL f;

(* Store concrete value to symbolic address, read from /different/ address  *)
val a = mk_var ("a", Type `:word64`);
val f = ``
    let mem = 
    (bir_symb_eval_store
        (BVal_SymbMem Bit64 Bit8 (K 0w)) (BVal_Imm (Imm64 ^a)) 
        BEnd_LittleEndian (BVal_Imm (Imm64 0x1234w)))
    in 
      (bir_symb_eval_load mem (BVal_Imm (Imm64 0x1234w)) BEnd_LittleEndian
      Bit64)``
EVAL f;

