(* -------------------------------------------------------------------------- *)
(* Symbolic Memory:                                                           *)
(* Mapping addresses to (symbolic) Expressions                                *)
(* Do we need a different memory?                                             *)
(* ---------------------------------------------------------------------------*)

(* 
app load ["HolKernel", "Parse", "boolLib", "bossLib"];
app load ["wordsTheory", "bitstringTheory"];
app load ["bir_auxiliaryTheory", "bir_immTheory", "bir_symb_expTheory"];
 *)

open HolKernel Parse boolLib bossLib;
open wordsTheory;
open bir_mem_expTheory;

val _ = new_theory "bir_symb_mem";



(* 
 * split words to bytes:
 * for each byte in r:
 *  currByte = r % 256
 *  r = r / 256
 *)

val bir_symb_split_def = Define`
    (bir_symb_split w (0: num) ls = ls) ∧
    (bir_symb_split w n ls = bir_symb_split (w DIV 256) (n-1) ((w MOD 256) :: ls))`;

val bir_symb_mem_split_def = Define `
    (bir_symb_mem_split (BVal_Imm (Imm8 w)) = [w2n w]) ∧
    (bir_symb_mem_split (BVal_Imm (Imm16 w)) = bir_symb_split (w2n w) 2 [] ) /\
    (bir_symb_mem_split (BVal_Imm (Imm64 w)) = bir_symb_split (w2n w) 8 [] )`;
 
(* Problem: 
 * SMT-Solver can only do arithmetic on reals and ints 
 *)



(* This is the function we need to implement *)
(* 
val bir_symb_store_in_mem_def = Define `bir_symb_store_in_mem 
    (value_ty: bir_immtype_t) (a_ty: bir_immtype_t) (result: bir_imm_t)
    (mmap: num -> num) (en: bir_endian_t) (a: num) = 


val bir_symb_load_from_mem_def = Define `bir_symb_load_from_mem 
    (value_ty : bir_immtype_t) (result_ty: bir_immtype_t) 
    (a_ty: bir_immtype_t) (mmap: num -> num)
    (en: bir_endian_t) (a:num) = 
    SOME (mmap a)`;


val bir_symb_eval_load_def = Define `
   (bir_symb_eval_load (BVal_Mem ta tv mmap) (BVal_Imm a) (en: bir_endian_t) t =
   if type_of_bir_imm a = ta then 
     case bir_symb_load_from_mem tv t a mmap en (b2n a) of 
    | NONE   => BVal_Unknown
    | SOME i => Bval_Imm (n2bs i Bit8)
   else BVal_Unknown) ∧
   (bir_symb_eval_load _ _ _ _  = BVal_Unknown)`;
 *)

val _ = export_theory();

