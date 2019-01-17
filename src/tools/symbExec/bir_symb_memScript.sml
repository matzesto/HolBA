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

val _ = new_theory "bir_symb_mem";
(*
(* Symbolic Memory maps addresses to Expressions *)
val _ = Datatype `bir_symb_mem_t = 
    SymbMem (bir_exp_t |-> bir_exp_t)`;

val bir_symb_mem_lookup_def = Define `
    bir_symb_mem_lookup (SymbMem mem) ex = FLOOKUP mem ex`;

(* Read Expression ex of Type ty from Memory mem *)
val bir_read_from_mem_def = Define `
    bir_read_from_mem (SymbMem mem) ex  = 
    case bir_symb_mem_lookup mem ex of
      NONE => Symbolic (BExp_Const (Imm64 1w))
    | SOME e => e`;
 *)


(* This is the function we need to implement *)
val bir_symb_load_from_mem_def = Define `bir_symb_load_from_mem 
    (value_ty : bir_immtype_t) (result_ty: bir_immtype_t) (mmap: num -> num)
    (en: bir_endian_t) (a:num) = 
    nnmap a;

    

val bir_symb_eval_load_def = Define `
   (bir_symb_eval_load (BVal_Mem ta tv mmap) (BVal_Imm a) (en: bir_endian_t) t =
   if type_of_bir_imm a = ta then 
     case bir_symb_load_from_mem tv t a mmap en (b2n a) of 
    | NONE   => BVal_Unknown
    | SOME i => Bval_Imm i
   else BVal_Unknown) ∧
   (bir_symb_eval_load _ _ _ _  = BVal_Unknown)`;


val _ = export_theory();

