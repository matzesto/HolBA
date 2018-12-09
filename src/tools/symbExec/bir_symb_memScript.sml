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
val _ = export_theory();

