(* -------------------------------------------------------------------------- *)
(* Symbolic Expressions:                                                      *)
(* Either Expressions, containg at least one fresh variable,                  *)
(* Or Immediates                                                              *)
(* Not sure, if we need to distinguish at all                                 *)
(* ---------------------------------------------------------------------------*)

(* 
app load ["HolKernel", "Parse", "boolLib", "bossLib"];
app load ["wordsTheory", "bitstringTheory"];
app load ["bir_auxiliaryTheory", "bir_immTheory", "bir_expTheory", 
          "bir_symb_envTheory"];
*)

open HolKernel Parse boolLib bossLib;
open wordsTheory bitstringTheory;
open bir_auxiliaryTheory bir_immTheory bir_expTheory;


val _ = new_theory "bir_symb_exp";

val _ = Datatype `bir_symb_exp_t = 
   | Symbolic bir_exp_t
   | Concrete bir_imm_t`;


(* ------------------------------------------------------------------------- *)
(* Evaluate  Expressions                                            *)
(* --------------------------------------------------------------------------*)


val _ = export_theory();
