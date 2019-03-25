(*
load "ldrstrBinaryTheory";
*)

open HolKernel;
open ldrstrBinaryTheory;

val ldrstr_prog = ((snd o dest_comb o concl) ldrstr_arm8_THM);
val blocks = (fst o dest_list o dest_BirProgram) ldrstr_prog;

val foo = dest_comb ldrstr_prog;
