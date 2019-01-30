(* -------------------------------------------------------------------------- *)
(* Symbolic Memory:                                                           *)
(* Memory now Bit64 -> Bit8 fixed, instead of num -> num                      *)
(* This way, we avoid conversion from words to numbers,                       *)
(* which was not possible with symbolic words! )                              *)
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


(* ----------------------------------------------- *)
(* Memory Store                                    *)
(* ----------------------------------------------- *)

(* Split arbtrary size words to list containing its bytes *)
(* Imm1 still missing, but who uses it anyway?! *)
val word_split_to_bytes_def = Define `
    (word_split_to_bytes  (Imm8 w) = [w]) ∧
    (word_split_to_bytes (Imm16 w) = 
        [word_extract 15 8 w; word_extract 7 0 w]) /\
    (word_split_to_bytes (Imm32 w) = 
        [word_extract 31 24 w; word_extract 23 16 w; 
         word_extract 15 8 w; word_extract 7 0 w ]) ∧
    (word_split_to_bytes (Imm64 w) = 
        [word_extract 63 48 w; word_extract 48 32 w; 
         word_extract 31 24 w; word_extract 23 16 w;
         word_extract 15 8 w; word_extract 7 0 w]) ∧
    (word_split_to_bytes (_) = [])`;

(* Update the memory function byte-wise *)
val bir_symb_update_mmap_def = Define `
    (bir_symb_update_mmap (a_ty: bir_immtype_t)  mmap (a: word64) [] = (mmap: word64 -> word8)) ∧
    (bir_symb_update_mmap a_ty mmap a (v::vs) = 
        bir_symb_update_mmap a_ty ((a =+ v) mmap) (a + 1w) vs)`;

(* Store a value in the memory *)
val bir_symb_store_in_mem_def = Define ` 
    bir_symb_store_in_mem value_ty a_ty result mmap en a = 
    case a of 
       | ((Imm64 a') =>
            let vs = word_split_to_bytes result in
            let vs' = 
                (* It's probably the wrong way round. its always the wrong way
                 * round *)
                (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                    | BEnd_BigEndian => SOME vs
                    | BEnd_NoEndian => NONE) in (* TODO No Endian! *)
                case  vs' of
                     NONE => NONE 
                   | SOME vs'' => SOME (bir_symb_update_mmap a_ty mmap a' vs''))
       | _ => NONE`;




(* --------------------------------------------- *)
(* Memory Read                                   *)
(* --------------------------------------------- *)  

(* Again, no one ever uses Bit1! *)
val bir_symb_load_bytes_from_mem_def = Define `
    bir_symb_load_bytes_from_mem 
        (mmap: word64 -> word8) (a: word64)  (result_ty: bir_immtype_t) = case (result_ty) of 
    | Bit8 => [mmap a]
    | Bit16 => [mmap a; mmap (a+1w)]
    | Bit32 => [mmap a; mmap (a+1w); mmap (a+2w); mmap (a+3w)]
    | Bit64 => [mmap a; mmap (a+1w); mmap (a+2w); mmap (a+3w); mmap (a+4w); 
                mmap (a+5w); mmap (a+6w); mmap (a+7w)]
    | _ => []`;

(* Concatenate byte to 'a words *)
val bir_symb_compute_word_from_bytes_def = Define `
    bir_symb_compute_word_from_bytes (vs: word8 list) (result_ty: bir_immtype_t) = 
    case (result_ty) of 
    | Bit8  => SOME (Imm8  ((concat_word_list vs):word8))
    | Bit16 => SOME (Imm16 ((concat_word_list vs):word16))
    | Bit32 => SOME (Imm32 ((concat_word_list vs):word32))
    | Bit64 => SOME (Imm64 ((concat_word_list vs):word64))
    | _ => NONE`;


(* read words from memory *)
val bir_symb_load_from_mem_def = Define `
    bir_symb_load_from_mem (value_ty: bir_immtype_t) (result_ty: bir_immtype_t)
    (a_ty: bir_immtype_t) (mmap: word64 -> word8) (en: bir_endian_t) a = 
    case a of 
       | (Imm64 a') => 
           let vs = bir_symb_load_bytes_from_mem mmap a' result_ty in 
           let vs' = (case en of BEnd_LittleEndian => SOME (REVERSE vs)
                | BEnd_BigEndian => SOME vs
                | BEnd_NoEndian => NONE) in
            case vs' of NONE => NONE 
            | SOME (vs'') => 
                bir_symb_compute_word_from_bytes vs'' result_ty
       | _ => NONE`;


val _ = export_theory();
