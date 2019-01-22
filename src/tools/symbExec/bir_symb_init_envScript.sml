(********************************************************)
(* Functions definied within this file are use to       *)
(* initialize the environment / memory                  *)
(* This is mostly SML -- not HOL definitions!           *)
(********************************************************)

(* 
app load ["bir_symb_envTheory", "bir_symb_execTheory"]
*)

open HolKernel;
open bir_expTheory;
open bir_symb_execTheory 
open bir_symb_envTheory;
open bir_valuesTheory;
open bir_immTheory;
open bir_mem_expTheory;
open finite_mapTheory;
open bitstringTheory;
open stringLib;

val _ = new_theory "test";


(* auxiliary operations on finite maps *)
val fmap_update_replace_def = Define `
    fmap_update_replace (map: 'a |-> 'b) (a,  b) = 
    case (FLOOKUP map a) of 
    | NONE  => FUPDATE map (a, b)
    | SOME v => FUPDATE (map \\  a ) (a, b)`;

val bir_symb_env_update_def = Define `
    bir_symb_env_update varname vo ty (BEnv env) = 
    BEnv (fmap_update_replace env (varname, (ty, vo)))`;
 
 
(* Initialize all the Registers / Variables we have *)


(* Functions to generate symolbic registers of _64 _8 and _1 bits *)
fun generate_symbolic_register_64 (name: string) = 
  let 
    val reg_0 = mk_var(name^"_0", Type `:word8`)
    val reg_1 = mk_var(name^"_1", Type `:word8`)
    val reg_2 = mk_var(name^"_2", Type `:word8`)
    val reg_3 = mk_var(name^"_3", Type `:word8`)
    val reg_4 = mk_var(name^"_4", Type `:word8`)
    val reg_5 = mk_var(name^"_5", Type `:word8`)
    val reg_6 = mk_var(name^"_6", Type `:word8`)
    val reg_7 = mk_var(name^"_7", Type `:word8`)
  in 
    (reg_0, reg_1, reg_2, reg_3,
     reg_4, reg_5, reg_6, reg_7)
  end;

fun generate_symbolic_register_1 (name : string) = 
  mk_var(name, Type `:word1`);

fun generate_symbolic_register_8 (name : string) = 
  mk_var(name, Type `:word8`);


(* Add symbolic registers byte-wise in environment *)
fun add_symbolic_register_to_env_64 name env = 
    let 
        val (r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7) =
          generate_symbolic_register_64 name
        val name_hol = fromMLstring name 
    in
        (rhs o concl o EVAL)
    ``
        bir_symb_env_update 
            (^name_hol ++ "_0") (SOME (BVal_Imm (Imm8 ^r_0))) (BType_Imm Bit8) (
        bir_symb_env_update 
            (^name_hol ++ "_1") (SOME (BVal_Imm (Imm8 ^r_1))) (BType_Imm Bit8) (
        bir_symb_env_update 
            (^name_hol ++ "_2") (SOME (BVal_Imm (Imm8 ^r_2))) (BType_Imm Bit8) (
        bir_symb_env_update 
            (^name_hol ++ "_3") (SOME (BVal_Imm (Imm8 ^r_3))) (BType_Imm Bit8) (
        bir_symb_env_update 
            (^name_hol ++ "_4") (SOME (BVal_Imm (Imm8 ^r_4))) (BType_Imm Bit8) (
        bir_symb_env_update 
            (^name_hol ++ "_5") (SOME (BVal_Imm (Imm8 ^r_5))) (BType_Imm Bit8) (
        bir_symb_env_update 
            (^name_hol ++ "_6") (SOME (BVal_Imm (Imm8 ^r_6))) (BType_Imm Bit8) (
        bir_symb_env_update 
            (^name_hol ++ "_7") (SOME (BVal_Imm (Imm8 ^r_7))) (BType_Imm Bit8) 
            ^env )))))))
    ``
  end;

fun add_symbolic_register_to_env_8 name env = 
    let 
      val r = generate_symbolic_register_8 name
      val name_hol = fromMLstring name
    in
      (rhs o concl o EVAL)
    `` bir_symb_env_update 
        ^name_hol (SOME (BVAL_Imm (Imm8 ^r))) (BType_Imm Bit8) ^env
    ``
    end;

fun add_symbolic_register_to_env_1 name env = 
    let 
      val r = generate_symbolic_register_1 name
      val name_hol = fromMLstring name
    in
      (rhs o concl o EVAL)
    ``
      bir_symb_env_update
        ^name_hol (SOME (BVAL_Imm (Imm1 ^r))) (BType_Imm Bit1) ^env
    ``
    end;


fun add_registers_to_env_64 [] env = env
  | add_registers_to_env_64 (reg :: regs) env = 
        add_registers_to_env_64 regs (add_symbolic_register_to_env_64 reg env)

fun add_registers_to_env_8 [] env = env
  | add_registers_to_env_8 (reg :: regs) env = 
        add_registers_to_env_8 regs (add_symbolic_register_to_env_8 reg env)

fun add_registers_to_env_1 [] env = env
  | add_registers_to_env_1 (reg :: regs) env =
        add_registers_to_env_1 regs (add_symbolic_register_to_env_1 reg env)

fun init_env () = 
    let 
      (* 64 Bit Registers *)
      val reg_list_64 = [
        "R0", "R1", "R2", "R3", "R4", 
        "R5", "R6", "R7", "R8", "R9",
        "R10","R11","R12", "SP_EL0",
        "SP_process", "ADDR"]
      (* 1 Byte registers *)
      val reg_list_8 = [ "VAL" ]
      (* 1 Bit flags *)
      val reg_list_1  = [
        "ProcState_N", "ProcState_Z",
        "ProcState_C", "ProcState_V" ]
    in
      let 
        val e = add_registers_to_env_64 reg_list_64 ``BEnv FEMPTY`` 
      in 
        let 
          val ee =  add_registers_to_env_8 reg_list_8 e 
        in 
          add_registers_to_env_1 reg_list_1 ee
        end
      end
    end;

val _ = export_theory();
