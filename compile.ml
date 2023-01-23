(* étiquettes
     F_function      entrée fonction
     E_function      sortie fonction
     L_xxx           sauts
     S_xxx           chaîne
   expression calculée avec la pile si besoin, résultat final dans %rdi
   fonction : arguments sur la pile, résultat dans %rax ou sur la pile
            res k
            ...
            res 1
            arg n
            ...
            arg 1
            adr. retour
   rbp ---> ancien rbp
            ...
            var locales
            ...
            calculs
   rsp ---> ...
*)

open Format
open Ast
open Tast
open X86_64

exception Anomaly of string

let debug = ref false

let strings = Hashtbl.create 32
let adresses = Hashtbl.create 2
let alloc_string =
  let r = ref 0 in
  fun s ->
    incr r;
    let l = "S_" ^ string_of_int !r in
    Hashtbl.add strings l s;
    l

let malloc n = movq (imm n) (reg rdi) ++ call "malloc"
let allocz n = movq (imm n) (reg rdi) ++ call "allocz"

let sizeof = Typing.sizeof

let new_label =
  let r = ref 0 in fun () -> incr r; "L_" ^ string_of_int !r
(* renvoie "L_i" en incrémentant i pour ne jamais avoir deux fois le même à partir de 0 *)

type env = {
  exit_label: string;
  ofs_this: int;
  nb_locals: int ref; (* maximum *)
  next_local: int; (* 0, 1, ... *)
}

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0 }

let mk_bool d = { expr_desc = d; expr_typ = Tbool }

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true ++
  movq (imm 0) (reg rdi) ++ jmp l_end ++
  label l_true ++ movq (imm 1) (reg rdi) ++ label l_end

let nombre_vars = ref 0;;
let addr = ref (-8);;

let rec expr env e = match e.expr_desc with
                            | TEskip ->
                               nop
                            | TEconstant (Cbool true) ->
                               movq (imm 1) (reg rdi)
                            | TEconstant (Cbool false) ->
                               movq (imm 0) (reg rdi)
                            | TEconstant (Cint x) ->
                               movq (imm64 x) (reg rdi) ++ (comment "")
                            | TEnil ->
                               xorq (reg rdi) (reg rdi)
                            | TEconstant (Cstring s) ->
                               let l = (alloc_string s) in
                               movq (ilab l) (reg rdi)
                            | TEbinop (Band, e1, e2) -> let a, b, c, d = new_label(), new_label(), new_label(), new_label() in
                                                        (expr env e1) ++ (testq (reg rdi) (reg rdi)) ++ (jne a) ++ (je c) ++ ret ++
                                                          (label a) ++ (expr env e2) ++ (testq (reg rdi) (reg rdi)) ++ (jne b) ++ (je c) ++ ret ++
                                                          (label b) ++ (movq (imm 1) (reg rdi)) ++ (jmp d) ++ ret ++
                                                          (label c) ++ (movq (imm 0) (reg rdi)) ++ (jmp d) ++ ret ++
                                                          (label d)
                            | TEbinop (Bor, e1, e2) -> let a, b, c, d = new_label(), new_label(), new_label(), new_label() in
                                                       (expr env e1) ++ (testq (reg rdi) (reg rdi)) ++ (jne b) ++ (je a) ++ ret ++
                                                         (label a) ++ (expr env e2) ++ (testq (reg rdi) (reg rdi)) ++ (jne b) ++ (je c) ++ ret ++
                                                         (label b) ++ (movq (imm 1) (reg rdi)) ++ (jmp d) ++ ret ++
                                                         (label c) ++ (movq (imm 0) (reg rdi)) ++ (jmp d) ++ ret ++
                                                         (label d)
  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) -> let a, b, c = new_label(), new_label(), new_label() in
                                                     let jumps_op = begin match op with
                                              