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

let rec expr env e = match e.expr_desc with
  | TEskip ->
    nop
  | TEconstant (Cbool true) ->
    movq (imm 1) (reg rdi)
  | TEconstant (Cbool false) ->
    movq (imm 0) (reg rdi)
  | TEconstant (Cint x) ->
    movq (imm64 x) (reg rdi)
  | TEnil ->
    xorq (reg rdi) (reg rdi)
  | TEconstant (Cstring s) ->
     let l = (alloc_string s) in
     movq (ilab l) (reg rdi)
    (* TODO code pour constante string *)
  | TEbinop (Band, e1, e2) ->
    (* TODO code pour ET logique lazy *) assert false
  | TEbinop (Bor, e1, e2) ->
    (* TODO code pour OU logique lazy *) assert false
  | TEbinop (Blt | Ble | Bgt | Bge as op, e1, e2) -> let _ = op in
    (* TODO code pour comparaison ints *) assert false
  | TEbinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1, e2) -> let opq = fun x y -> begin match op with
                                                                            | Badd -> addq x y
                                                                            | Bsub -> subq x y
                                                                            | Bmul -> imulq x y
                                                                            | Bdiv -> (movq (imm 0) (reg rdx)) ++ (movq (reg rsi) (reg rax)) ++ idivq (reg rdi) ++ (movq (reg rdx) (reg rdi))
                                                                            | Bmod -> (movq (imm 0) (reg rdx)) ++ (movq (reg rsi) (reg rax)) ++ idivq (reg rdi) ++ (movq (reg rax) (reg rdi))
                                                                            | _ -> nop
                                                                  end in
                                                                (expr env e1) ++ (pushq (reg rdi)) ++ (expr env e2) ++ (pushq (reg rdi)) ++ (popq rsi) ++ (popq rdi) ++ (opq (reg rsi) (reg rdi))
  | TEbinop (Beq | Bne as op, e1, e2) -> let _ = op in
    (* TODO code pour egalite toute valeur *) assert false
  | TEunop (Uneg, e1) ->
    (* TODO code pour negation ints *) assert false
  | TEunop (Unot, e1) ->
    (* TODO code pour negation bool *) assert false
  | TEunop (Uamp, e1) ->
    (* TODO code pour & *) assert false
  | TEunop (Ustar, e1) ->
    (* TODO code pour * *) assert false
  | TEprint el ->
     let affiche x = match x.expr_typ with
       | Tint -> (expr env x) ++ (call "print_int")
       | Tstring -> (expr env x) ++ (call "print_string")
       | _ -> nop
     in let rec affiche_liste q = match q with
       | [] -> nop
       | x::q -> let cas = affiche_liste q in (affiche  x) ++ cas
     in affiche_liste el
    (* TODO code pour Print assert false *)
  | TEident x ->
    (* TODO code pour x *) assert false
  | TEassign ([{expr_desc=TEident x}], [e1]) ->
    (* TODO code pour x := e *) assert false
  | TEassign ([lv], [e1]) ->
    (* TODO code pour x1,... := e1,... *) assert false
  | TEassign (_, _) ->
     assert false
  | TEblock el -> let rec seq el = match el with
                  | [] -> nop
                  | x::el -> (expr env x) ++ (seq el)
                  in seq el
     (* TODO code pour block assert false *)
  | TEif (e1, e2, e3) ->
     (* TODO code pour if *) assert false
  | TEfor (e1, e2) ->
     (* TODO code pour for *) assert false
  | TEnew ty ->
     (* TODO code pour new S *) assert false
  | TEcall (f, el) -> call ("F_"^f.fn_name)
     (* TODO code pour appel fonction *)
  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false
  | TEvars _ ->
     assert false (* fait dans block *)
  | TEreturn [] ->
    (* TODO code pour return e *) assert false
  | TEreturn [e1] ->
    (* TODO code pour return e1,... *) assert false
  | TEreturn _ ->
     assert false
  | TEincdec (e1, op) -> match op with
                         | Inc -> movq (imm 1) (reg rsi) ++ addq (reg rsi) (reg rdi)
                         | Dec -> movq (imm 1) (reg rsi) ++ subq (reg rsi) (reg rdi)
(* TODO code pour return e++, e-- *)
let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  (* TODO code pour fonction *) let s = f.fn_name in
  label ("F_" ^ s) ++ (expr strings e) ++ ret

let decl code = function
  | TDfunction (f, e) -> code ++ function_ f e
  | TDstruct _ -> code

let file ?debug:(b=false) dl =
  debug := b;
  (* TODO calcul offset champs *)
  (* TODO code fonctions *) let funs = List.fold_left decl nop dl in
  { text =
      globl "main" ++ label "main" ++
      call "F_main" ++
      xorq (reg rax) (reg rax) ++
      ret ++
      funs ++
      inline "
print_int:
        movq    %rdi, %rsi
        movq    $S_int, %rdi
        xorq    %rax, %rax
        call    printf
        ret

print_string:
        movq $0, %rax
        call printf
        ret

"; (* TODO print pour d'autres valeurs *)
   (* TODO appel malloc de stdlib *)
    data =
      label "S_int" ++ string "%ld\n" ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop) (* On ajoute récursivement (label l ++ string s à nop pour (l,s) dans strings *)
    ;
  }
