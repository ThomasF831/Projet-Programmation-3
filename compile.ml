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
                               movq (imm64 x) (reg rdi)
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
                                                                    | Blt -> jl, jge
                                                                    | Ble -> jle, jg
                                                                    | Bgt -> jg, jle
                                                                    | Bge -> jge, jl
                                                                    | _ -> failwith "L'opération binaire n'est pas une comparaison d'entiers"
                                                                    end
                                                     in (expr env e1) ++ (pushq (reg rdi)) ++ (expr env e2) ++ (pushq (reg rdi)) ++ (popq rsi) ++ (popq rdi) ++
                                                          (cmpq (reg rsi) (reg rdi)) ++ ((fst jumps_op) a) ++ ((snd jumps_op) b) ++
                                                          (label a) ++ (movq (imm 1) (reg rdi)) ++ (jmp c) ++ ret ++
                                                          (label b) ++ (movq (imm 0) (reg rdi)) ++ (jmp c) ++ ret ++
                                                          (label c)
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
  | TEunop (Uneg, e1) -> (expr env e1) ++ (negq (reg rdi))
  | TEunop (Unot, e1) -> (expr env e1) ++ (movq (imm 1) (reg rsi)) ++ (subq (reg rdi) (reg rsi)) ++ (movq (reg rsi) (reg rdi))
  | TEunop (Uamp, e1) ->
     (* TODO code pour & *) assert false
  | TEunop (Ustar, e1) ->
    (* TODO code pour * *) assert false
  | TEprint el ->
     let affiche x = match x.expr_typ with
       | Tint -> (expr env x) ++ (call "print_int")
       | Tstring -> (expr env x) ++ (call "print_string")
       | Tbool -> (expr env x) ++ (call "print_bool")
       | _ -> nop
     in let rec affiche_liste q = match q with
       | [] -> nop
       | x::q -> let cas = affiche_liste q in (affiche  x) ++ cas
     in affiche_liste el
  | TEident x -> inline ("\tmovq "^(string_of_int (Hashtbl.find adresses x.v_id)^"(%rbp), %rdi\n"))
    (* TODO code pour x *)
  | TEassign ([{expr_desc=TEident x}], [e1]) ->
    (* TODO code pour x := e *) assert false
  | TEassign ([lv], [e1]) ->
    (* TODO code pour x1,... := e1,... *) assert false
  | TEassign (_, _) ->
     assert false
  | TEblock el -> let rec seq el env = begin match el with
                  | [] -> nop
                  | {expr_desc = TEvars (vl,al); expr_typ = Tmany [] }::el -> let rec aux vl al env =  match vl, al with
                                                                                | [], [] -> nop
                                                                                | v::vl, a::al -> nombre_vars := !nombre_vars + 1; Hashtbl.add adresses v.v_id !addr; addr := !addr - sizeof(v.v_typ); (expr env a) ++ (pushq (reg rdi)) ++ (aux vl al env)
                                                                                | _ -> failwith "La liste des variables et celle des valeurs à assigner n'ont pas la même longueur !"
                                                                              in let code = aux vl al env in
                                                                                 code ++ (seq el env)
                  | x::el -> (expr env x) ++ seq el env
                                       end
                  in seq el env
  | TEif (e1, e2, e3) -> let a, b, c = new_label(), new_label(), new_label() in
      (expr env e1) ++ (testq (reg rdi) (reg rdi)) ++ (jne a) ++ (je b) ++ ret ++ (label a) ++ (expr env e2) ++ (jmp c) ++ ret ++ (label b) ++ (expr env e3) ++ ret ++ (jmp c) ++ (label c) ++ ret
  | TEfor (e1, e2) ->  let a, b, c = new_label(), new_label(), new_label() in
                       (label a) ++ (expr env e1) ++ (testq (reg rdi) (reg rdi)) ++ (jne b) ++ (je c) ++ ret ++ (label b) ++ (expr env e2) ++ (jmp a) ++ ret ++ (label c) ++ ret
     (* TODO code pour for *)
  | TEnew ty ->
     (* TODO code pour new S *) assert false
  | TEcall (f, el) -> call ("F_"^f.fn_name) ++ (movq (reg rax) (reg rdi))
  | TEdot (e1, {f_ofs=ofs}) ->
     (* TODO code pour e.f *) assert false
  | TEvars (lvars, lassigne) -> assert false
                                       (* fait dans block *)
  | TEreturn [] -> nop
  | TEreturn [e1] -> (expr env e1) ++ (movq (reg rdi) (reg rax))
  | TEreturn _ ->
     assert false
  | TEincdec (e1, op) -> match op with
                         | Inc -> movq (imm 1) (reg rsi) ++ addq (reg rsi) (reg rdi)
                         | Dec -> movq (imm 1) (reg rsi) ++ subq (reg rsi) (reg rdi)
;;

let function_ f e =
  if !debug then eprintf "function %s:@." f.fn_name;
  let s = f.fn_name in
  let dep = ref nop in
  let code = expr strings e in
  for i = 0 to  !nombre_vars-1 do
    dep := !dep ++ (popq rdx)
  done;
  nombre_vars := 0;
  label ("F_" ^ s) ++ (pushq (reg rbp)) ++ (movq (reg rsp) (reg rbp)) ++ code ++ (!dep) ++ (popq rbp) ++ ret

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
print_bool:
        testq %rdi, %rdi
        jne print_true
        je print_false
        ret
print_true:
        movq $true, %rdi
        call print_string
        ret
print_false:
        movq $false, %rdi
        call print_string
        ret
";
   (* TODO appel malloc de stdlib *)
    data =
      label "true" ++ string "true\n" ++
      label "false" ++ string "false\n" ++
      label "S_int" ++ string "%ld\n" ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop) (* On ajoute récursivement (label l ++ string s à nop pour (l,s) dans strings *)
    ;
  }
