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

(* Dictionnaire contenant les couples (nom de label, chaîne de caractères) des labels de .data contenant les chaînes de caractères *)

let adresses = Hashtbl.create 2

(* Dictionnaire contenant les couples (v_id, adresse) des variables *)

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

(* Je n'ai pas compris à quoi ça sert *)

let empty_env =
  { exit_label = ""; ofs_this = -1; nb_locals = ref 0; next_local = 0 }

let mk_bool d = { expr_desc = d; expr_typ = Tbool }

(* f reçoit le label correspondant à ``renvoyer vrai'' *)
let compile_bool f =
  let l_true = new_label () and l_end = new_label () in
  f l_true ++
  movq (imm 0) (reg rdi) ++ jmp l_end ++
  label l_true ++ movq (imm 1) (reg rdi) ++ label l_end

(* Cela non plus *)

let nombre_vars = ref 0;;

(* Compte le nombre de variables empilées sur la pile pour l'appel de fonction courant afin de pouvoir toutes les dépiler avant le ret sans quoi on obtient des erreurs "segmentation fault *)

let addr = ref (-8);;

(* Contient l'adresse par rapport à %rbp à laquelle va être empilée la prochaine variable *)

let rec expr env e = match e.expr_desc with
(* Génère le code associé à l'expression e *)
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
(* Pour les deux opérations du dessus j'ai adapté le code de if. Les labels du milieu correspondent à un code qui stocke vrai/faux dans %rdi. On teste si la première expression permet de connaître la valeur de l'opération et le cas échéant on fait directement un saut aux labels qui mettent vrai/faux dans %rdi sans tester la deuxième expression. *)
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
(* Ces comparaisons peuvent toutes se déterminer en observant le(s) signe(s) de la différence. On peut donc réutiliser le schéma du cas précédent avec les sauts conditionnels adéquats. *)
                            | TEbinop (Badd | Bsub | Bmul | Bdiv | Bmod as op, e1, e2) -> let opq = fun x y -> begin match op with
                                                                                     | Badd -> addq x y
                                                                                     | Bsub -> subq x y
                                                                                     | Bmul -> imulq x y
                                                                                     | Bdiv -> (movq (imm 0) (reg rdx)) ++ (movq (reg rdi) (reg rax)) ++ idivq (reg rsi) ++ (movq (reg rax) (reg rdi))
                                                                                     | Bmod -> (movq (imm 0) (reg rdx)) ++ (movq (reg rdi) (reg rax)) ++ idivq (reg rsi) ++ (movq (reg rdx) (reg rdi))
                                                                                     | _ -> nop
                                                                                     end in
                                                                (expr env e1) ++ (pushq (reg rdi)) ++ (expr env e2) ++ (pushq (reg rdi)) ++ (popq rsi) ++ (popq rdi) ++ (opq (reg rsi) (reg rdi))
(* Il s'agit essentiellement de réutiliser les fonctions assembleurs déjà existantes. On empile les résultats des expressions pour que la valeur de la première ne soit pas modifiée lors du calcul de la seconde. *)
                            | TEbinop (Beq | Bne as op, e1, e2) -> let a, b, c = new_label(), new_label(), new_label() in
                                                                   (expr env e1) ++ (pushq (reg rdi)) ++ (expr env e2) ++ (pushq (reg rdi)) ++ (popq rsi) ++ (popq rdi) ++
                                                                     (cmpq (reg rsi) (reg rdi)) ++ begin
                                                                       if op = Beq then (je a) ++ (jne b)
                                                                       else (jne a) ++ (je b) end ++
                                                                     (label a) ++ (movq (imm 1) (reg rdi)) ++ (jmp c) ++ ret ++
                                                                     (label b) ++ (movq (imm 0) (reg rdi)) ++ (jmp c) ++ ret ++
                                                                     (label c)
(* C'est la même chose que pour les comparaisons mais ça ne fonctionne pas sur les chaînes de caractères. *)
                            | TEunop (Uneg, e1) -> (expr env e1) ++ (negq (reg rdi))
(* C'est la même chose que pour les opérations arithmétiques précédentes. *)
                            | TEunop (Unot, e1) -> (expr env e1) ++ (movq (imm 1) (reg rsi)) ++ (subq (reg rdi) (reg rsi)) ++ (movq (reg rsi) (reg rdi))
(* Ici la fonction correspondante en assembleur ne fonctionnait pas comme je le souhaitait. J'ai donc réécrit un code assembleur qui fait ce que je souhaite. *)
                            | TEunop (Uamp, e1) -> begin match e1 with
                                                   | {expr_desc = TEident x} -> (movq (imm (Hashtbl.find adresses x.v_id)) (reg rdi))
                                                   | _ -> assert false
                                                   end
                            | TEunop (Ustar, e1) -> (expr env e1) ++ (movq (reg rdi) (reg rsi)) ++ (movq (reg rbp) (reg rdi)) ++ (addq (reg rsi) (reg rdi)) ++ (inline "\tmovq (%rdi), %rdi\n")
(* Pour renvoyer l'adresse d'une variable, on utilise simplement celle qui est stockée dans le dictionnaire adresses. Ensuite, on peut déréférencer en déplaçant la valeur stockée à cette adresse dans %rdi. *) *)
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
(* Pour récupérer la valeur d'une variable, on déplace la valeur stockée à l'adresse associée à la variable dans le dictionnaire adresses dans %rdi *)
                            | TEassign ([{expr_desc=TEident x}], [e1]) -> (expr env e1) ++ (inline ("\tmovq %rdi, "^(string_of_int (Hashtbl.find adresses x.v_id))^"(%rbp)\n"))
                            | TEassign (lv, le) -> let rec evalue_valeurs l = match l with
                                                     | [] -> nop
                                                     | e::l -> (expr env e) ++ (pushq (reg rdi)) ++ (evalue_valeurs l)
                                                   in let rec assigne_valeurs l = match l with
                                                        | [] -> nop
                                                        | ({expr_desc=TEident v})::l -> (popq rdi) ++ (inline ("\tmovq %rdi, "^(string_of_int (Hashtbl.find adresses v.v_id))^"(%rbp)\n")) ++ (assigne_valeurs l)
                                                        | _ -> failwith "Tentative d'assigner une expression à une expression qui n'est pas une variable!"
                                                      in (evalue_valeurs le) ++ (assigne_valeurs (List.rev lv))
(* Pour les TEassign, il suffit de modifier la valeur stockée à l'adresse des variables. Dans le cas des affectations en parallèle, il faut évaluer toutes les expressions avant de réaliser les affectations. Pour cela, on les place sur la pile. *) 
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
(* On concatène les codes associés à chaque expression du bloc. Pour les variables, on empile leurs valeurs sur la pile en incrémentant le compteur de variables et en stockant leurs adresses dans le dictionnaire adresses. *)
                            | TEif (e1, e2, e3) -> let a, b, c = new_label(), new_label(), new_label() in
                                                   (expr env e1) ++ (testq (reg rdi) (reg rdi)) ++ (jne a) ++ (je b) ++ (label a) ++ (expr env e2) ++ (jmp c) ++ (label b) ++ (expr env e3) ++ (jmp c) ++ (label c)
                            | TEfor (e1, e2) ->  let a, b, c = new_label(), new_label(), new_label() in
                                                 (jmp a) ++ (label a) ++ (expr env e1) ++ (testq (reg rdi) (reg rdi)) ++ (jne b) ++ (je c) ++ ret ++ (label b) ++ (expr env e2) ++ (jmp a) ++ ret ++ (label c) ++ ret
(* On utilise des sauts conditionnels pour pouvoir sauter les bouts de code qu'on veut éviter dans le cas du if ou pour en répéter une partie dans le cas du while *)
                            | TEnew ty ->
                               (* TODO code pour new S *) assert false
(* Je ne l'ai pas fait. *)
                            | TEcall (f, el) -> let rec aux vl el = match vl, el with
                                                  | [], [] -> nop
                                                  | v::vl, e::el -> nombre_vars := !nombre_vars + 1;
                                                                    let valeur = expr env e in valeur ++
                                                                                                 (try (inline ("\tmovq %rdi, "^(string_of_int (Hashtbl.find adresses v.v_id))^"(%rbp)\n"))
                                                                                                  with Not_found -> (Hashtbl.add adresses v.v_id !addr; addr := !addr - sizeof(v.v_typ); (expr env e) ++ (pushq (reg rdi))))
                                                                                               ++ (aux vl el)
                                                  | _ -> failwith "Le nombe d'arguments n'est pas celui attendu!"
                                                in let decl_vars = aux f.fn_params el in
                                                   decl_vars ++ call ("F_"^f.fn_name) ++ (movq (reg rax) (reg rdi))
(* Le code des fonctions est déjà généré à l'aide des appels à function_ ainsi il suffit d'insérer "call <fonction>" dans le code puis mettre le contenu de %rdi dans %rax. La fonction auxiliaire avait pour but de gérer le cas des fonctions à paramètres en ajoutant des variables supplémentaires pour chaque paramètre mais ça n'a pas fonctionné (cf. rapport). *)
                            | TEdot (e1, {f_ofs=ofs}) ->
                               (* TODO code pour e.f *) assert false
                            | TEvars (lvars, lassigne) -> assert false
                            (* fait dans block *)
                            | TEreturn [] -> nop
                            | TEreturn [e1] -> (expr env e1) ++ (movq (reg rdi) (reg rax))
                            | TEreturn _ ->
                               assert false
                            | TEincdec (e1, op) -> match e1 with
                                                   | {expr_desc = TEident x} ->  begin match op with
                                                                                  | Inc -> (expr env e1) ++ movq (imm 1) (reg rsi) ++ addq (reg rsi) (reg rdi) ++ (inline ("\tmovq %rdi, "^(string_of_int (Hashtbl.find adresses x.v_id))^"(%rbp)\n"))
                                                                                  | Dec -> (expr env e1)++ movq (imm 1) (reg rsi) ++ subq (reg rsi) (reg rdi) ++ (inline ("\tmovq %rdi, "^(string_of_int (Hashtbl.find adresses x.v_id))^"(%rbp)\n"))
                                                                                  end
                                                   | _ -> failwith "impossible d'incrémenter ou décrémenter une expression qui n'est pas une variable"
(* On effectue simplement une addition ou une soustraction par 1 en récupérant la valeur de la variable comme pour TEident puis on modifie la valeur de la variable comme avec TEassign. *)
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
  
 (* On ajoute une fonction en assembleur qui contient le code généré à partir du corps de la fonction. On compte aussi le nombre de variables empilées afin de pouvoir les dépiler et éviter les erreurs "segmentation fault". *)

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
(* Pour print_string, il s'agit d'un simple appel à printf qui affiche la chaîne de caractère stockée dans %rdi. Pour print_bool, on fait un saut à une fonction qui affiche "true" si le booléen contenu dans %rdi est vrai ou à une fonction qui affiche "false" sinon. *)
   (* TODO appel malloc de stdlib *)
    data =
      label "true" ++ string "true\n" ++
      label "false" ++ string "false\n" ++
      label "S_int" ++ string "%ld\n" ++
      (Hashtbl.fold (fun l s d -> label l ++ string s ++ d) strings nop) 
      
(* On ajoute récursivement (label l ++ string s à nop pour (l,s) dans strings *)
    ;
  }
