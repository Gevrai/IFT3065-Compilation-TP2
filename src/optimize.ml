(* optimize.ml --- A dummy optimizer  *)

module EL = Elexp
module EN = Env
module M = Myers

let rec constant_folding (e : EL.elexp) = match e with
    | EL.Call (f, args) -> (match f,args with
        | (EL.Var ((_, "_+_"), _),
            [expr; EL.Imm(Sexp.Integer(_,0))]) ->
                expr
        | (EL.Var ((_, "_+_"), _), 
            [ EL.Imm(Sexp.Integer(_,0)); expr]) ->
                expr
        | EL.Var ((_, "_+_"), _),
            [EL.Imm(Sexp.Integer(_, num1));
             EL.Imm(Sexp.Integer(_, num2))] ->
                 EL.Imm(Sexp.Integer(Util.dummy_location, num1 + num2))
        | (_, _) -> e)
    | EL.Lambda (vname, expr) -> 
            EL.Lambda (vname, constant_folding expr)
    | _ -> e

(* Vous recevez:
 * - une expression `e` de type `elexp` (défini dans elexp.ml)
 * - un contexte `ctx` qui donne la valeur associée à chaque variable
 *   du contexte.  Le contexte est représenté par une sorte de liste
 *   à accès O(log N) implémentée dans le fichier myers.ml.
 *   Chaque élément de la liste est une paire qui contient le nom
 *   (si la variable a un nom), et la valeur de la variable.
 * Malgré que les variables soient immuables, la valeur d'une variable est
 * stockée dans une "ref cell" parce que c'est la façon la plus simple
 * de gérer les définitions récursives.
 *
 * Vous devez renvoyer une nouvelle expression de type `elexp` équivalente à
 * `e` et idéalement plus simple/efficace.  *)

let optimize (ctx : (string option * (EN.value_type ref)) M.myers)
             (e : EL.elexp)
    : EL.elexp
  = constant_folding e

                
(*
let rec constant_folding (e : EL.elexp) = match e with
    | EL.Call (EL.Var ((_, "_+_"), _),
            [expr; EL.Imm(Sexp.Integer(_,0))]) 
        -> expr
    | EL.Lambda (vname, expr) -> 
            EL.Lambda (vname, constant_folding expr)
    | _ -> e
*)

(* partie du inlining incomplete
(* return value of an element in the context by its name *)
let getListElement ctx name =
    let len = M.length ctx in
        match

let isElement ctx name n = match nth n ctx with
    | (Some name, _) -> true
    | _ -> false
    

(* substitute all occurence of arg by narg in expression e *)
let substitute_arg e arg narg =

(* substitute all occurence of arg by narg in expression e *)
let substitute_args e args nargs =

(* substitute all occurence of arg by narg in expression e *)
let substitute_closure closure nargs =

let map2 f list = match (f, list) with
    | (f, (name, exp)::tl) -> (name, f exp) :: map2 tl

(* inline expansion *)
let inlining_elexp e ctx = match e with
    | Call (f, args) -> match (f, args) with
        | (((_, function_name), index), hd::tl) ->
            let closure = getListElement ctx function_name in 
                substitute_closure closure args;; 
    | Let (l, (vname, exp) :: tl, body ->
            Let (l, map2 inlining_elexp (vname, exp)::tl ctx, 
                inlining_elexp body ctx)
    | Lambda (param, body) -> Lambda (param, inlining_elexp body ctx)

    (* TODO *)
    (*| Case (l, e, branches, default *)
    | _ -> e
*)
