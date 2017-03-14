(* optimize.ml --- A dummy optimizer  *)

module EL = Elexp
module EN = Env
module M = Myers

let rec constant_folding (e : EL.elexp) = match e with
    | EL.Call (f, args) -> (match f,args with

        (* fold e + 0 -> e *)
        | (EL.Var ((_, "_+_"), _),
            [expr; EL.Imm(Sexp.Integer(_,0))]) ->
                constant_folding expr

        (* fold 0 + e -> e *)
        | (EL.Var ((_, "_+_"), _), 
            [ EL.Imm(Sexp.Integer(_,0)); expr]) ->
                constant_folding expr
  
        (* fold e - 0 -> e *)
        | (EL.Var ((_, "_-_"), _),
            [expr; EL.Imm(Sexp.Integer(_,0))]) ->
                constant_folding expr

        (* fold 1*e -> e *)
        | (EL.Var ((_, "_*_"), _), 
            [ EL.Imm(Sexp.Integer(_,1)); expr]) ->
                constant_folding expr

        (* fold e*1 -> e *)
        | (EL.Var ((_, "_*_"), _), 
            [ expr; EL.Imm(Sexp.Integer(_,1)) ]) ->
                constant_folding expr

        (* fold e/1 -> e *)
        | (EL.Var ((_, "_/_"), _), 
            [ expr; EL.Imm(Sexp.Integer(_,1)) ]) ->
                constant_folding expr
                
        (* fold a + b -> (a + b)  *)
        | EL.Var ((_, "_+_"), _),
            [EL.Imm(Sexp.Integer(_, num1));
             EL.Imm(Sexp.Integer(_, num2))] ->
                 EL.Imm(Sexp.Integer(Util.dummy_location, num1 + num2))
        | (_, _) -> e)

    | EL.Lambda (vname, expr) -> 
            EL.Lambda (vname, constant_folding expr)

    | EL.Let (loc, name_exp_list, body) ->
        EL.Let (loc, 
            List.map (fun (n, e) -> (n, constant_folding e)) name_exp_list,
            constant_folding body)

    | EL.Case (l, e, branches, default) ->
            EL.Case(l, constant_folding e,
            Util.SMap.map 
                (fun (loc, li, e) -> (loc, li, constant_folding e)) branches,
            (match default with
                | None -> None
                | Some (n, e) -> Some (n, constant_folding e)))

    | _ -> e



let rec constant_propagation 
    (ctx : (string option * (EN.value_type ref)) M.myers)
    (e : EL.elexp) 
        : EL.elexp
    = match e with
        | EL.Var ((loc, varname), dbi) -> 
                (match M.find (fun (s, _) -> s = Some varname) ctx with
                    | None            -> e
                    | Some (_, value) -> (match !value with
                        | EN.Vint i    -> EL.Imm
                            (Sexp.Integer (Util.dummy_location, i))
                        | EN.Vstring s -> EL.Imm
                            (Sexp.String (Util.dummy_location, s))
                        | EN.Vfloat f  -> EL.Imm
                            (Sexp.Float (Util.dummy_location,f))
                        | _ -> e))
                        

        | EL.Call (f, args) -> EL.Call (constant_propagation ctx f,
                                        List.map (constant_propagation ctx) 
                                            args)

        | EL.Lambda ((_, varname), expr) ->
                (match M.find (fun (s, _) -> s = Some varname) ctx with
                    | None -> 
                            EL.Lambda ((Util.dummy_location, varname), 
                                constant_propagation ctx expr)
                    | Some (s, _) ->
                            EL.Lambda ((Util.dummy_location, varname), 
                                constant_propagation
                                (M.map (fun (name, value) -> 
                                        if name = s then
                                            (None, value)
                                        else
                                            (name, value)) 
                                ctx) expr ))


        | EL.Let (loc, name_exp_list, body) ->
                e (*TODO*)

        | EL.Case (l, e, branches, default) ->
            EL.Case(l, constant_propagation ctx e,
            Util.SMap.map 
                (fun (loc, li, e) -> (loc, li, constant_propagation ctx e)) 
                    branches,
            (match default with
                | None -> None
                | Some (n, e) -> Some (n, constant_propagation ctx e)))
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

                
(* partie du inlining incomplete

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
