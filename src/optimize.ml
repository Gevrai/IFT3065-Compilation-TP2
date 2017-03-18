(* optimize.ml --- A dummy optimizer  *)

module EL = Elexp
module EN = Env
module M = Myers


(* Creates a boolean from condition, heavily dependant on boolean
 * representation in builtin.typer, but it works for our purpose *)
let mkBool cond loc =
  let s = if cond then "true" else "false" in
  EL.Imm(Sexp.Symbol(loc, s))


(* Relatively basic recursive constant folding optimization
   - Returns 'true' as second tuple value if ever any of the elexp inside has
    been altered.
*)
let rec constant_folding (e : EL.elexp) = match e with
  (* Some basic fonctions can be precomputed maybe *)
    | EL.Call (f, args) -> ( match (f,args) with
    (* Trivial folding cases with 1 and 0, for integer and floats *)
        (* e + 0 -> e *)
        | (EL.Var ((_, "_+_"), _), [expr; EL.Imm(Sexp.Integer(_,0))])
        | (EL.Var ((_, "Float_+"), _), [expr; EL.Imm(Sexp.Float(_,0.0))])
        (* 0 + e -> e *)
        | (EL.Var ((_, "_+_"), _), [ EL.Imm(Sexp.Integer(_,0)); expr])
        | (EL.Var ((_, "Float_+"), _), [ EL.Imm(Sexp.Float(_,0.0)); expr])
        (* e - 0 -> e *)
        | (EL.Var ((_, "_-_"), _), [expr; EL.Imm(Sexp.Integer(_,0))])
        | (EL.Var ((_, "Float_-"), _), [expr; EL.Imm(Sexp.Float(_,0.0))])
        (* 1*e -> e *)
        | (EL.Var ((_, "_*_"), _), [ EL.Imm(Sexp.Integer(_,1)); expr])
        | (EL.Var ((_, "Float_*"), _), [ EL.Imm(Sexp.Float(_,1.0)); expr])
        (* e*1 -> e *)
        | (EL.Var ((_, "_*_"), _), [ expr; EL.Imm(Sexp.Integer(_,1)) ])
        | (EL.Var ((_, "Float_*"), _), [ expr; EL.Imm(Sexp.Float(_,1.0)) ])
        (* e/1 -> e *)
        | (EL.Var ((_, "_/_"), _), [ expr; EL.Imm(Sexp.Integer(_,1)) ])
        | (EL.Var ((_, "Float_/"), _), [ expr; EL.Imm(Sexp.Float(_,1.0)) ])
          -> let (ret,hC) = constant_folding expr in (ret, true)

    (* If we know the values of both side of the operation we precompute them *)
        (* Int 'op' Int -> Int  *)
        | EL.Var ((loc, op_str), _ ), [EL.Imm(Sexp.Integer(_, num1));
                                       EL.Imm(Sexp.Integer(_, num2))]
          -> (match op_str with
              | "_+_"    -> (EL.Imm(Sexp.Integer(loc, num1 + num2)), true)
              | "_-_"    -> (EL.Imm(Sexp.Integer(loc, num1 - num2)), true)
              | "_*_"    -> (EL.Imm(Sexp.Integer(loc, num1 * num2)), true)
              | "_/_"    -> (EL.Imm(Sexp.Integer(loc, num1 / num2)), true)
              | "Int_<"  -> (mkBool (num1 < num2) loc, true)
              | "Int_>"  -> (mkBool (num1 > num2) loc, true)
              | "Int_eq" -> (mkBool (num1 = num2) loc, true)
              | "Int_<=" -> (mkBool (num1 <= num2) loc, true)
              | "Int_>=" -> (mkBool (num1 >= num2) loc, true)
              | _ -> (e, false)
            )
        (* Float 'op' Float -> Float *)
        | EL.Var ((loc, op_str), _), [EL.Imm(Sexp.Float(_, num1)); 
                                      EL.Imm(Sexp.Float(_, num2))]
          -> (match op_str with
              | "Float_+" -> (EL.Imm(Sexp.Float(loc, num1 +. num2)), true)
              | "Float_-" -> (EL.Imm(Sexp.Float(loc, num1 -. num2)), true)
              | "Float_*" -> (EL.Imm(Sexp.Float(loc, num1 *. num2)), true)
              | "Float_/" -> (EL.Imm(Sexp.Float(loc, num1 /. num2)), true)
              | _ -> (e, false)
            )
        (* String functions *)
        | EL.Var ((loc, "Float_to_string"), _), [EL.Imm(Sexp.Float(_, num1))]
          -> (EL.Imm(Sexp.String(loc, string_of_float num1)), true)
        | EL.Var ((loc, "String_eq"), _), [EL.Imm(Sexp.String(_, str1)); 
                                           EL.Imm(Sexp.String(_, str2))]
          -> (mkBool (str1 = str2) loc, true)
        (* We didn't find anything, look inside for opportunities *)
        | (_,_) -> let (f_e, f_hC) = constant_folding f in
          let (args_e, args_hC) = constant_folding_elexps args in
          (EL.Call(f_e, args_e), f_hC || args_hC)
    )

    (* Nothing to do really aside from propagating the optimization, the hard
        part here is to not mess the hasChanged boolean value
       There are three helper function to do this right after *)
    | EL.Lambda (vname, expr)
      -> let (ret,hC) = constant_folding expr in
      (EL.Lambda (vname, ret), hC)

    | EL.Let (loc, name_exprs, body)
      -> let (body_e, body_hC) = constant_folding body in
      let (name_exprs, name_exprs_hC)= constant_folding_name_exprs name_exprs in
      (EL.Let(loc, name_exprs, body_e), body_hC || name_exprs_hC)

    | EL.Case (l, e, branches, default)
      -> let (e, ehC) = constant_folding e in
      let (b, bhC) = constant_folding_branches branches in
      let (d, dhC) = match default with
        | None -> (None, false)
        | Some (n,e)
          -> let (d', dhC') = constant_folding e in (Some (n, d'), dhC')
      in
      (EL.Case(l, e, b, d), ehC || bhC || dhC)
    | _ -> (e, false)

(* From a elexp list of a call, scours the building 'elexp' and
 * recursively fold the constants inside, returning true if it happened *)
and constant_folding_elexps exprs = match exprs with
  | [] -> ([], false)
  | e :: es ->
    let (e, hC) = constant_folding e in
    let (es, hCs) = constant_folding_elexps es in
    (e :: es, hC || hCs)

(* From a name_exp list of a let binding, scours the building 'elexp' and
 * recursively fold the constants inside, returning true if hasChanged *)
and constant_folding_name_exprs name_exprs = match name_exprs with
  | [] -> ([], false)
  | (n, e) :: es ->
    let (e, hC) = constant_folding e in
    let (es, hCs) = constant_folding_name_exprs es in
    ((n,e) :: es, hC || hCs)

(* From a branch consisting of a map, returns the optimized elexp map and true
   if there was any changes made to any elexp inside *)
and constant_folding_branches branches =
  let branches_list = Elexp.SMap.bindings branches in
  let rec internal_fold lst = 
    match lst with
    | [] -> (Elexp.SMap.empty,false)
    | (key, (l,n,e)) :: es ->
      let (e, hC) = constant_folding e in
      let (es, hCs) = internal_fold es in
      (Elexp.SMap.add key (l,n,e) es, hC || hCs)
  in internal_fold branches_list

(* lookup for value of a variable in the given context and return that
 * value if it exists *)
let lookup_ctx ctx varname = 
    let rec aux ctx varname ind len =
        if ind = len then
            None
        else
            match M.nth ind ctx with 
                | (None, value_ref) -> aux ctx varname (ind+1) len
                | (Some var, value_ref) 
                    -> if var = varname then
                           Some !value_ref
                       else
                           aux ctx varname (ind+1) len

    in aux ctx varname 0 (M.length ctx)

(* remove from context the elements with name corresponding to the
 * nth element from the name_exp_list
 * helper function for the Let case of constant_propagation *)
let remove_names_in_ctx (name_exp_list : (EL.vname * EL.elexp) list)
        (ctx : (string option * (EN.value_type ref)) M.myers) =
    let rec helper l ctx n len =
        if n = len then ctx else
          match List.nth name_exp_list n with
          | ((_, name), valref)
                -> (match M.find (fun (s, _) -> s = Some name) ctx with
                        | None -> helper l ctx (n+1) len
                        | Some _
                            -> (* eliminate the variable from the context *)
                                        helper l (M.map (fun (varname, value) ->
                                                if varname = Some name then
                                                    (None, value)
                                                else
                                                    (varname, value))
                                        ctx) (n+1) len)
    in helper name_exp_list ctx 0 (List.length name_exp_list)



let rec constant_propagation
    (ctx : (string option * (EN.value_type ref)) M.myers)
    (e : EL.elexp)
        : EL.elexp
    = match e with
        | EL.Var ((loc, varname), dbi)
            -> (match lookup_ctx ctx varname with
                    | None -> e
                    | Some value -> (match value with
                        | EN.Vint i    -> EL.Imm
                            (Sexp.Integer (Util.dummy_location, i))
                        | EN.Vstring s -> EL.Imm
                            (Sexp.String (Util.dummy_location, s))
                        | EN.Vfloat f  -> EL.Imm
                            (Sexp.Float (Util.dummy_location,f))
                        | _ -> e))

        | EL.Call (f, args)
            -> EL.Call (constant_propagation ctx f,
                                        List.map (constant_propagation ctx)
                                            args)

        | EL.Lambda ((_, varname), expr)
            -> (match lookup_ctx ctx varname with
                    | None
                        -> EL.Lambda ((Util.dummy_location, varname),
                                constant_propagation ctx expr)
                    | Some _
                        -> EL.Lambda ((Util.dummy_location, varname),
                                constant_propagation
                                (* eliminate the variable from the
                                 * context *)
                                (M.map (fun (name, value)
                                    -> if name = Some varname then
                                            (None, value)
                                        else
                                            (name, value))
                                ctx) expr ))


        | EL.Let (loc, name_exp_list, body)
            -> EL.Let(loc,
                    List.map (fun (var, expr)
                        -> (var, constant_propagation ctx expr)) name_exp_list,
                    constant_propagation
                        (remove_names_in_ctx name_exp_list ctx) body)

        | EL.Case (l, e, branches, default)
            -> EL.Case(l, constant_propagation ctx e,
            Util.SMap.map
                (fun (loc, li, e) -> (loc, li, constant_propagation ctx e))
                    branches,
            (match default with
                | None -> None
                | Some (n, e) -> Some (n, constant_propagation ctx e)))
        | _ -> e

(* let rec case_reduction *)
(*     (ctx : (string option * (EN.value_type ref)) M.myers) (e : EL.elexp) *)
(*         : EL.elexp = match e with *)
(*   | EL.Case (loc, exp, branches, default) *)
(*     -> match exp with *)
(*       | EL.Cons(loc, cname) -> *)

(*     let goodBranch = *)
(*   | _ -> e *)


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

let rec optimize (ctx : (string option * (EN.value_type ref)) M.myers)
             (e : EL.elexp) : EL.elexp =
  let prop = constant_propagation ctx e in
  let (folded, hasChanged) = constant_folding prop in
  if hasChanged then optimize ctx folded else folded

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
