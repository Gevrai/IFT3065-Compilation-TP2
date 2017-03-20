(* optimize.ml --- A dummy optimizer  *)

module EL = Elexp
module EN = Env
module M = Myers




(* Constant folding optimization, folding everything it can in one pass.
   - TODO shallowChange : if the children of optimized elexp have already been checked,
       only do a shallow optimization pass when there is a modification
   - Returns tuple (optimizedElexp : Elexp.elexp, isModified : bool)
*)
let constant_folding (e : EL.elexp) =
  (* If at any time in the optimization pass we modify something, this is 'true' *)
  let globalModified = ref false in
  let globalModification () = globalModified := true; () in

  (* Creates integer/float/boolean *)
  let makeInt loc num =
    globalModification ();
    EL.Imm(Sexp.Integer(loc, num)) in
  let makeFloat loc num =
    globalModification ();
    EL.Imm(Sexp.Float(loc, num)) in
  let makeBool loc cond =
    let s = if cond then "true" else "false" in
    globalModification ();
    EL.Imm(Sexp.Symbol(loc, s)) in

  (* From (elexp, hasChanged) tuple, only optimize the immediate children since there can only
  be new opportunities there, not deeper *)
  let rec shallowOptimizeIfNeeded (e, hC) =
    if hC
    then cstfld e false
    else (e, hC)
  (* Main constant folding recursive function *)
  and cstfld e deepOpt = match e with
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
          -> globalModification ();
          if deepOpt
          then
            let (e,hC) = shallowOptimizeIfNeeded (cstfld expr deepOpt) in
            (e, true)
          else (expr, true)
    (* If we know the values of both side of the operation we precompute them *)
        (* Int 'op' Int -> Int  *)
        | EL.Var ((loc, op_str), _ ), [EL.Imm(Sexp.Integer(_, num1));
                                       EL.Imm(Sexp.Integer(_, num2))]
          -> (match op_str with
              | "_+_"    -> (makeInt loc (num1 + num2), true)
              | "_-_"    -> (makeInt loc (num1 - num2), true)
              | "_*_"    -> (makeInt loc (num1 * num2), true)
              | "_/_"    -> (makeInt loc (num1 / num2), true)
              | "Int_<"  -> (makeBool loc (num1 < num2), true)
              | "Int_>"  -> (makeBool loc (num1 > num2), true)
              | "Int_eq" -> (makeBool loc (num1 = num2), true)
              | "Int_<=" -> (makeBool loc (num1 <= num2), true)
              | "Int_>=" -> (makeBool loc (num1 >= num2), true)
              | _ -> (e, false)
            )
        (* Float 'op' Float -> Float *)
        | EL.Var ((loc, op_str), _), [EL.Imm(Sexp.Float(_, num1)); 
                                      EL.Imm(Sexp.Float(_, num2))]
          -> (match op_str with
              | "Float_+" -> (makeFloat loc (num1 +. num2), true)
              | "Float_-" -> (makeFloat loc (num1 -. num2), true)
              | "Float_*" -> (makeFloat loc (num1 *. num2), true)
              | "Float_/" -> (makeFloat loc (num1 /. num2), true)
              | _ -> (e, false)
            )
        (* String functions *)
        | EL.Var ((loc, "Float_to_string"), _), [EL.Imm(Sexp.Float(_, num1))]
          -> (EL.Imm(Sexp.String(loc, string_of_float num1)), true)
        | EL.Var ((loc, "String_eq"), _), [EL.Imm(Sexp.String(_, str1)); 
                                           EL.Imm(Sexp.String(_, str2))]
          -> (makeBool loc (str1 = str2), true)
        (* We didn't find anything, look inside for opportunities if we are in a deep pass *)
        | (_,_) ->
          if deepOpt then
            let (f_e, f_hC) = shallowOptimizeIfNeeded(cstfld f deepOpt) in
            let (args_e, args_hC) = cstFoldElexps args deepOpt in
            (EL.Call(f_e, args_e), f_hC || args_hC)
          else
            (e, false)
    )

    (* Nothing to do really aside from propagating the optimization, the hard
        part here is to not mess the hasChanged boolean value
       There are three helper function to do this right after *)
    | EL.Lambda (vname, expr) ->
        if deepOpt then
          let (ret,hC) = shallowOptimizeIfNeeded(cstfld expr deepOpt) in
          (EL.Lambda (vname, ret), hC)
        else
          (e, false)

    | EL.Let (loc, name_exprs, body) ->
      if deepOpt then
        let (body_e, body_hC) = shallowOptimizeIfNeeded(cstfld body deepOpt) in
        let (name_exprs, name_exprs_hC)= cstFoldNameExprs name_exprs deepOpt in
        (EL.Let(loc, name_exprs, body_e), body_hC || name_exprs_hC)
      else
        (e, false)

    | EL.Case (l, e, branches, default) ->
      if deepOpt then
        let (e, ehC) = shallowOptimizeIfNeeded(cstfld e deepOpt) in
        let (b, bhC) = cstFoldBranches branches deepOpt in
        let (d, dhC) = match default with
          | None -> (None, false)
          | Some (n,e)
            -> let (d', dhC') = shallowOptimizeIfNeeded(cstfld e deepOpt) in (Some (n, d'), dhC')
        in
        (EL.Case(l, e, b, d), ehC || bhC || dhC)
      else
        (e, false)
    | _ -> (e, false)

  (* Every three next function takes a list or map as input and propagate
     the cst_fold optimization to every constituants. If ever any of those
     hasChanged (hC), returns true for the next optimization pass *)
  and cstFoldElexps exprs deepOpt = match exprs with
    | [] -> ([], false)
    | e :: es ->
      let (e, hC) = shallowOptimizeIfNeeded(cstfld e deepOpt) in
      let (es, hCs) = cstFoldElexps es deepOpt  in
      (e :: es, hC || hCs)
  and cstFoldNameExprs name_exprs deepOpt = match name_exprs with
    | [] -> ([], false)
    | (n, e) :: es ->
      let (e, hC) = shallowOptimizeIfNeeded(cstfld e deepOpt) in
      let (es, hCs) = cstFoldNameExprs es deepOpt in
      ((n,e) :: es, hC || hCs)
  and cstFoldBranches branches deepOpt =
    let branches_list = Elexp.SMap.bindings branches in
    let rec _cstFoldBranches lst = 
      match lst with
      | [] -> (Elexp.SMap.empty,false)
      | (key, (l,n,e)) :: es ->
        let (e, hC) = shallowOptimizeIfNeeded(cstfld e deepOpt) in
        let (es, hCs) = _cstFoldBranches es in
        (Elexp.SMap.add key (l,n,e) es, hC || hCs)
    in _cstFoldBranches branches_list
  in
  (* Main call! *)
  shallowOptimizeIfNeeded(cstfld e true)

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
