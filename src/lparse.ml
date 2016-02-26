(*
 *      Typer Compiler
 *
 * ---------------------------------------------------------------------------
 *
 *      Copyright (C) 2011-2016  Free Software Foundation, Inc.
 *
 *   Author: Pierre Delaunay <pierre.delaunay@hec.ca>
 *   Keywords: languages, lisp, dependent types.
 *
 *   This file is part of Typer.
 *
 *   Typer is free software; you can redistribute it and/or modify it under the
 *   terms of the GNU General Public License as published by the Free Software
 *   Foundation, either version 3 of the License, or (at your option) any
 *   later version.
 *
 *   Typer is distributed in the hope that it will be useful, but WITHOUT ANY
 *   WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 *   FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 *   more details.
 *
 *   You should have received a copy of the GNU General Public License along 
 *   with this program.  If not, see <http://www.gnu.org/licenses/>. 
 *
 * ---------------------------------------------------------------------------
 *  
 *      Description:
 *          parse pexp expression into lexp
 *
 * --------------------------------------------------------------------------- *)

open Util
open Sexp
open Pexp
open Lexp
open Grammar
open Debruijn
open Fmt

(* Shortcut => Create a Var *)
let make_var name index loc = 
    Var(((loc, name), index))
;;

let not_implemented_error () =
    internal_error "not implemented"
;;

let lexp_error = msg_error "LEXP"
let lexp_warning = msg_warning "LEXP"

(* Vdef is exactly similar to Pvar but need to modify our ctx *)
let pvar_to_vdef p =
    p
;;
(*  PEXP is not giving SEXP types this is why types are unknown *)

(*
 *  The main job of lexp (currently) is determine variable name (index)
 *  and to regroup type specification with their variable 
 *)
 
let rec lexp_parse (p: pexp) (ctx: lexp_context): (lexp * lexp_context) =
    (* So I don't have to extract it *)
    let tloc = pexp_location p in
    match p with
        (*  Block/String/Integer/Float *)
        | Pimm value -> Imm(value), ctx
            
        (*  Symbol i.e identifier /!\ A lot of Pvar are not variables /!\ *)
        | Pvar (loc, name) -> 
            let idx = get_var_index name ctx in
            (* This should be an error but we currently accept it for debugging *)
            if idx < 0 then
                lexp_warning tloc ("Variable: '" ^ name ^ "' does not exist");
            (make_var name (idx + 1) loc), ctx; 
        
        (*  Let, Variable declaration + local scope *)
        | Plet(loc, decls, body) ->         (* /!\ HERE *)    
            let decl, nctx = lexp_parse_let decls (add_scope ctx) in
            let bdy, nctx = lexp_parse body nctx in
            (* print_lexp_context nctx; *)
            (*  Send back old context we exit the inner scope *)
            Let(tloc, decl, bdy), ctx
            
        (* ->/=> *)
        | Parrow (kind, Some var, tp, loc, expr) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let ltyp, ctx = lexp_parse tp ctx in
            let lxp, ctx = lexp_parse expr ctx in
            Arrow(kind, Some nvar, ltyp, tloc, lxp), ctx
            
        | Parrow (kind, None, tp, loc, expr) ->
            let ltyp, ctx = lexp_parse tp ctx in
            let lxp, ctx = lexp_parse expr ctx in
            Arrow(kind, None, ltyp, tloc, lxp), ctx
            
        (*  *)
        | Plambda (kind, var, Some ptype, body) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let ltyp, ctx = lexp_parse ptype ctx in
            let lbody, ctx = lexp_parse body ctx in
            Lambda(kind, nvar, ltyp, lbody), ctx
            
        | Plambda (kind, var, None, body) ->
            let nvar = pvar_to_vdef var in  (* /!\ HERE *)
            let lbody, ctx = lexp_parse body ctx in
            Lambda(kind, nvar, UnknownType(tloc), lbody), ctx (* /!\ Missing Type *)
            
        (* Function Call *)
        | Pcall (fname, args) ->
            let fname, ctx = lexp_parse fname ctx in
            Call(fname, (Aexplicit, UnknownType(tloc))::[]), ctx
            
        | _ 
            -> UnknownType(tloc), ctx

and lexp_parse_let decls ctx =

    (*  Merge Type info and declaration together  since we don't know where the
        type info will be a map is used to merge together declaration *)
    let rec loop (decls: (pvar * pexp * bool) list) merged: 
                                    (vdef * pexp option * pexp option) list =
                
        (*  we cant evaluate here because variable are not in the environment *)
        match decls with
            | [] -> (SMap.fold (fun k d acc -> d::acc) merged [])
            | hd::tl ->
                match hd with
                (*  Type Info: Var:Type *)
                | ((loc, name), type_info, true) -> begin
                    try
                        (*  If found its means the instruction was declared 
                         *  before the type info. Should we allow this? *)
                        let (vd, inst, _) = SMap.find name merged in
                        let new_decl = (vd, inst, Some type_info) in
                        let new_map = SMap.add name new_decl merged in
                        (loop tl new_map)
                    with Not_found ->
                        let new_decl = (loc, name), None, Some type_info in
                        let new_map = (SMap.add name new_decl merged) in
                        (loop tl new_map) end
                    
                (* Instruction: Var = expr *)
                | ((loc, name), inst, false) -> begin
                    try
                        let (vd, _, ptyp) = SMap.find name merged in
                        let new_decl = (vd, Some inst, ptyp) in
                        let new_map = SMap.add name new_decl merged in
                        (loop tl new_map)
                    with Not_found ->
                        let new_decl = ((loc, name), Some inst, None) in
                        let new_map = SMap.add name new_decl merged in
                        (loop tl new_map) end in
                        
    let decls = loop decls SMap.empty in
    
    (*  Add Each Variable to the environment *)
    let rec add_var_env decls ctx =
        match decls with
            | [] -> ctx
            | hd::tl -> begin
                match hd with 
                    (*  Unused variable: No Instruction *)
                    (*  Warning will be printed later   *)
                    | ((loc, name), None, _) -> add_var_env tl ctx 
                    | ((loc, name), _, _) -> 
                        let ctx = add_variable name loc ctx in
                            add_var_env tl ctx end in
            
    let nctx = add_var_env decls ctx in
    
    (* Evaluate Instruction and types *)
    let rec eval_decls decls ctx acc =
        match decls with
            | [] -> acc, ctx
            | hd::tl -> begin
                match hd with 
                    | ((loc, name), Some pinst, Some ptype) ->
                        let linst, nctx = lexp_parse pinst ctx in
                        let ltyp, nctx = lexp_parse ptype nctx in
                        let nacc = ((loc, name), linst, ltyp)::acc in
                        (eval_decls tl nctx nacc)
                    | ((loc, name), Some pinst, None) ->
                        let linst, nctx = lexp_parse pinst ctx in
                        let nacc = ((loc, name), linst, UnknownType(loc))::acc in
                        (eval_decls tl nctx nacc) 
                    (* Skip the variable *)
                    | ((loc, name), None, _) -> 
                        lexp_warning loc "Unused Variable";
                        (eval_decls tl ctx acc) 
                         end in
                        
    eval_decls decls nctx []
;;

(*  Print back in CET (Close Enough Typer) 
 *      param: pretty => Should the code be indented and everything
 *)
 
              (*  pretty ? * indent level *)
type print_context = (bool * int)
 
let rec lexp_print_adv opt exp =
    let slexp_print = lexp_print_adv opt in (* short_lexp_print *)
    let pty, indent = opt in
    match exp with
        | Imm(value)             -> sexp_print value
        | Var ((loc, name), idx) -> 
            print_string name; 
            if idx >= 0 then begin
                print_string "("; print_int idx; print_string ")"; end
        
        | Let (_, decls, body)   ->
            print_string "let "; lexp_print_decls (pty, indent + 1) decls; 
            make_line " " (indent * 4 + 4);
            print_string " in "; lexp_print_adv (pty, indent + 2) body
            
        | Arrow(kind, Some (_, name), tp, loc, expr) ->
            slexp_print tp; print_string ": "; print_string name;
            print_string " -> "; slexp_print expr;
            
        | Arrow(kind, None, tp, loc, expr) ->
            slexp_print tp; print_string " -> "; slexp_print expr;
            
        | Lambda(kind, (loc, name), ltype, lbody) ->
            print_string "lambda ("; print_string (name ^ ": "); 
            slexp_print ltype; print_string ") -> "; slexp_print lbody;
            
        | Call(fname, args) -> begin  (*  /!\ Partial Print *)
            let str = match fname with
                | Var((_, name), _) -> name
                | _ -> print_string "\nhere\n"; "unkwn" in
            match str with
                (* Special Operator *)
                | "_=_" -> print_string ("(lhs" ^ " = " ^ "rhs)")
                | "_+_" -> print_string ("(lhs" ^ " + " ^ "rhs)")
                | "_-_" -> print_string ("(lhs" ^ " - " ^ "rhs)")
                | "_/_" -> print_string ("(lhs" ^ " / " ^ "rhs)")
                | "_*_" -> print_string ("(lhs" ^ " * " ^ "rhs)")
                (* not an operator *)
                | _ -> print_string ("(" ^ str ^ ")") end

        (* debug catch all *)
        | UnknownType (loc)      -> print_string "unkwn";
        | _ -> print_string "expr"
            
and lexp_print_decls opt decls =
    let pty, indent = opt in
    List.iteri (fun idx g -> match g with
        | ((loc, name), expr, ltyp) ->
            if pty && idx > 0 then make_line " " (indent * 4);
            print_string (name ^  ": "); lexp_print_adv opt ltyp; print_string "; ";
            print_string (name ^ " = "); lexp_print_adv opt expr; print_string ";";
            if pty then print_string "\n")
        decls
;;


let lexp_print = lexp_print_adv (false, 0)
            
let lexp_parse_all (p: pexp list) (ctx: lexp_context): 
                                        (lexp list * lexp_context) =
    let rec loop (plst: pexp list) ctx (acc: lexp list) = 
        match plst with
            | [] -> ((List.rev acc), ctx)
            | _  -> let lxp, new_ctx = lexp_parse (List.hd plst) ctx in
                    (loop (List.tl plst) new_ctx (lxp::acc)) in
    (loop p ctx [])
;;