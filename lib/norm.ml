(*
 * Copyright (c) 2017 Takahisa Watanabe <takahisa@logic.cs.tsukuba.ac.jp> All rights reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 *)
module rec E: sig
  type var = string
  type toplevel =
    | Toplevel_Let    of var * var list * var list * E0.core_term
    | Toplevel_LetRec of var * var list * var list * E0.core_term
  and mod_decl =
    | StructureDec of var * E0.mod_term
    | SignatureDec of var * mod_type

  and core_type =
    | VarT    of var
    | AccT    of path * var
    | AppT    of core_type * core_type
    | ArrT    of core_type * core_type
    | PairT   of core_type * core_type
    | CodT    of core_type
    | EscT    of core_type
    | ModT    of mod_type 
    | ModCodT of mod_type

  and mod_type = 
    | Signature of signature 
    | Sharing   of mod_type * var * core_type
  and signature = signature_component list
  and signature_component =
    | TypeS     of var * core_type option
    | ValS      of var * core_type
    | ModS      of var * mod_type

  and path =
    | VarP of var
    | DollarP of var
end = E

and E0: sig
  type core_term =
    | CodE    of E1.core_term
    | RunE    of core_term
    | ModE    of mod_term * E.mod_type
    | ModCodE of E1.mod_term * E.mod_type
    | RunModE of core_term * E.mod_type
    | LetModE of E.var * mod_term * core_term
    | FunModE of E.var * E.mod_type * core_term
    | VarE    of E.var
    | AccE    of path * E.var
    | LetE    of E.var * E.var list * E.var list * core_term * core_term
    | LetRecE of E.var * E.var list * E.var list * core_term * core_term
    | FunE    of E.var * E.core_type option * core_term
    | AppE    of core_term * core_term
    | IfE     of core_term * core_term * core_term
    | IntE    of int
    | BoolE   of bool
    | NotE    of core_term
    | NegE    of core_term
    | AddE    of core_term * core_term
    | SubE    of core_term * core_term
    | MulE    of core_term * core_term
    | DivE    of core_term * core_term
    | EqE     of core_term * core_term
    | NeE     of core_term * core_term
    | GtE     of core_term * core_term
    | GtEqE   of core_term * core_term
    | LeE     of core_term * core_term
    | LeEqE   of core_term * core_term
    | ConjE   of core_term * core_term
    | DisjE   of core_term * core_term
    | ConsE   of core_term * core_term
    | PairE   of core_term * core_term
    | MatchE  of core_term * (pattern * core_term) list

  and mod_term = 
    | VarM      of E.var
    | Structure of structure 
    | UnpackM   of core_term
  and structure = structure_component list
  and structure_component =
    | TypeM     of E.var * E.core_type option
    | LetRecM   of E.var * E.var list * E.var list * core_term
    | LetM      of E.var * E.var list * E.var list * core_term
    | ModM      of E.var * mod_term

  and pattern =
    | VarPat  of E.var
    | ConsPat of pattern * pattern
    | PairPat of pattern * pattern
    | WildPat
    
  and path =
    | VarP of E.var
    | DollarP of E.var
end = E0

and E1: sig
  type core_term =
		| EscE    of E0.core_term
    | ModE    of mod_term * E.mod_type
    | VarE    of E.var
    | AccE    of path * E.var
		| LetE    of E.var * E.var list * E.var list * core_term * core_term
    | LetRecE of E.var * E.var list * E.var list * core_term * core_term
    | FunE    of E.var * E.core_type option * core_term
    | AppE    of core_term * core_term
    | IfE     of core_term * core_term * core_term
		| IntE    of int
    | BoolE   of bool
    | NotE    of core_term
    | NegE    of core_term
    | AddE    of core_term * core_term
    | SubE    of core_term * core_term
    | MulE    of core_term * core_term
    | DivE    of core_term * core_term
    | EqE     of core_term * core_term
    | NeE     of core_term * core_term
    | GtE     of core_term * core_term
    | GtEqE   of core_term * core_term
    | LeE     of core_term * core_term
    | LeEqE   of core_term * core_term
    | ConjE   of core_term * core_term
    | DisjE   of core_term * core_term
    | ConsE   of core_term * core_term
    | PairE   of core_term * core_term
    | MatchE  of core_term * (pattern * core_term) list

  and mod_term = 
    | VarM      of E.var
    | Structure of structure 
    | UnpackM   of core_term
  and structure = structure_component list
  and structure_component =
    | TypeM     of E.var * E.core_type option
    | LetRecM   of E.var * E.var list * E.var list * core_term
    | LetM      of E.var * E.var list * E.var list * core_term
    | ModM      of E.var * mod_term

  and pattern =
    | VarPat  of E.var
    | ConsPat of pattern * pattern
    | PairPat of pattern * pattern
    | WildPat

  and path =
    | VarP of E.var
end = E1

module Set = Set.Make (String)

let rec lookup_signature name = function
  | E.SignatureDec (name', s0) :: decl_list when name = name' -> Some s0
  | _ :: decl_list ->
    lookup_signature name decl_list
  | _ ->
    None

let rec lookup_structure name = function
  | E.StructureDec (name', m0) :: decl_list when name = name' -> Some m0
  | _ :: decl_list ->
    lookup_structure name decl_list
  | _ ->
    None

let rec f: (Syntax.mod_decl list * Syntax.toplevel list) -> (E.mod_decl list * E.toplevel list) =
  fun (decl_list, toplevel_list) -> 
    let decl_list' = List.rev @@ List.fold_left begin fun env -> function
      | Syntax.StructureDec (x0, m0) -> E.StructureDec (x0, norm_structure0 env m0) :: env
      | Syntax.SignatureDec (x0, s0) -> E.SignatureDec (x0, norm_signature env s0) :: env
    end [] decl_list in
    let toplevel_list' = List.map begin function
      | Syntax.Toplevel_Let (x0, xs0, ys0, e0) ->
        E.Toplevel_Let (x0, xs0, ys0, norm_e0 decl_list' e0)
      | Syntax.Toplevel_LetRec (x0, xs0, ys0, e0) ->
        E.Toplevel_LetRec (x0, xs0, ys0, norm_e0 decl_list' e0)
    end toplevel_list in
    decl_list', toplevel_list'

and norm_e0 env = function
  | Syntax.CodE (Syntax.ModE (m0, s0))    -> E0.ModCodE (norm_structure1 env m0, norm_signature env s0)
  | Syntax.CodE e0                        -> E0.CodE (norm_e1 env e0)
  | Syntax.RunE e0                        -> E0.RunE (norm_e0 env e0)
  | Syntax.ModE (m0, s0)                  -> E0.ModE (norm_structure0 env m0, norm_signature env s0)
  | Syntax.RunModE (e0, s0)               -> E0.RunModE (norm_e0 env e0, norm_signature env s0)
  | Syntax.LetModE (x0, m0, e0)           -> E0.LetModE (x0, norm_structure0 env m0, norm_e0 env e0)
  | Syntax.FunModE (x0, s0, e0)           -> E0.FunModE (x0, norm_signature env s0, norm_e0 env e0)
  | Syntax.AccE (Syntax.VarP x0, x1)      -> E0.(AccE (VarP x0, x1))
  | Syntax.AccE (Syntax.DollarP x0, x1)   -> E0.(AccE (DollarP x0, x1))
  | Syntax.EscE _                         -> failwith "[error] ``<esc>`` is not allowed to appear at level-0 term"

  | Syntax.VarE x0                        -> E0.VarE x0
  | Syntax.IntE n0                        -> E0.IntE n0
  | Syntax.BoolE b0                       -> E0.BoolE b0
  | Syntax.LetE (x0, xs0, ys0, e0, e1)    -> E0.LetE (x0, xs0, ys0, norm_e0 env e0, norm_e0 env e1)
  | Syntax.LetRecE (x0, xs0, ys0, e0, e1) -> E0.LetRecE (x0, xs0, ys0, norm_e0 env e0, norm_e0 env e1)
  | Syntax.FunE (x0, Some t0, e0)         -> E0.FunE(x0, Some (norm_type env t0), norm_e0 env e0)
  | Syntax.FunE (x0, None, e0)            -> E0.FunE (x0, None, norm_e0 env e0)
  | Syntax.AppE (e0, e1)                  -> E0.AppE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.IfE (e0, e1, e2)               -> E0.IfE (norm_e0 env e0, norm_e0 env e1, norm_e0 env e2)
  | Syntax.NegE e0                        -> E0.NegE (norm_e0 env e0)
  | Syntax.NotE e0                        -> E0.NotE (norm_e0 env e0)
  | Syntax.AddE (e0, e1)                  -> E0.AddE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.SubE (e0, e1)                  -> E0.SubE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.MulE (e0, e1)                  -> E0.MulE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.DivE (e0, e1)                  -> E0.DivE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.EqE (e0, e1)                   -> E0.EqE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.NeE (e0, e1)                   -> E0.NeE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.GtE (e0, e1)                   -> E0.GtE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.LeE (e0, e1)                   -> E0.LeE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.GtEqE (e0, e1)                 -> E0.GtEqE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.LeEqE (e0, e1)                 -> E0.LeEqE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.DisjE (e0, e1)                 -> E0.DisjE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.ConjE (e0, e1)                 -> E0.ConjE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.ConsE (e0, e1)                 -> E0.ConsE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.PairE (e0, e1)                 -> E0.PairE (norm_e0 env e0, norm_e0 env e1)
  | Syntax.MatchE (e0, cs0)               -> E0.MatchE (norm_e0 env e0, List.map begin 
                                               fun (pattern, body) -> (norm_pattern0 env pattern, norm_e0 env body)
                                             end cs0)

and norm_e1 env = function
  | Syntax.EscE e0                        -> E1.EscE (norm_e0 env e0)
  | Syntax.ModE (m0, s0)                  -> E1.ModE (norm_structure1 env m0, norm_signature env s0)
  | Syntax.AccE (Syntax.VarP x0, x1)      -> E1.(AccE (VarP x0, x1))
  | Syntax.AccE (Syntax.DollarP _, _)     -> failwith "[error] ``dollar`` is not allowed to appear at level-1 term"
  | Syntax.RunModE _                      -> failwith "[error] ``run_module`` is not allowed to appear at level-1 term"
  | Syntax.LetModE _                      -> failwith "[error] ``let module`` is not allowed to appear at level-1 term"
  | Syntax.FunModE _                      -> failwith "[error] ``functor`` is not allowed to appear at level-1 term"
  | Syntax.CodE _                         -> failwith "[error] ``code`` is not allowed to appear at level-1 term"
  | Syntax.RunE _                         -> failwith "[error] ``run`` is not allowed to appear at level-1 term"

  | Syntax.VarE x0                        -> E1.VarE x0
  | Syntax.IntE n0                        -> E1.IntE n0
  | Syntax.BoolE b0                       -> E1.BoolE b0
  | Syntax.LetE (x0, xs0, ys0, e0, e1)    -> E1.LetE (x0, xs0, ys0, norm_e1 env e0, norm_e1 env e1)
  | Syntax.LetRecE (x0, xs0, ys0, e0, e1) -> E1.LetRecE (x0, xs0, ys0, norm_e1 env e0, norm_e1 env e1)
  | Syntax.FunE (x0, Some t0, e0)         -> E1.FunE(x0, Some (norm_type env t0), norm_e1 env e0)
  | Syntax.FunE (x0, None, e0)            -> E1.FunE (x0, None, norm_e1 env e0)
  | Syntax.AppE (e0, e1)                  -> E1.AppE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.IfE (e0, e1, e2)               -> E1.IfE (norm_e1 env e0, norm_e1 env e1, norm_e1 env e2)
  | Syntax.NegE e0                        -> E1.NegE (norm_e1 env e0)
  | Syntax.NotE e0                        -> E1.NotE (norm_e1 env e0)
  | Syntax.AddE (e0, e1)                  -> E1.AddE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.SubE (e0, e1)                  -> E1.SubE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.MulE (e0, e1)                  -> E1.MulE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.DivE (e0, e1)                  -> E1.DivE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.EqE (e0, e1)                   -> E1.EqE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.NeE (e0, e1)                   -> E1.NeE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.GtE (e0, e1)                   -> E1.GtE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.LeE (e0, e1)                   -> E1.LeE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.GtEqE (e0, e1)                 -> E1.GtEqE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.LeEqE (e0, e1)                 -> E1.LeEqE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.DisjE (e0, e1)                 -> E1.DisjE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.ConjE (e0, e1)                 -> E1.ConjE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.ConsE (e0, e1)                 -> E1.ConsE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.PairE (e0, e1)                 -> E1.PairE (norm_e1 env e0, norm_e1 env e1)
  | Syntax.MatchE (e0, cs0)               -> E1.MatchE (norm_e1 env e0, List.map begin 
                                               fun (pattern, body) -> (norm_pattern1 env pattern, norm_e1 env body)
                                             end cs0)

and norm_type env = function
  | Syntax.VarT x0                      -> E.VarT x0
  | Syntax.AccT (Syntax.VarP x0, x1)    -> E.AccT (E.VarP x0, x1)
  | Syntax.AccT (Syntax.DollarP x0, x1) -> E.AccT (E.DollarP x0, x1)
  | Syntax.ArrT (t0, t1)                -> E.ArrT (norm_type env t0, norm_type env t1)
  | Syntax.AppT (t0, t1)                -> E.AppT (norm_type env t0, norm_type env t1)
  | Syntax.PairT (t0, t1)               -> E.PairT (norm_type env t0, norm_type env t1)
  | Syntax.CodT t0 -> begin
      match norm_type env t0 with
      | E.ModT s0 -> E.ModCodT s0
      | t0'       -> E.CodT t0'
    end
  | Syntax.ModT s0 -> E.ModT (norm_signature env s0)
  | Syntax.EscT t0 -> E.EscT (norm_type env t0)

and norm_structure0 env = function
  | Syntax.Structure cs0                  -> E0.Structure (List.map (norm_structure_component0 env) cs0)
  | Syntax.UnpackM (Syntax.ModE (m0, s0)) -> E0.UnpackM (norm_e0 env (Syntax.ModE (m0, s0)))
  | Syntax.UnpackM _                      -> failwith "[error] only module is only allowed to appear within unpack"
  | Syntax.VarM x0 -> begin
    match lookup_structure x0 env with
    | Some m0 -> m0
    | None    -> failwith (Printf.sprintf "unbound module structure '%s'" x0)
  end
and norm_structure_component0 env = function
  | Syntax.TypeM (x0, Some t0)        -> E0.TypeM (x0, Some (norm_type env t0))
  | Syntax.TypeM (x0, None)           -> E0.TypeM (x0, None)
  | Syntax.LetRecM (x0, xs0, ys0, e0) -> E0.LetRecM (x0, xs0, ys0, norm_e0 env e0)
  | Syntax.LetM (x0, xs0, ys0, e0)    -> E0.LetM (x0, xs0, ys0, norm_e0 env e0)
  | Syntax.ModM (x0, m0)              -> E0.ModM (x0, norm_structure0 env m0)

and norm_structure1 env = function
  | Syntax.Structure cs0                  -> E1.Structure (List.map (norm_structure_component1 env) cs0)
  | Syntax.UnpackM (Syntax.ModE (m0, s0)) -> E1.UnpackM (norm_e1 env (Syntax.ModE (m0, s0)))
  | Syntax.UnpackM _                      -> failwith "[error] only module is only allowed to appear within unpack"
  | Syntax.VarM x0                        -> E1.VarM x0
and norm_structure_component1 env = function
  | Syntax.TypeM (x0, Some t0)        -> E1.TypeM (x0, Some (norm_type env t0))
  | Syntax.TypeM (x0, None)           -> E1.TypeM (x0, None)
  | Syntax.LetRecM (x0, xs0, ys0, e0) -> E1.LetRecM (x0, xs0, ys0, norm_e1 env e0)
  | Syntax.LetM (x0, xs0, ys0, e0)    -> E1.LetM (x0, xs0, ys0, norm_e1 env e0)
  | Syntax.ModM (x0, m0)              -> E1.ModM (x0, norm_structure1 env m0)

and norm_signature env = function
  | Syntax.Signature cs0        -> E.Signature (List.map (norm_signature_component env) cs0)
  | Syntax.Sharing (s0, x0, t0) -> E.Sharing (norm_signature env s0, x0, norm_type env t0)
  | Syntax.VarS x0 -> begin
      match lookup_signature x0 env with
      | Some s0 -> s0
      | None    -> failwith (Printf.sprintf "unbound module signature '%s'" x0)
    end
and norm_signature_component env = function
  | Syntax.TypeS (x0, Some t0) -> E.TypeS (x0, Some (norm_type env t0))
  | Syntax.TypeS (x0, None) -> E.TypeS (x0, None)
  | Syntax.ValS (x0, t0) -> E.ValS (x0, norm_type env t0)
  | Syntax.ModS (x0, m0) -> E.ModS (x0, norm_signature env m0)

and norm_pattern0 env = function
  | Syntax.VarPat x0            -> E0.VarPat x0
  | Syntax.ConsPat (pat0, pat1) -> E0.ConsPat (norm_pattern0 env pat0, norm_pattern0 env pat1)
  | Syntax.PairPat (pat0, pat1) -> E0.PairPat (norm_pattern0 env pat0, norm_pattern0 env pat1)
  | Syntax.WildPat              -> E0.WildPat
and norm_pattern1 env = function
  | Syntax.VarPat x0            -> E1.VarPat x0
  | Syntax.ConsPat (pat0, pat1) -> E1.ConsPat (norm_pattern1 env pat0, norm_pattern1 env pat1)
  | Syntax.PairPat (pat0, pat1) -> E1.PairPat (norm_pattern1 env pat0, norm_pattern1 env pat1)
  | Syntax.WildPat              -> E1.WildPat

let toplevel_decl_list: Syntax.mod_decl list ref =
  ref []

let rec g: (E.mod_decl list * E.toplevel list) -> (Syntax.mod_decl list * Syntax.toplevel list) =
  fun (decl_list, toplevel_list) -> 
    toplevel_decl_list := [];
    let decl_list' = List.map begin function
      | E.StructureDec (x0, m0) -> Syntax.StructureDec (x0, denorm_structure0 m0)
      | E.SignatureDec (x0, s0) -> Syntax.SignatureDec (x0, denorm_signature s0)
    end decl_list in
    let toplevel_list' = List.map begin function
      | E.Toplevel_Let (x0, xs0, ys0, e0) ->
        Syntax.Toplevel_Let (x0, xs0, ys0, denorm_e0 e0)
      | E.Toplevel_LetRec (x0, xs0, ys0, e0) ->
        Syntax.Toplevel_LetRec (x0, xs0, ys0, denorm_e0 e0)
    end toplevel_list in
    (!toplevel_decl_list @ decl_list'), toplevel_list'

and denorm_e0 = function
  | E0.CodE e0                        -> Syntax.CodE (denorm_e1 e0)
  | E0.RunE e0                        -> Syntax.RunE (denorm_e0 e0)
  | E0.ModE (m0, s0)                  -> Syntax.ModE (denorm_structure0 m0, denorm_signature s0)
  | E0.ModCodE _                      -> failwith "[error] ``code of a module`` should not appear in denorm"
  | E0.RunModE _                      -> failwith "[error] ``run_module`` should not appear in denorm"
  | E0.LetModE (x0, m0, e0)           -> Syntax.LetModE (x0, denorm_structure0 m0, denorm_e0 e0)
  | E0.FunModE (x0, s0, e0)           -> Syntax.FunModE (x0, denorm_signature s0, denorm_e0 e0)
  | E0.AccE (E0.VarP x0, x1)          -> Syntax.AccE (Syntax.VarP x0, x1)
  | E0.AccE (E0.DollarP x0, x1)       -> failwith "[error] ``dollar`` should not appear in denorm"
  | E0.VarE x0                        -> Syntax.VarE x0
  | E0.IntE n0                        -> Syntax.IntE n0
  | E0.BoolE b0                       -> Syntax.BoolE b0
  | E0.LetE (x0, xs0, ys0, e0, e1)    -> Syntax.LetE (x0, xs0, ys0, denorm_e0 e0, denorm_e0 e1)
  | E0.LetRecE (x0, xs0, ys0, e0, e1) -> Syntax.LetRecE (x0, xs0, ys0, denorm_e0 e0, denorm_e0 e1)
  | E0.FunE (x0, Some t0, e0)         -> Syntax.FunE (x0, Some (denorm_type t0), denorm_e0 e0)
  | E0.FunE (x0, None, e0)            -> Syntax.FunE (x0, None, denorm_e0 e0)
  | E0.AppE (e0, e1)                  -> Syntax.AppE (denorm_e0 e0, denorm_e0 e1)
  | E0.IfE (e0, e1, e2)               -> Syntax.IfE (denorm_e0 e0, denorm_e0 e1, denorm_e0 e2)
  | E0.NegE e0                        -> Syntax.NegE (denorm_e0 e0)
  | E0.NotE e0                        -> Syntax.NotE (denorm_e0 e0)
  | E0.AddE (e0, e1)                  -> Syntax.AddE (denorm_e0 e0, denorm_e0 e1)
  | E0.SubE (e0, e1)                  -> Syntax.SubE (denorm_e0 e0, denorm_e0 e1)
  | E0.MulE (e0, e1)                  -> Syntax.MulE (denorm_e0 e0, denorm_e0 e1)
  | E0.DivE (e0, e1)                  -> Syntax.DivE (denorm_e0 e0, denorm_e0 e1)
  | E0.EqE (e0, e1)                   -> Syntax.EqE (denorm_e0 e0, denorm_e0 e1)
  | E0.NeE (e0, e1)                   -> Syntax.NeE (denorm_e0 e0, denorm_e0 e1)
  | E0.GtE (e0, e1)                   -> Syntax.GtE (denorm_e0 e0, denorm_e0 e1)
  | E0.LeE (e0, e1)                   -> Syntax.LeE (denorm_e0 e0, denorm_e0 e1)
  | E0.GtEqE (e0, e1)                 -> Syntax.GtEqE (denorm_e0 e0, denorm_e0 e1)
  | E0.LeEqE (e0, e1)                 -> Syntax.LeEqE (denorm_e0 e0, denorm_e0 e1)
  | E0.DisjE (e0, e1)                 -> Syntax.DisjE (denorm_e0 e0, denorm_e0 e1)
  | E0.ConjE (e0, e1)                 -> Syntax.ConjE (denorm_e0 e0, denorm_e0 e1)
  | E0.ConsE (e0, e1)                 -> Syntax.ConsE (denorm_e0 e0, denorm_e0 e1)
  | E0.PairE (e0, e1)                 -> Syntax.PairE (denorm_e0 e0, denorm_e0 e1)
  | E0.MatchE (e0, cs0)               -> Syntax.MatchE (denorm_e0 e0, List.map begin
                                           fun (pattern, body) -> (denorm_pattern0 pattern, denorm_e0 body)
                                         end cs0)

and denorm_e1 = function
  | E1.EscE e0                        -> Syntax.EscE (denorm_e0 e0)
  | E1.ModE _                         -> failwith "[error] ``code of a module`` should not appear in denorm"
  | E1.AccE (E1.VarP x0, x1)          -> Syntax.AccE (Syntax.VarP x0, x1)
  | E1.VarE x0                        -> Syntax.VarE x0
  | E1.IntE n0                        -> Syntax.IntE n0
  | E1.BoolE b0                       -> Syntax.BoolE b0
  | E1.LetE (x0, xs0, ys0, e0, e1)    -> Syntax.LetE (x0, xs0, ys0, denorm_e1 e0, denorm_e1 e1)
  | E1.LetRecE (x0, xs0, ys0, e0, e1) -> Syntax.LetRecE (x0, xs0, ys0, denorm_e1 e0, denorm_e1 e1)
  | E1.FunE (x0, Some t0, e0)         -> Syntax.FunE (x0, Some (denorm_type t0), denorm_e1 e0)
  | E1.FunE (x0, None, e0)            -> Syntax.FunE (x0, None, denorm_e1 e0)
  | E1.AppE (e0, e1)                  -> Syntax.AppE (denorm_e1 e0, denorm_e1 e1)
  | E1.IfE (e0, e1, e2)               -> Syntax.IfE (denorm_e1 e0, denorm_e1 e1, denorm_e1 e2)
  | E1.NegE e0                        -> Syntax.NegE (denorm_e1 e0)
  | E1.NotE e0                        -> Syntax.NotE (denorm_e1 e0)
  | E1.AddE (e0, e1)                  -> Syntax.AddE (denorm_e1 e0, denorm_e1 e1)
  | E1.SubE (e0, e1)                  -> Syntax.SubE (denorm_e1 e0, denorm_e1 e1)
  | E1.MulE (e0, e1)                  -> Syntax.MulE (denorm_e1 e0, denorm_e1 e1)
  | E1.DivE (e0, e1)                  -> Syntax.DivE (denorm_e1 e0, denorm_e1 e1)
  | E1.EqE (e0, e1)                   -> Syntax.EqE (denorm_e1 e0, denorm_e1 e1)
  | E1.NeE (e0, e1)                   -> Syntax.NeE (denorm_e1 e0, denorm_e1 e1)
  | E1.GtE (e0, e1)                   -> Syntax.GtE (denorm_e1 e0, denorm_e1 e1)
  | E1.LeE (e0, e1)                   -> Syntax.LeE (denorm_e1 e0, denorm_e1 e1)
  | E1.GtEqE (e0, e1)                 -> Syntax.GtEqE (denorm_e1 e0, denorm_e1 e1)
  | E1.LeEqE (e0, e1)                 -> Syntax.LeEqE (denorm_e1 e0, denorm_e1 e1)
  | E1.DisjE (e0, e1)                 -> Syntax.DisjE (denorm_e1 e0, denorm_e1 e1)
  | E1.ConjE (e0, e1)                 -> Syntax.ConjE (denorm_e1 e0, denorm_e1 e1)
  | E1.ConsE (e0, e1)                 -> Syntax.ConsE (denorm_e1 e0, denorm_e1 e1)
  | E1.PairE (e0, e1)                 -> Syntax.PairE (denorm_e1 e0, denorm_e1 e1)
  | E1.MatchE (e0, cs0)               -> Syntax.MatchE (denorm_e1 e0, List.map begin
                                           fun (pattern, body) -> (denorm_pattern1 pattern, denorm_e1 body)
                                         end cs0)

and denorm_type = function
  | E.VarT x0                 -> Syntax.VarT x0
  | E.AccT (E.VarP x0, x1)    -> Syntax.AccT (Syntax.VarP x0, x1)
  | E.AccT (E.DollarP x0, x1) -> failwith "[error] ``dollar`` should not appear in denorm"
  | E.ArrT (t0, t1)           -> Syntax.ArrT (denorm_type t0, denorm_type t1)
  | E.AppT (t0, t1)           -> Syntax.AppT (denorm_type t0, denorm_type t1)
  | E.PairT (t0, t1)          -> Syntax.PairT (denorm_type t0, denorm_type t1)
  | E.CodT t0                 -> Syntax.CodT (denorm_type t0)
  | E.EscT t0                 -> Syntax.EscT (denorm_type t0)
  | E.ModT s0                 -> Syntax.ModT (denorm_signature s0)
  | E.ModCodT s0              -> Syntax.CodT (Syntax.ModT (denorm_signature s0))

and denorm_structure0 = function
  | E0.UnpackM e0     -> Syntax.UnpackM (denorm_e0 e0)
  | E0.Structure cs0  -> Syntax.Structure (List.map denorm_structure_component0 cs0)
  | E0.VarM x0        -> Syntax.VarM x0
and denorm_structure_component0 = function
  | E0.TypeM (x0, Some t0)        -> Syntax.TypeM (x0, Some (denorm_type t0))
  | E0.TypeM (x0, None)           -> Syntax.TypeM (x0, None)
  | E0.LetRecM (x0, xs0, ys0, e0) -> Syntax.LetRecM (x0, xs0, ys0, denorm_e0 e0)
  | E0.LetM (x0, xs0, ys0, e0)    -> Syntax.LetM (x0, xs0, ys0, denorm_e0 e0)
  | E0.ModM (x0, m0)              -> Syntax.ModM (x0, denorm_structure0 m0)

and denorm_signature = function
  | E.Signature cs0 ->
    let x0 = Fresh.con () in
    let s0 = Syntax.Signature (List.map denorm_signature_component cs0) in
    toplevel_decl_list := !toplevel_decl_list @ [Syntax.SignatureDec (x0, s0)];
    Syntax.VarS x0
  | E.Sharing (s0, x0, t0) -> Syntax.Sharing (denorm_signature s0, x0, denorm_type t0)
and denorm_signature_component = function
  | E.TypeS (x0, Some t0) -> Syntax.TypeS (x0, Some (denorm_type t0))
  | E.TypeS (x0, None)    -> Syntax.TypeS (x0, None)
  | E.ValS (x0, t0)       -> Syntax.ValS (x0, denorm_type t0)
  | E.ModS (x0, m0)       -> Syntax.ModS (x0, denorm_signature m0)

and denorm_pattern0 = function
  | E0.VarPat x0            -> Syntax.VarPat x0
  | E0.ConsPat (pat0, pat1) -> Syntax.ConsPat (denorm_pattern0 pat0, denorm_pattern0 pat1)
  | E0.PairPat (pat0, pat1) -> Syntax.PairPat (denorm_pattern0 pat0, denorm_pattern0 pat1)
  | E0.WildPat              -> Syntax.WildPat
and denorm_pattern1 = function
  | E1.VarPat x0            -> Syntax.VarPat x0
  | E1.ConsPat (pat0, pat1) -> Syntax.ConsPat (denorm_pattern1 pat0, denorm_pattern1 pat1)
  | E1.PairPat (pat0, pat1) -> Syntax.PairPat (denorm_pattern1 pat0, denorm_pattern1 pat1)
  | E1.WildPat              -> Syntax.WildPat