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
module Small = struct
  type var = string
  and core_term =
    | VarE    of var
    | AccE    of path * var
    | LetE    of var * var list * var list * core_term * core_term
    | LetRecE of var * var list * var list * core_term * core_term
    | FunE    of var * core_term
    | AppE    of core_term * core_term
    | IfE     of core_term * core_term * core_term
    | CodE    of core_term
    | EscE    of core_term
    | RunE    of core_term
    | BoolE   of bool
    | IntE    of int
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
    | NotE    of core_term
    | NegE    of core_term
    | PairE   of core_term * core_term
    | MatchE  of core_term * (pattern * core_term) list

  and core_type =
    | VarT    of var
    | AccT    of path * var
    | AppT    of core_type * core_type
    | ArrT    of core_type * core_type
    | CodT    of core_type
    | EscT    of core_type
    | PairT   of core_type * core_type

  and mod_decl =
    | StructureDec of var * mod_term
    | SignatureDec of var * mod_type

  and mod_term  = Structure of structure | UnpackM of core_term
  and structure = structure_component list
  and structure_component =
    | TypeM   of var * core_type
    | LetRecM of var * var list * var list * core_term
    | LetM    of var * var list * var list * core_term
          
  and mod_type  = Signature of signature | Sharing of mod_type * var * core_type
  and signature = signature_component list
  and signature_component =
    | TypeS of var * core_type option
    | ValS  of var * core_type
          
  and path =
    | VarP of var
    | DollarP of var

  and pattern =
    | VarPat  of var
    | ConsPat of pattern * pattern
    | PairPat of pattern * pattern
    | WildPat
end

module Large = struct
  type toplevel =
    | Toplevel_Let    of Small.var * Small.var list * Small.var list * core_term
    | Toplevel_LetRec of Small.var * Small.var list * Small.var list * core_term
  and core_term =
    | SmallE  of Small.core_term
    | LetE    of Small.var * Small.var list * Small.var list * core_term * core_term
    | LetRecE of Small.var * Small.var list * Small.var list * core_term * core_term
    | LetModE of Small.var * Small.mod_term * core_term
    | FunE    of Small.var * core_type * core_term
    | FunModE of Small.var * Small.mod_type * core_term
    | AppE    of core_term * core_term
    | IfE     of core_term * core_term * core_term
    | CodE    of core_term
    | ModE    of Small.mod_term * Small.mod_type
  and core_type =
    | SmallT  of Small.core_type
    | ArrT    of core_type * core_type
    | AppT    of core_type * core_type
    | PairT   of core_type * core_type
    | ModT    of Small.mod_type 
    | ModCodT of Small.mod_type
end

module S = Small
module L = Large

module Set = Set.Make (String)

let rec lookup_signature name = function
  | S.SignatureDec (name', s0) :: decl_list when name = name' -> Some s0
  | _ :: decl_list ->
    lookup_signature name decl_list
  | _ ->
    None

let rec lookup_structure name = function
  | S.StructureDec (name', m0) :: decl_list when name = name' -> Some m0
  | _ :: decl_list ->
    lookup_structure name decl_list
  | _ ->
    None

let rec f: (Syntax.mod_decl list * Syntax.toplevel list) -> (Small.mod_decl list * Large.toplevel list) =
  fun (decl_list, toplevel_list) -> 
    let decl_list' = List.rev @@ List.fold_left begin fun env -> function
      | Syntax.StructureDec (x0, m0) -> S.StructureDec (x0, norm_structure env m0) :: env
      | Syntax.SignatureDec (x0, s0) -> S.SignatureDec (x0, norm_signature env s0) :: env
    end [] decl_list in
    let toplevel_list' = List.map begin function
      | Syntax.Toplevel_Let (x0, xs0, ys0, e0) ->
        L.Toplevel_Let (x0, xs0, ys0, norm_term decl_list' e0)
      | Syntax.Toplevel_LetRec (x0, xs0, ys0, e0) ->
        L.Toplevel_LetRec (x0, xs0, ys0, norm_term decl_list' e0)
    end toplevel_list in
    decl_list', toplevel_list'

and norm_term env = function
  | Syntax.VarE x0 ->
    L.SmallE (S.VarE x0)
  | Syntax.AccE (Syntax.VarP x0, x1) ->
    L.SmallE (S.AccE (S.VarP x0, x1))
  | Syntax.AccE (Syntax.DollarP x0, x1) ->
    L.SmallE (S.AccE (S.DollarP x0, x1))
  | Syntax.FunE (x0, Some t0, e0) -> begin
      match norm_type env t0, norm_term env e0 with
      | L.SmallT _, L.SmallE e0' ->
        L.SmallE (S.FunE (x0, e0'))
      | t0, e0 ->
        L.FunE (x0, t0, e0)
    end
  | Syntax.FunE (x0, None, e0) -> begin
      match norm_term env e0 with
      | L.SmallE e0' ->
        L.SmallE (S.FunE (x0, e0'))
      | _ ->
        failwith "[error] large-term must be explicitly typed"
    end
  | Syntax.FunModE (x0, s0, e0) ->
    L.FunModE (x0, norm_signature env s0, norm_term env e0)
  | Syntax.AppE (e0, e1) -> begin
      match norm_term env e0, norm_term env e1 with
      | L.SmallE e0', L.SmallE e1' ->
        L.SmallE (S.AppE (e0', e1'))
      | e0, e1 ->
        L.AppE (e0, e1)
    end
  | Syntax.LetE (x0, xs0, ys0, e0, e1) -> begin
      match norm_term env e0, norm_term env e1 with
      | L.SmallE e0', L.SmallE e1' ->
        L.SmallE (S.LetE (x0, xs0, ys0, e0', e1'))
      | e0, e1 ->
        L.LetE (x0, xs0, ys0, e0, e1)
    end
  | Syntax.LetRecE (x0, xs0, ys0, e0, e1) -> begin
      match norm_term env e0, norm_term env e1 with
      | L.SmallE e0', L.SmallE e1' ->
        L.SmallE (S.LetRecE (x0, xs0, ys0, e0', e1'))
      | e0, e1 ->
        L.LetRecE (x0, xs0, ys0, e0, e1)
    end
  | Syntax.LetModE (x0, m0, e0) ->
    L.LetModE (x0, norm_structure env m0, norm_term env e0)
  | Syntax.IfE (e0, e1, e2) -> begin
      match norm_term env e0, norm_term env e1, norm_term env e2 with
      | L.SmallE e0', L.SmallE e1', L.SmallE e2' ->
        L.SmallE (S.IfE (e0', e1', e2'))
      | e0, e1, e2 ->
        L.IfE (e0, e1, e2)
    end
  | Syntax.ModE (m0, s0) ->
    L.ModE (norm_structure env m0, norm_signature env s0)
  | Syntax.CodE e0 -> begin
      match norm_term env e0 with
      | L.SmallE e0' -> L.SmallE (S.CodE e0')
      | L.FunE _ ->
        failwith "[error] function (large-term) can not appear within a code brakcet"
      | e0 ->
        L.CodE e0
    end
  | Syntax.EscE e0 -> begin
      match norm_term env e0 with
      | L.SmallE e0' -> L.SmallE (S.EscE e0')
      | _ ->
        failwith "[error] ``<esc>`` is not allowed to apply to large term"
    end
  | Syntax.RunE e0 -> begin
      match norm_term env e0 with
      | L.SmallE e0' -> L.SmallE (S.RunE e0')
      | _ ->
        failwith "[error] ``<run>`` is not allowed to apply to large term"
    end
  | Syntax.BoolE b0 ->
    L.SmallE (S.BoolE b0)
  | Syntax.IntE n0 ->
    L.SmallE (S.IntE n0)
  | Syntax.NegE e0 -> begin
      match norm_term env e0 with
      | L.SmallE e0' ->
        L.SmallE (S.NegE e0')
      | _ ->
        failwith "[error] ``<neg>`` is not allowed to apply to large term"
    end
  | Syntax.NotE e0 -> begin
      match norm_term env e0 with
      | L.SmallE e0' ->
        L.SmallE (S.NotE e0')
      | _ ->
        failwith "[error] ``<neg>`` is not allowed to apply to large term"
    end
  | Syntax.AddE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.AddE (e0, e1))
  | Syntax.SubE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.SubE (e0, e1))
  | Syntax.MulE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.MulE (e0, e1))
  | Syntax.DivE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.DivE (e0, e1))
  | Syntax.EqE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.EqE (e0, e1))
  | Syntax.NeE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.NeE (e0, e1))
  | Syntax.GtE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.GtE (e0, e1))
  | Syntax.LeE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.LeE (e0, e1))
  | Syntax.GtEqE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.GtEqE (e0, e1))
  | Syntax.LeEqE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.LeEqE (e0, e1))
  | Syntax.DisjE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.DisjE (e0, e1))
  | Syntax.ConjE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.ConjE (e0, e1))
  | Syntax.ConsE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.ConsE (e0, e1))
  | Syntax.PairE (e0, e1) ->
    norm_binop env ~lhs:e0 ~rhs:e1 ~f:(fun e0 e1 -> S.PairE (e0, e1))
  | Syntax.MatchE (e0, cs0) -> begin
      match norm_term env e0 with
      | L.SmallE e0' ->
        L.SmallE (S.MatchE (e0', List.map begin fun (pattern, body) ->
            match norm_pattern env pattern, norm_term env body with
            | pattern', L.SmallE body' ->
              pattern', body'
            | _ ->
              failwith "[error] large term is not allowed to appear within small term"
          end cs0))
      | _ ->
        failwith "[error] large term is not allowed to appear within small term"
    end
and norm_binop env ~f ~lhs ~rhs =
  match norm_term env lhs, norm_term env rhs with
  | L.SmallE e0', L.SmallE e1' ->
    L.SmallE (f e0' e1')
  | _ ->
    failwith "[error] large term is not allowed to appear within small term"

and norm_type env = function
  | Syntax.VarT x0 ->
    L.SmallT (S.VarT x0)
  | Syntax.AccT (Syntax.VarP x0, x1) ->
    L.SmallT (S.AccT (S.VarP x0, x1))
  | Syntax.AccT (Syntax.DollarP x0, x1) ->
    L.SmallT (S.AccT (S.DollarP x0, x1))
  | Syntax.ArrT (t0, t1) -> begin
      match norm_type env t0, norm_type env t1 with
      | L.SmallT t0', L.SmallT t1' ->
        L.SmallT (S.ArrT (t0', t1'))
      | t0, t1 ->
        L.PairT (t0, t1)
    end
  | Syntax.AppT (t0, t1) -> begin
      match norm_type env t0, norm_type env t1 with
      | L.SmallT t0', L.SmallT t1' ->
        L.SmallT (S.AppT (t0', t1'))
      | t0, t1 ->
        L.AppT (t0, t1)
    end
  | Syntax.PairT (t0, t1) -> begin
      match norm_type env t0, norm_type env t1 with
      | L.SmallT t0', L.SmallT t1' ->
        L.SmallT (S.PairT (t0', t1'))
      | t0, t1 ->
        L.PairT (t0, t1)
    end
  | Syntax.CodT t0 -> begin
      match norm_type env t0 with
      | L.SmallT t0' -> L.SmallT (S.CodT t0')
      | L.ModT s0 ->
        L.ModCodT s0
      | _ ->
        failwith "[error] ``code`` is not allowed to apply to large type"
    end
  | Syntax.EscT t0 -> begin
      match norm_type env t0 with
      | L.SmallT t0' -> L.SmallT (S.EscT t0')
      | _ ->
        failwith "[error] ``%`` is not allowed to apply to large type"
    end
  | Syntax.ModT s0 ->
    L.ModT (norm_signature env s0)

and norm_structure env = function
  | Syntax.Structure cs0 ->
    S.Structure (List.map (norm_structure_component env) cs0)
  | Syntax.VarM x0 -> begin
      match lookup_structure x0 env with
      | Some m0 -> m0
      | None ->
        failwith (Printf.sprintf "unbound module structure '%s'" x0)
    end
  | Syntax.UnpackM e0 -> begin
      match norm_term env e0 with
      | L.SmallE e0' -> S.UnpackM e0'
      | _ ->
        failwith "[error] large-term can not appear within a module structure"
    end

and norm_structure_component env = function
  | Syntax.TypeM (x0, t0) -> begin
      match norm_type env t0 with
      | L.SmallT t0' -> S.TypeM (x0, t0')
      | _ ->
        failwith "[error] large-term can not appear within a module structure"
    end
  | Syntax.LetRecM (x0, xs0, ys0, e0) -> begin
      match norm_term env e0 with
      | L.SmallE e0' -> S.LetRecM (x0, xs0, ys0, e0')
      | _ ->
        failwith "[error] large term/type can not appear within a module structure"
    end
  | Syntax.LetM (x0, xs0, ys0, e0) -> begin
      match norm_term env e0 with
      | L.SmallE e0' -> S.LetM (x0, xs0, ys0, e0')
      | _ ->
        failwith "[error] large term/type can not appear within a module structure"
    end
  | Syntax.ModM _ ->
    failwith "[error] module structure can not appear within a module structure"

and norm_signature env = function
  | Syntax.Signature cs0 ->
    S.Signature (List.map (norm_signature_component env) cs0)
  | Syntax.Sharing (s0, x0, t0) -> begin
      match norm_type env t0 with
      | L.SmallT t0' ->
        S.Sharing (norm_signature env s0, x0, t0')
      | _ ->
        failwith "[error] large-type can not appear within a sharing constraints"
    end
  | Syntax.VarS x0 -> begin
      match lookup_signature x0 env with
      | Some s0 -> s0
      | None ->
        failwith (Printf.sprintf "unbound module signature '%s'" x0)
    end

and norm_signature_component env = function
  | Syntax.TypeS (x0, Some t0) -> begin
      match norm_type env t0 with
      | L.SmallT t0' -> S.TypeS (x0, Some t0')
      | _ ->
        failwith "[error] large-type can not appear within a module signature"
    end
  | Syntax.TypeS (x0, None) ->
    S.TypeS (x0, None)
  | Syntax.ValS (x0, t0) -> begin
      match norm_type env t0 with
      | L.SmallT t0' -> S.ValS (x0, t0')
      | _ ->
        failwith "[error] large-type can not appear within a module signature"
    end
  | Syntax.ModS _ ->
    failwith "[error] module signature can not appear within a module signature"

and norm_pattern env = function
  | Syntax.VarPat x0 ->
    S.VarPat x0
  | Syntax.ConsPat (pat0, pat1) ->
    S.ConsPat (norm_pattern env pat0, norm_pattern env pat1)
  | Syntax.PairPat (pat0, pat1) ->
    S.PairPat (norm_pattern env pat0, norm_pattern env pat1)
  | Syntax.WildPat ->
    S.WildPat

let toplevel_decl_list: Syntax.mod_decl list ref =
  ref []

let rec g: (Small.mod_decl list * Large.toplevel list) -> (Syntax.mod_decl list * Syntax.toplevel list) =
  fun (decl_list, toplevel_list) -> 
    toplevel_decl_list := [];
    let decl_list' = List.map begin function
      | S.StructureDec (x0, m0) -> Syntax.StructureDec (x0, denorm_structure m0)
      | S.SignatureDec (x0, s0) -> Syntax.SignatureDec (x0, denorm_signature s0)
    end decl_list in
    let toplevel_list' = List.map begin function
      | L.Toplevel_Let (x0, xs0, ys0, e0) ->
        Syntax.Toplevel_Let (x0, xs0, ys0, denorm_term e0)
      | L.Toplevel_LetRec (x0, xs0, ys0, e0) ->
        Syntax.Toplevel_LetRec (x0, xs0, ys0, denorm_term e0)
    end toplevel_list in
    (!toplevel_decl_list @ decl_list'), toplevel_list'

and denorm_term = function
  | L.SmallE (S.VarE x0) ->
    Syntax.VarE x0
  | L.SmallE (S.AccE (S.VarP x0, x1)) ->
    Syntax.AccE (Syntax.VarP x0, x1)
  | L.SmallE (S.AccE (S.DollarP x0, x1)) ->
    Syntax.AccE (Syntax.DollarP x0, x1)
  | L.SmallE (S.LetE (x0, xs0, ys0, e0, e1)) ->
    Syntax.LetE (x0, xs0, ys0, denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.LetRecE (x0, xs0, ys0, e0, e1)) ->
    Syntax.LetRecE (x0, xs0, ys0, denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.FunE (x0, e0)) ->
    Syntax.FunE (x0, None, denorm_term (L.SmallE e0))
  | L.SmallE (S.AppE (e0, e1)) ->
    Syntax.AppE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.IfE (e0, e1, e2)) ->
    Syntax.IfE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1), denorm_term (L.SmallE e2))
  | L.SmallE (S.CodE e0) ->
    Syntax.CodE (denorm_term (L.SmallE e0))
  | L.SmallE (S.EscE e0) ->
    Syntax.EscE (denorm_term (L.SmallE e0))
  | L.SmallE (S.RunE e0) ->
    Syntax.RunE (denorm_term (L.SmallE e0))
  | L.SmallE (S.BoolE b0) ->
    Syntax.BoolE b0
  | L.SmallE (S.IntE n0) ->
    Syntax.IntE n0
  | L.SmallE (S.AddE (e0, e1)) ->
    Syntax.AddE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.SubE (e0, e1)) ->
    Syntax.SubE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.MulE (e0, e1)) ->
    Syntax.MulE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.DivE (e0, e1)) ->
    Syntax.DivE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.EqE (e0, e1)) ->
    Syntax.EqE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.NeE (e0, e1)) ->
    Syntax.NeE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.GtE (e0, e1)) ->
    Syntax.GtE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.LeE (e0, e1)) ->
    Syntax.LeE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.GtEqE (e0, e1)) ->
    Syntax.GtEqE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.LeEqE (e0, e1)) ->
    Syntax.LeEqE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.ConjE (e0, e1)) ->
    Syntax.ConjE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.DisjE (e0, e1)) ->
    Syntax.DisjE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.ConsE (e0, e1)) ->
    Syntax.ConsE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.PairE (e0, e1)) ->
    Syntax.PairE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.NotE e0) ->
    Syntax.NotE (denorm_term (L.SmallE e0))
  | L.SmallE (S.NegE e0) ->
    Syntax.NegE (denorm_term (L.SmallE e0))
  | L.SmallE (S.MatchE (e0, cs0)) ->
    Syntax.MatchE (denorm_term (L.SmallE e0),
      List.map (fun (pattern, body) -> (denorm_pattern pattern, denorm_term (L.SmallE body))) cs0)
  | L.LetE (x0, xs0, ys0, e0, e1) ->
    Syntax.LetE (x0, xs0, ys0, denorm_term e0, denorm_term e1)
  | L.LetRecE (x0, xs0, ys0, e0, e1) ->
    Syntax.LetRecE (x0, xs0, ys0, denorm_term e0, denorm_term e1)
  | L.LetModE (x0, m0, e1) ->
    Syntax.LetModE (x0, denorm_structure m0, denorm_term e1)
  | L.FunModE (x0, s0, e0) ->
    Syntax.FunModE (x0, denorm_signature s0, denorm_term e0)
  | L.FunE (x0, t0,  e0) ->
    Syntax.FunE (x0, Some (denorm_type t0), denorm_term e0)
  | L.AppE (e0, e1) ->
    Syntax.AppE (denorm_term e0, denorm_term e1)
  | L.IfE (e0, e1, e2) ->
    Syntax.IfE (denorm_term e0, denorm_term e1, denorm_term e2)
  | L.CodE e0 ->
    Syntax.CodE (denorm_term e0)
  | L.ModE (m0, s0) ->
    Syntax.ModE (denorm_structure m0, denorm_signature s0)

and denorm_type = function
  | L.SmallT (S.VarT x0) ->
    Syntax.VarT x0
  | L.SmallT (S.AccT (S.VarP x0, x1)) ->
    Syntax.AccT (Syntax.VarP x0, x1)
  | L.SmallT (S.AccT (S.DollarP x0, x1)) ->
    Syntax.AccT (Syntax.DollarP x0, x1)
  | L.SmallT (S.ArrT (t0, t1)) ->
    Syntax.ArrT (denorm_type (L.SmallT t0), denorm_type (L.SmallT t1))
  | L.SmallT (S.AppT (t0, t1)) ->
    Syntax.AppT (denorm_type (L.SmallT t0), denorm_type (L.SmallT t1))
  | L.SmallT (S.PairT (t0, t1)) ->
    Syntax.PairT (denorm_type (L.SmallT t0), denorm_type (L.SmallT t1))
  | L.SmallT (S.CodT t0) ->
    Syntax.CodT (denorm_type (L.SmallT t0))
  | L.SmallT (S.EscT t0) ->
    Syntax.EscT (denorm_type (L.SmallT t0))
  | L.ArrT (t0, t1) ->
    Syntax.ArrT (denorm_type t0, denorm_type t1)
  | L.AppT (t0, t1) ->
    Syntax.AppT (denorm_type t0, denorm_type t1)
  | L.PairT (t0, t1) ->
    Syntax.PairT (denorm_type t0, denorm_type t1)
  | L.ModT s0 ->
    Syntax.ModT (denorm_signature s0)
  | L.ModCodT s0 ->
    Syntax.CodT (Syntax.ModT (denorm_signature s0))

and denorm_structure = function
  | S.Structure cs0 ->
    let set = List.fold_right Set.union (List.map dollar_structure_component cs0) Set.empty in
    let (bindings, cs1) = List.split @@ List.map begin fun var ->
      let con = Fresh.con () in
      ((var, con), Syntax.ModM (con, Syntax.UnpackM (Syntax.VarE var)))
    end (Set.elements set) in
    Syntax.Structure (cs1 @ List.map begin fun c -> 
        denorm_structure_component @@ (rename_structure_component bindings c)
      end cs0)
  | S.UnpackM e0 ->
    Syntax.UnpackM (denorm_term (L.SmallE e0))

and denorm_structure_component = function
  | S.TypeM (x0, t0) ->
    Syntax.TypeM (x0, denorm_type (L.SmallT t0))
  | S.LetRecM (x0, xs0, ys0, e0) ->
    Syntax.LetRecM (x0, xs0, ys0, denorm_term (L.SmallE e0))
  | S.LetM (x0, xs0, ys0, e0) ->
    Syntax.LetM (x0, xs0, ys0, denorm_term (L.SmallE e0))

and denorm_signature = function
  | S.Signature cs0 ->
    let x0 = Fresh.con () in
    let s0 = Syntax.Signature (List.map denorm_signature_component cs0) in
    toplevel_decl_list := !toplevel_decl_list @ [Syntax.SignatureDec (x0, s0)];
    Syntax.VarS x0
  | S.Sharing (s0, x0, t0) ->
    Syntax.Sharing (denorm_signature s0, x0, denorm_type (L.SmallT t0))

and denorm_signature_component = function
  | S.TypeS (x0, Some t0) ->
    Syntax.TypeS (x0, Some (denorm_type (L.SmallT t0)))
  | S.TypeS (x0, None) ->
    Syntax.TypeS (x0, None)
  | S.ValS (x0, t0) ->
    Syntax.ValS (x0, denorm_type (L.SmallT t0))

and denorm_pattern = function
  | S.VarPat x0 ->
    Syntax.VarPat x0
  | S.ConsPat (pat0, pat1) ->
    Syntax.ConsPat (denorm_pattern pat0, denorm_pattern pat1)
  | S.PairPat (pat0, pat1) ->
    Syntax.PairPat (denorm_pattern pat0, denorm_pattern pat1)
  | S.WildPat ->
    Syntax.WildPat


and dollar_structure_component = function
  | S.TypeM (_, t0) ->
    dollar_core_type t0
  | S.LetRecM (_, _, _, e0) ->
    dollar_core_term e0
  | S.LetM (_, _, _, e0) ->
    dollar_core_term e0

and dollar_core_term = function
  | S.AccE (S.DollarP x0, _) ->
    Set.singleton x0
  | S.IfE (e0, e1, e2) ->
    Set.union (dollar_core_term e0) (Set.union (dollar_core_term e1) (dollar_core_term e2))
  | S.LetE (_, _, _, e0, e1) | S.LetRecE (_, _, _, e0, e1) | S.AppE (e0, e1)
  | S.AddE (e0, e1) | S.SubE (e0, e1) | S.MulE (e0, e1) | S.DivE (e0, e1)
  | S.EqE (e0, e1)  | S.NeE (e0, e1)  | S.GtE (e0, e1)  | S.LeE (e0, e1) | S.GtEqE (e0, e1) | S.LeEqE (e0, e1)
  | S.ConjE (e0, e1) | S.DisjE (e0, e1) | S.ConsE (e0, e1) | S.PairE (e0, e1) ->
    Set.union (dollar_core_term e0) (dollar_core_term e1)
  | S.FunE (_, e0) | S.CodE e0 | S.EscE e0 | S.RunE e0 | S.NotE e0 | S.NegE e0 ->
    dollar_core_term e0
  | S.MatchE (e0, cs0) ->
    List.fold_right (fun (_, e) -> Set.union (dollar_core_term e)) cs0 (dollar_core_term e0)
  | _ ->
    Set.empty

and dollar_core_type = function
  | S.AccT (S.DollarP x0, _) ->
    Set.singleton x0
  | S.ArrT (t0, t1) | S.PairT (t0, t1) ->
    Set.union (dollar_core_type t0) (dollar_core_type t1)
  | S.CodT t0 | S.EscT t0 ->
    dollar_core_type t0
  | _ ->
    Set.empty
 
and rename_structure_component env = function
  | S.TypeM (x0, t0) ->
    S.TypeM (x0, rename_core_type env t0)
  | S.LetRecM (x0, xs0, ys0, e0) ->
    S.LetRecM (x0, xs0, ys0, rename_core_term env e0)
  | S.LetM (x0, xs0, ys0, e0) ->
    S.LetM (x0, xs0, ys0, rename_core_term env e0)

and rename_core_term env = function
  | S.VarE x0 ->
    S.VarE x0
  | S.AccE (S.VarP x0, x1) ->
    S.AccE (S.VarP x0, x1)
  | S.AccE (S.DollarP x0, x1) ->
    S.AccE (S.VarP (List.assoc x0 env), x1)
  | S.IfE (e0, e1, e2) ->
    S.IfE (rename_core_term env e0, rename_core_term env e1, rename_core_term env e1)
  | S.LetRecE (x0, xs0, ys0, e0, e1) ->
    S.LetRecE (x0, xs0, ys0, rename_core_term env e0, rename_core_term env e1)
  | S.LetE (x0, xs0, ys0, e0, e1) ->
    S.LetE (x0, xs0, ys0, rename_core_term env e0, rename_core_term env e1)
  | S.AppE (e0, e1) ->
    S.AppE (rename_core_term env e0, rename_core_term env e1)
  | S.FunE (x0, e0) ->
    S.FunE (x0, rename_core_term env e0)
  | S.CodE e0 ->
    S.CodE (rename_core_term env e0)
  | S.EscE e0 ->
    S.EscE (rename_core_term env e0)
  | S.RunE e0 ->
    S.RunE (rename_core_term env e0)
  | S.BoolE b0 ->
    S.BoolE b0
  | S.IntE n0 ->
    S.IntE n0
  | S.AddE (e0, e1) ->
    S.AddE (rename_core_term env e0, rename_core_term env e1)
  | S.SubE (e0, e1) ->
    S.SubE (rename_core_term env e0, rename_core_term env e1)
  | S.MulE (e0, e1) ->
    S.MulE (rename_core_term env e0, rename_core_term env e1)
  | S.DivE (e0, e1) ->
    S.DivE (rename_core_term env e0, rename_core_term env e1)
  | S.EqE (e0, e1) ->
    S.EqE (rename_core_term env e0, rename_core_term env e1)
  | S.NeE (e0, e1) ->
    S.NeE (rename_core_term env e0, rename_core_term env e1)
  | S.GtE (e0, e1) ->
    S.GtE (rename_core_term env e0, rename_core_term env e1)
  | S.LeE (e0, e1) ->
    S.LeE (rename_core_term env e0, rename_core_term env e1)
  | S.GtEqE (e0, e1) ->
    S.GtEqE (rename_core_term env e0, rename_core_term env e1)
  | S.LeEqE (e0, e1) ->
    S.LeEqE (rename_core_term env e0, rename_core_term env e1)
  | S.ConjE (e0, e1) ->
    S.ConjE (rename_core_term env e0, rename_core_term env e1)
  | S.DisjE (e0, e1) ->
    S.DisjE (rename_core_term env e0, rename_core_term env e1)
  | S.ConsE (e0, e1) ->
    S.ConsE (rename_core_term env e0, rename_core_term env e1)
  | S.NotE e0 ->
    S.NotE (rename_core_term env e0)
  | S.NegE e0 ->
    S.NegE (rename_core_term env e0)
  | S.MatchE (e0, cs0) ->
    S.MatchE (rename_core_term env e0, 
      List.map (fun (pattern, body) -> (pattern, rename_core_term env body)) cs0)
  | S.PairE (e0, e1) ->
    S.PairE (rename_core_term env e0, rename_core_term env e1)

and rename_core_type env = function
  | S.VarT x0 ->
    S.VarT x0
  | S.AccT (S.VarP x0, x1) ->
    S.AccT (S.VarP x0, x1)
  | S.AccT (S.DollarP x0, x1) ->
    S.AccT (S.VarP (List.assoc x0 env), x1)
  | S.ArrT (t0, t1) ->
    S.ArrT (rename_core_type env t0, rename_core_type env t1)
  | S.AppT (t0, t1) ->
    S.AppT (rename_core_type env t0, rename_core_type env t1)
  | S.PairT (t0, t1) ->
    S.PairT (rename_core_type env t0, rename_core_type env t1)
  | S.CodT t0 ->
    S.CodT (rename_core_type env t0)
  | S.EscT t0 ->
    S.EscT (rename_core_type env t0)
