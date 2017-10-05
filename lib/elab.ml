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
open Norm
module S = Small
module L = Large

external identity: 'a -> 'a = "%identity"

let rec f : (S.mod_decl list * L.toplevel list) -> (S.mod_decl list * L.toplevel list) =
  fun (decl_list, toplevel_list) ->
    let decl_list' = List.map begin function
      | S.StructureDec (x0, m0) -> S.StructureDec (x0, structure0 m0)
      | S.SignatureDec (x0, s0) -> S.SignatureDec (x0, signature0 s0)
    end decl_list in
    let toplevel_list' = List.map begin function
      | L.Toplevel_Let (x0, xs0, ys0, e0) ->
        L.Toplevel_Let (x0, xs0, ys0, large_term0 e0)
      | L.Toplevel_LetRec (x0, xs0, ys0, e0) ->
        L.Toplevel_LetRec (x0, xs0, ys0, large_term0 e0)
    end toplevel_list in
    decl_list', toplevel_list'

and small_type0 = function
  | S.VarT x0 ->
    S.VarT x0
  | S.AccT (S.VarP x0, x1) ->
    S.AccT (S.VarP x0, x1)
  | S.AccT (S.DollarP x0, x1) ->
    S.AccT (S.DollarP x0, x1)
  | S.ArrT (t0, t1) ->
    S.ArrT (small_type0 t0, small_type0 t1)
  | S.AppT (t0, t1) ->
    S.AppT (small_type0 t0, small_type0 t1)
  | S.PairT (t0, t1) ->
    S.PairT (small_type0 t0, small_type0 t1)
  | S.CodT t0 ->
    S.CodT (small_type0 t0)
  | S.EscT _ ->
    failwith "[error] ``<esc>`` is not allowed to appear at level-0 type"
and small_type1 = function
  | S.VarT x0 ->
    S.VarT x0
  | S.AccT (S.VarP x0, x1) ->
    S.AccT (S.VarP x0, x1)
  | S.AccT (S.DollarP x0, x1) ->
    S.AccT (S.DollarP x0, x1)
  | S.ArrT (t0, t1) ->
    S.ArrT (small_type1 t0, small_type1 t1)
  | S.AppT (t0, t1) ->
    S.AppT (small_type1 t0, small_type1 t1)
  | S.PairT (t0, t1) ->
    S.PairT (small_type1 t0, small_type1 t1)
  | S.CodT _ ->
    failwith "[error] ``code`` is not allowed to appear at level-1 type"
  | S.EscT t0 ->
    small_type1 t0

and small_term0 = function
  | S.VarE x0 ->
    S.VarE x0
  | S.AccE (S.VarP x0, x1) ->
    S.AccE (S.VarP x0, x1)
  | S.AccE (S.DollarP x0, x1) ->
    S.AccE (S.DollarP x0, x1)
  | S.LetE (x0, xs0, ys0, e0, e1) ->
    S.LetE (x0, xs0, ys0, small_term0 e0, small_term0 e1)
  | S.LetRecE (x0, xs0, ys0, e0, e1) ->
    S.LetRecE (x0, xs0, ys0, small_term0 e0, small_term0 e1)
  | S.FunE (x0, e0) ->
    S.FunE (x0, small_term0 e0)
  | S.AppE (e0, e1) ->
    S.AppE (small_term0 e0, small_term0 e1)
  | S.IfE (e0, e1, e2) ->
    S.IfE (small_term0 e0, small_term0 e1, small_term0 e2)
  | S.CodE e0 ->
    S.CodE (small_term0 e0)
  | S.RunE e0 ->
    S.RunE (small_term0 e0)
  | S.EscE _ ->
    failwith "[error] ``<esc>`` is not allowed to appear at level-0 term"
  | S.BoolE b0 ->
    S.BoolE b0
  | S.IntE n0 ->
    S.IntE n0
  | S.AddE (e0, e1) ->
    S.AddE (small_term0 e0, small_term0 e1)
  | S.SubE (e0, e1) ->
    S.SubE (small_term0 e0, small_term0 e1)
  | S.MulE (e0, e1) ->
    S.MulE (small_term0 e0, small_term0 e1)
  | S.DivE (e0, e1) ->
    S.DivE (small_term0 e0, small_term0 e1)
  | S.EqE (e0, e1) ->
    S.EqE (small_term0 e0, small_term0 e1)
  | S.NeE (e0, e1) ->
    S.NeE (small_term0 e0, small_term0 e1)
  | S.GtE (e0, e1) ->
    S.GtE (small_term0 e0, small_term0 e1)
  | S.GtEqE (e0, e1) ->
    S.GtEqE (small_term0 e0, small_term0 e1)
  | S.LeE (e0, e1) ->
    S.LeE (small_term0 e0, small_term0 e1)
  | S.LeEqE (e0, e1) ->
    S.LeEqE (small_term0 e0, small_term0 e1)
  | S.ConjE (e0, e1) ->
    S.ConjE (small_term0 e0, small_term0 e1)
  | S.DisjE (e0, e1) ->
    S.DisjE (small_term0 e0, small_term0 e1)
  | S.ConsE (e0, e1) ->
    S.ConsE (small_term0 e0, small_term0 e1)
  | S.PairE (e0, e1) ->
    S.PairE (small_term0 e0, small_term0 e1)
  | S.NotE e0 ->
    S.NotE (small_term0 e0)
  | S.NegE e0 ->
    S.NegE (small_term0 e0)
  | S.MatchE (e0, cs0) ->
    S.MatchE (small_term0 e0,
      List.map (fun (pattern, body) -> (pattern, small_term0 body)) cs0)

and small_term1 = function
  | S.VarE x0 ->
    S.VarE x0
  | S.AccE (S.VarP x0, x1) ->
    S.AccE (S.VarP x0, x1)
  | S.AccE (S.DollarP x0, x1) ->
    S.AccE (S.DollarP x0, x1)
  | S.LetE (x0, xs0, ys0, e0, e1) ->
    S.LetE (x0, xs0, ys0, small_term1 e0, small_term1 e1)
  | S.LetRecE (x0, xs0, ys0, e0, e1) ->
    S.LetRecE (x0, xs0, ys0, small_term1 e0, small_term1 e1)
  | S.FunE (x0, e0) ->
    S.FunE (x0, small_term1 e0)
  | S.AppE (e0, e1) ->
    S.AppE (small_term1 e0, small_term1 e1)
  | S.IfE (e0, e1, e2) ->
    S.IfE (small_term1 e0, small_term1 e1, small_term1 e2)
  | S.CodE _ ->
    failwith "[error] ``code`` is not allowed to appear at level-1 term"
  | S.RunE _ ->
    failwith "[error] ``run`` is not allowed to appear at level-1 term"
  | S.EscE e0 ->
    S.EscE (small_term0 e0)
  | S.BoolE b0 ->
    S.BoolE b0
  | S.IntE n0 ->
    S.IntE n0
  | S.AddE (e0, e1) ->
    S.AddE (small_term1 e0, small_term1 e1)
  | S.SubE (e0, e1) ->
    S.SubE (small_term1 e0, small_term1 e1)
  | S.MulE (e0, e1) ->
    S.MulE (small_term1 e0, small_term1 e1)
  | S.DivE (e0, e1) ->
    S.DivE (small_term1 e0, small_term1 e1)
  | S.EqE (e0, e1) ->
    S.EqE (small_term1 e0, small_term1 e1)
  | S.NeE (e0, e1) ->
    S.NeE (small_term1 e0, small_term1 e1)
  | S.GtE (e0, e1) ->
    S.GtE (small_term1 e0, small_term1 e1)
  | S.GtEqE (e0, e1) ->
    S.GtEqE (small_term1 e0, small_term1 e1)
  | S.LeE (e0, e1) ->
    S.LeE (small_term1 e0, small_term1 e1)
  | S.LeEqE (e0, e1) ->
    S.LeEqE (small_term1 e0, small_term1 e1)
  | S.ConjE (e0, e1) ->
    S.ConjE (small_term1 e0, small_term1 e1)
  | S.DisjE (e0, e1) ->
    S.DisjE (small_term1 e0, small_term1 e1)
  | S.ConsE (e0, e1) ->
    S.ConsE (small_term1 e0, small_term1 e1)
  | S.PairE (e0, e1) ->
    S.PairE (small_term1 e0, small_term1 e1)
  | S.NotE e0 ->
    S.NotE (small_term1 e0)
  | S.NegE e0 ->
    S.NegE (small_term1 e0)
  | S.MatchE (e0, cs0) ->
    S.MatchE (small_term1 e0,
      List.map (fun (pattern, body) -> (pattern, small_term1 body)) cs0)

and large_type0 = function
  | L.SmallT t0 ->
    L.SmallT (small_type0 t0)
  | L.ArrT (t0, t1) ->
    L.ArrT (large_type0 t0, large_type0 t1)
  | L.AppT (t0, t1) ->
    L.AppT (large_type0 t0, large_type0 t1)
  | L.PairT (t0, t1) ->
    L.PairT (large_type0 t0, large_type0 t1)
  | L.ModT s0 ->
    L.ModT (signature0 s0)
  | L.ModCodT s0 ->
    L.ModT (signature1 s0)

and large_type1 = function
  | L.SmallT t0 ->
    L.SmallT (small_type1 t0)
  | L.ArrT (t0, t1) ->
    L.ArrT (large_type1 t0, large_type1 t1)
  | L.AppT (t0, t1) ->
    L.AppT (large_type1 t0, large_type1 t1)
  | L.PairT (t0, t1) ->
    L.PairT (large_type1 t0, large_type1 t1)
  | L.ModT s0 ->
    L.ModT (signature1 s0)
  | L.ModCodT _ ->
    failwith "[error] ``code`` is not allowed to appear at level-1 type"

and large_term0 = function
  | L.SmallE e0' ->
    L.SmallE (small_term0 e0')
  | L.FunE (x0, t0, e0) ->
    L.FunE (x0, large_type0 t0, large_term0 e0)
  | L.FunModE (x0, s0, e0) ->
    L.FunModE (x0, signature0 s0, large_term0 e0)
  | L.AppE (e0, e1) ->
    L.AppE (large_term0 e0, large_term0 e1)
  | L.IfE (e0, e1, e2) ->
    L.IfE (large_term0 e0, large_term0 e1, large_term0 e2)
  | L.LetE (x0, xs0, ys0, e0, e1) ->
    L.LetE (x0, xs0, ys0, large_term0 e0, large_term0 e1)
  | L.LetRecE (x0, xs0, ys0, e0, e1) ->
    L.LetRecE (x0, xs0, ys0, large_term0 e0, large_term0 e1)
  | L.LetModE (x0, m0, e0) ->
    L.LetModE (x0, structure0 m0, large_term0 e0)
  | L.ModE (m0, s0) ->
    L.ModE (structure0 m0, signature0 s0)
  | L.CodE e0 ->
    large_term1 e0

and large_term1 = function
  | L.SmallE e0' ->
    L.SmallE (small_term1 e0')
  | L.FunE (x0, t0, e0) ->
    L.FunE (x0, large_type1 t0, large_term1 e0)
  | L.FunModE (x0, s0, e0) ->
    L.FunModE (x0, signature1 s0, large_term1 e0)
  | L.AppE (e0, e1) ->
    L.AppE (large_term1 e0, large_term1 e1)
  | L.IfE (e0, e1, e2) ->
    L.IfE (large_term1 e0, large_term1 e1, large_term1 e2)
  | L.LetE (x0, xs0, ys0, e0, e1) ->
    L.LetE (x0, xs0, ys0, large_term1 e0, large_term1 e1)
  | L.LetRecE (x0, xs0, ys0, e0, e1) ->
    L.LetRecE (x0, xs0, ys0, large_term1 e0, large_term1 e1)
  | L.LetModE (x0, m0, e0) ->
    L.LetModE (x0, structure1 m0, large_term1 e0)
  | L.ModE (m0, s0) ->
    L.ModE (structure1 m0, signature1 s0)
  | L.CodE _ ->
    failwith "[error] ``code`` is not allowed to appear at level-1 term"

and signature0 = function
  | S.Signature cs0 ->
    S.Signature (List.map signature_component0 cs0)
  | S.Sharing (s0, x0, t0) ->
    S.Sharing (signature0 s0, x0, small_type0 t0)
and signature_component0 = function
  | S.TypeS (x0, Some t0) ->
    S.TypeS (x0, Some (small_type0 t0))
  | S.TypeS (x0, None) ->
    S.TypeS (x0, None)
  | S.ValS (x0, t0) ->
    S.ValS (x0, small_type0 t0)

and signature1 = function
  | S.Signature cs0 ->
    S.Signature (List.map signature_component1 cs0)
  | S.Sharing (s0, x0, t0) ->
    S.Sharing (signature1 s0, x0, small_type1 t0)
and signature_component1 = function
  | S.TypeS (x0, Some t0) ->
    S.TypeS (x0, Some (small_type1 t0))
  | S.TypeS (x0, None) ->
    S.TypeS (x0, None)
  | S.ValS (x0, t0) ->
    S.ValS (x0, S.CodT (small_type1 t0))

and structure0 = function
  | S.Structure cs0 ->
    S.Structure (List.fold_right structure_component0 cs0 [])
  | S.UnpackM e0 ->
    S.UnpackM (small_term0 e0)

and structure_component0 e cs =
  match e with
  | S.TypeM (x0, t0) ->
    S.TypeM (x0, small_type0 t0) :: cs
  | S.LetRecM (x0, xs0, ys0, e0) ->
    S.LetRecM (x0, xs0, ys0, small_term0 e0) :: cs
  | S.LetM (x0, xs0, ys0, e0) ->
    S.LetM (x0, xs0, ys0, small_term0 e0) :: cs

and structure1 = function
  | S.Structure cs0 -> 
    let (_, cs0) = List.fold_left structure_component1 (identity, []) cs0 in
    S.Structure (List.rev cs0)
  | S.UnpackM e0 ->
    S.UnpackM (small_term1 e0)

and structure_component1 (f, cs) = function
  | S.TypeM (x0, t0) ->
    let t1 = small_type1 t0 in
    (f, S.TypeM (x0, t1) :: cs)
  | S.LetM (x0, xs0, ys0, e0) ->
    let e1 = small_term1 e0 in
    (insert_let f x0 xs0 ys0 e1, S.LetM (x0, xs0, ys0, S.CodE (f e1)) :: cs)
  | S.LetRecM (x0, xs0, ys0, e0) ->
    let e1 = small_term1 (S.LetRecE (x0, xs0, ys0, e0, S.VarE x0)) in
    (insert_let f x0 [] [] e1, S.LetM (x0, [], [], S.CodE (f e1)) :: cs)

and insert_let f x0 xs0 ys0 e0 =
  fun e1 -> f (S.LetE (x0, xs0, ys0, e0, e1))
