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
      | L.Toplevel_Let (x0, e0) -> L.Toplevel_Let (x0, large_term0 e0)
      | L.Toplevel_LetRec _ ->
        failwith "not implemented"
    end toplevel_list in
    decl_list', toplevel_list'

and small_type0 = function
  | S.VarT x0 ->
    S.VarT x0
  | S.AccT (S.VarP x0, x1) ->
    S.AccT (S.VarP x0, x1)
  | S.ArrT (t0, t1) ->
    S.ArrT (small_type0 t0, small_type0 t1)
  | S.CodT t0 ->
    S.CodT (small_type0 t0)
  | S.EscT _ ->
    failwith "[error] ``<esc>`` is not allowed to appear at level-0 type"
and small_type1 = function
  | S.VarT x0 ->
    S.VarT x0
  | S.AccT (S.VarP x0, x1) ->
    S.AccT (S.VarP x0, x1)
  | S.ArrT (t0, t1) ->
    S.ArrT (small_type1 t0, small_type1 t1)
  | S.CodT _ ->
    failwith "[error] ``code`` is not allowed to appear at level-1 type"
  | S.EscT t0 ->
    small_type1 t0

and small_term0 = function
  | S.VarE x0 ->
    S.VarE x0
  | S.AccE (S.VarP x0, x1) ->
    S.AccE (S.VarP x0, x1)
  | S.LetE (x0, e0, e1) ->
    S.LetE (x0, small_term0 e0, small_term0 e1)
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

and small_term1 = function
  | S.VarE x0 ->
    S.VarE x0
  | S.AccE (S.VarP x0, x1) ->
    S.AccE (S.VarP x0, x1)
  | S.LetE (x0, e0, e1) ->
    S.LetE (x0, small_term1 e0, small_term1 e1)
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

and large_type0 = function
  | L.SmallT t0 ->
    L.SmallT (small_type0 t0)
  | L.ArrT (t0, t1) ->
    L.ArrT (large_type0 t0, large_type0 t1)
  | L.ModT s0 ->
    L.ModT (signature0 s0)
  | L.ModCodT s0 ->
    L.ModT (signature0 s0)

and large_type1 = function
  | L.SmallT t0 ->
    L.SmallT (small_type1 t0)
  | L.ArrT (t0, t1) ->
    L.ArrT (large_type1 t0, large_type1 t1)
  | L.ModT s0 ->
    L.ModT (signature1 s0)
  | L.ModCodT _ ->
    failwith "[error] ``code`` is not allowed to appear at level-1 type"

and large_term0 = function
  | L.SmallE e0' ->
    L.SmallE (small_term0 e0')
  | L.FunE (x0, e0) ->
    L.FunE (x0, large_term0 e0)
  | L.AppE (e0, e1) ->
    L.AppE (large_term0 e0, large_term0 e1)
  | L.IfE (e0, e1, e2) ->
    L.IfE (large_term0 e0, large_term0 e1, large_term0 e2)
  | L.LetE (x0, e0, e1) ->
    L.LetE (x0, large_term0 e0, large_term0 e1)
  | L.LetModE (x0, e0, e1) ->
    L.LetModE (x0, large_term0 e0, large_term0 e1)
  | L.ModE (m0, s0) ->
    L.ModE (structure0 m0, signature0 s0)
  | L.CodE e0 ->
    large_term1 e0

and large_term1 = function
  | L.SmallE e0' ->
    L.SmallE (small_term1 e0')
  | L.FunE (x0, e0) ->
    L.FunE (x0, large_term1 e0)
  | L.AppE (e0, e1) ->
    L.AppE (large_term1 e0, large_term1 e1)
  | L.IfE (e0, e1, e2) ->
    L.IfE (large_term1 e0, large_term1 e1, large_term1 e2)
  | L.LetE (x0, e0, e1) ->
    L.LetE (x0, large_term1 e0, large_term1 e1)
  | L.LetModE (x0, e0, e1) ->
    L.LetModE (x0, large_term1 e0, large_term1 e1)
  | L.ModE (m0, s0) ->
    L.ModE (structure1 m0, signature1 s0)
  | L.CodE _ ->
    failwith "[error] ``code`` is not allowed to appear at level-1 term"

and signature0 = function
  | S.Signature cs0 ->
    S.Signature (List.map signature_component0 cs0)
and signature_component0 = function
  | S.TypeDec (x0, t0) ->
    S.TypeDec (x0, small_type0 t0)
  | S.ValueDec (x0, t0) ->
    S.ValueDec (x0, small_type0 t0)

and signature1 = function
  | S.Signature cs0 ->
    S.Signature (List.map signature_component1 cs0)
and signature_component1 = function
  | S.TypeDec (x0, t0) ->
    S.TypeDec (x0, small_type1 t0)
  | S.ValueDec (x0, t0) ->
    S.ValueDec (x0, S.CodT (small_type1 t0))

and structure0 = function
  | S.Structure cs0 ->
    S.Structure (List.fold_right structure_component0 cs0 [])
and structure_component0 e cs =
  match e with
  | S.TypeDef (x0, t0) ->
    S.TypeDef (x0, small_type0 t0) :: cs
  | S.ValueDef (x0, t0, e0) ->
    S.ValueDef (x0, small_type0 t0, small_term0 e0) :: cs

and structure1 = function
  | S.Structure cs0 -> 
    let (_, cs0) = List.fold_left structure_component1 (identity, []) cs0 in
    S.Structure (List.rev cs0)

and structure_component1 (f, cs) = function
  | S.TypeDef (x0, t0) ->
    let t1 = small_type1 t0 in
    (f, S.TypeDef (x0, t1) :: cs)
  | S.ValueDef (x0, t0, e0) ->
    let t1 = small_type1 t0 in
    let e1 = small_term1 e0 in
    (insert_let f x0 e1, S.ValueDef (x0, S.CodT t1, S.CodE (f e1)) :: cs)

and insert_let f x0 e0 =
  fun e1 -> f (S.LetE (x0, e0, e1))
