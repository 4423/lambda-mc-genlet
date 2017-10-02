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
    | LetE    of var * core_term * core_term
    | FunE    of var * core_term
    | AppE    of core_term * core_term
    | CodE    of core_term
    | EscE    of core_term
    | RunE    of core_term
  and core_type =
    | VarT    of var
    | AccT    of path * var
    | ArrT    of core_type * core_type
    | CodT    of core_type
    | EscT    of core_type

  and mod_decl =
    | StructureDec of var * mod_term
    | SignatureDec of var * mod_type

  and mod_term  = Structure of structure | VarM of var
  and structure = structure_component list
  and structure_component =
    | TypeDef  of var * core_type
    | ValueDef of var * core_type * core_term
          
  and mod_type  = Signature of signature | VarS of var
  and signature = signature_component list
  and signature_component =
    | TypeDec  of var * core_type
    | ValueDec of var * core_type
          
  and path =
    | VarP of var
end

module Large = struct
  type core_term =
    | SmallE  of Small.core_term
    | LetE    of Small.var * core_term * core_term
    | LetModE of Small.var * core_term * core_term
    | FunE    of Small.var * core_term
    | AppE    of core_term * core_term
    | CodE    of core_term
    | ModE    of Small.mod_term * Small.mod_type
  and core_type =
    | SmallT  of Small.core_type
    | ArrT    of core_type * core_type
    | ModT    of Small.mod_type 
    | ModCodT of Small.mod_type
end

module S = Small
module L = Large

let rec f: (Syntax.mod_decl list * Syntax.core_term) -> (Small.mod_decl list * Large.core_term) =
  fun (decl_list, e) -> 
    let decl_list' = List.map begin function
      | Syntax.StructureDec (x0, m0) -> S.StructureDec (x0, norm_structure m0)
      | Syntax.SignatureDec (x0, s0) -> S.SignatureDec (x0, norm_signature s0)
    end decl_list in
    decl_list', norm_term e

and norm_term = function
  | Syntax.VarE x0 ->
    L.SmallE (S.VarE x0)
  | Syntax.AccE (Syntax.VarP x0, x1) ->
    L.SmallE (S.AccE (S.VarP x0, x1))
  | Syntax.FunE (x0, e0) -> begin
      match norm_term e0 with
      | L.SmallE e0' ->
        L.SmallE (S.FunE (x0, e0'))
      | e0 ->
        L.FunE (x0, e0)
    end
  | Syntax.AppE (e0, e1) -> begin
      match norm_term e0, norm_term e1 with
      | L.SmallE e0', L.SmallE e1' ->
        L.SmallE (S.AppE (e0', e1'))
      | e0, e1 ->
        L.AppE (e0, e1)
    end
  | Syntax.LetE (x0, e0, e1) -> begin
      match norm_term e0, norm_term e1 with
      | L.SmallE e0', L.SmallE e1' ->
        L.SmallE (S.LetE (x0, e0', e1'))
      | e0, e1 ->
        L.LetE (x0, e0, e1)
    end
  | Syntax.LetModE (x0, e0, e1) ->
    L.LetModE (x0, norm_term e0, norm_term e1)
  | Syntax.ModE (m0, s0) ->
    L.ModE (norm_structure m0, norm_signature s0)
  | Syntax.CodE e0 -> begin
      match norm_term e0 with
      | L.SmallE e0' -> L.SmallE (S.CodE e0')
      | L.FunE _ ->
        failwith "[error] function (large-term) can not appear within a code brakcet"
      | e0 ->
        L.CodE e0
    end
  | Syntax.EscE e0 -> begin
      match norm_term e0 with
      | L.SmallE e0' -> L.SmallE (S.EscE e0')
      | _ ->
        failwith "[error] ``<esc>`` is not allowed to apply to large term"
    end
  | Syntax.RunE e0 -> begin
      match norm_term e0 with
      | L.SmallE e0' -> L.SmallE (S.RunE e0')
      | _ ->
        failwith "[error] ``<run>`` is not allowed to apply to large term"
    end
and norm_type = function
  | Syntax.VarT x0 ->
    L.SmallT (S.VarT x0)
  | Syntax.AccT (Syntax.VarP x0, x1) ->
    L.SmallT (S.AccT (S.VarP x0, x1))
  | Syntax.ArrT (t0, t1) -> begin
      match norm_type t0, norm_type t1 with
      | L.SmallT t0', L.SmallT t1' ->
        L.SmallT (S.ArrT (t0', t1'))
      | t0, t1 ->
        L.ArrT (t0, t1)
    end
  | Syntax.CodT t0 -> begin
      match norm_type t0 with
      | L.SmallT t0' -> L.SmallT (S.CodT t0')
      | L.ModT s0 ->
        L.ModCodT s0
      | _ ->
        failwith "[error] ``code`` is not allowed to apply to large type"
    end
  | Syntax.EscT t0 -> begin
      match norm_type t0 with
      | L.SmallT t0' -> L.SmallT (S.EscT t0')
      | _ ->
        failwith "[error] ``%`` is not allowed to apply to large type"
    end
  | Syntax.ModT s0 ->
    L.ModT (norm_signature s0)

and norm_structure = function
  | Syntax.Structure cs0 ->
    S.Structure (List.map norm_structure_component cs0)
  | Syntax.VarM x0 ->
    S.VarM x0
and norm_structure_component = function
  | Syntax.TypeDef (x0, t0) -> begin
      match norm_type t0 with
      | L.SmallT t0' -> S.TypeDef (x0, t0')
      | _ ->
        failwith "[error] large-term can not appear within a module structure"
    end
  | Syntax.ValueDef (x0, t0, e0) -> begin
      match norm_type t0, norm_term e0 with
      | L.SmallT t0', L.SmallE e0' -> S.ValueDef (x0, t0', e0')
      | _ ->
        failwith "[error] large term/type can not appear within a module structure"
    end

and norm_signature = function
  | Syntax.Signature cs0 ->
    S.Signature (List.map norm_signature_component cs0)
  | Syntax.VarS x0 ->
    S.VarS x0
and norm_signature_component = function
  | Syntax.TypeDec (x0, t0) -> begin
      match norm_type t0 with
      | L.SmallT t0' -> S.TypeDec (x0, t0')
      | _ ->
        failwith "[error] large-type can not appear within a module signature"
    end
  | Syntax.ValueDec (x0, t0) -> begin
      match norm_type t0 with
      | L.SmallT t0' -> S.ValueDec (x0, t0')
      | _ ->
        failwith "[error] large-type can not appear within a module signature"
    end

let rec g: (Small.mod_decl list * Large.core_term) -> (Syntax.mod_decl list * Syntax.core_term) =
  fun (decl_list, e) -> 
    let decl_list' = List.map begin function
      | S.StructureDec (x0, m0) -> Syntax.StructureDec (x0, denorm_structure m0)
      | S.SignatureDec (x0, s0) -> Syntax.SignatureDec (x0, denorm_signature s0)
    end decl_list in
    decl_list', denorm_term e

and denorm_term = function
  | L.SmallE (S.VarE x0) ->
    Syntax.VarE x0
  | L.SmallE (S.AccE (S.VarP x0, x1)) ->
    Syntax.AccE (Syntax.VarP x0, x1)
  | L.SmallE (S.LetE (x0, e0, e1)) ->
    Syntax.LetE (x0, denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.FunE (x0, e0)) ->
    Syntax.FunE (x0, denorm_term (L.SmallE e0))
  | L.SmallE (S.AppE (e0, e1)) ->
    Syntax.AppE (denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.CodE e0) ->
    Syntax.CodE (denorm_term (L.SmallE e0))
  | L.SmallE (S.EscE e0) ->
    Syntax.EscE (denorm_term (L.SmallE e0))
  | L.SmallE (S.RunE e0) ->
    Syntax.RunE (denorm_term (L.SmallE e0))
  | L.LetE (x0, e0, e1) ->
    Syntax.LetE (x0, denorm_term e0, denorm_term e1)
  | L.LetModE (x0, e0, e1) ->
    Syntax.LetModE (x0, denorm_term e0, denorm_term e1)
  | L.FunE (x0, e0) ->
    Syntax.FunE (x0, denorm_term e0)
  | L.AppE (e0, e1) ->
    Syntax.AppE (denorm_term e0, denorm_term e1)
  | L.CodE e0 ->
    Syntax.CodE (denorm_term e0)
  | L.ModE (m0, s0) ->
    Syntax.ModE (denorm_structure m0, denorm_signature s0)
and denorm_type = function
  | L.SmallT (S.VarT x0) ->
    Syntax.VarT x0
  | L.SmallT (S.AccT (S.VarP x0, x1)) ->
    Syntax.AccT (Syntax.VarP x0, x1)
  | L.SmallT (S.ArrT (t0, t1)) ->
    Syntax.ArrT (denorm_type (L.SmallT t0), denorm_type (L.SmallT t1))
  | L.SmallT (S.CodT t0) ->
    Syntax.CodT (denorm_type (L.SmallT t0))
  | L.SmallT (S.EscT t0) ->
    Syntax.EscT (denorm_type (L.SmallT t0))
  | L.ArrT (t0, t1) ->
    Syntax.ArrT (denorm_type t0, denorm_type t1)
  | L.ModT s0 ->
    Syntax.ModT (denorm_signature s0)
  | L.ModCodT s0 ->
    Syntax.CodT (Syntax.ModT (denorm_signature s0))

and denorm_structure = function
  | S.Structure cs0 ->
    Syntax.Structure (List.map denorm_structure_component cs0)
  | S.VarM x0 ->
    Syntax.VarM x0
and denorm_structure_component = function
  | S.TypeDef (x0, t0) ->
    Syntax.TypeDef (x0, denorm_type (L.SmallT t0))
  | S.ValueDef (x0, t0, e0) ->
    Syntax.ValueDef (x0, denorm_type (L.SmallT t0), denorm_term (L.SmallE e0))

and denorm_signature = function
  | S.Signature cs0 ->
    Syntax.Signature (List.map denorm_signature_component cs0)
  | S.VarS x0 ->
    Syntax.VarS x0
and denorm_signature_component = function
  | S.TypeDec (x0, t0) ->
    Syntax.TypeDec (x0, denorm_type (L.SmallT t0))
  | S.ValueDec (x0, t0) ->
    Syntax.ValueDec (x0, denorm_type (L.SmallT t0))
