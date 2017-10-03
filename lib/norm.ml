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
  and core_type =
    | VarT    of var
    | AccT    of path * var
    | ArrT    of core_type * core_type
    | CodT    of core_type
    | EscT    of core_type

  and mod_decl =
    | StructureDec of var * mod_term
    | SignatureDec of var * mod_type

  and mod_term  = Structure of structure
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
end

module Large = struct
  type toplevel =
    | Toplevel_Let    of Small.var * Small.var list * Small.var list * core_term
    | Toplevel_LetRec of Small.var * Small.var list * Small.var list * core_term
  and core_term =
    | SmallE  of Small.core_term
    | LetE    of Small.var * Small.var list * Small.var list * core_term * core_term
    | LetRecE of Small.var * Small.var list * Small.var list * core_term * core_term
    | LetModE of Small.var * core_term * core_term
    | FunE    of Small.var * core_term
    | FunModE of Small.var * Small.mod_type * core_term
    | AppE    of core_term * core_term
    | IfE     of core_term * core_term * core_term
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
  | Syntax.FunE (x0, e0) -> begin
      match norm_term env e0 with
      | L.SmallE e0' ->
        L.SmallE (S.FunE (x0, e0'))
      | e0 ->
        L.FunE (x0, e0)
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
  | Syntax.LetModE (x0, e0, e1) ->
    L.LetModE (x0, norm_term env e0, norm_term env e1)
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
and norm_type env = function
  | Syntax.VarT x0 ->
    L.SmallT (S.VarT x0)
  | Syntax.AccT (Syntax.VarP x0, x1) ->
    L.SmallT (S.AccT (S.VarP x0, x1))
  | Syntax.ArrT (t0, t1) -> begin
      match norm_type env t0, norm_type env t1 with
      | L.SmallT t0', L.SmallT t1' ->
        L.SmallT (S.ArrT (t0', t1'))
      | t0, t1 ->
        L.ArrT (t0, t1)
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
  | L.SmallE (S.LetE (x0, xs0, ys0, e0, e1)) ->
    Syntax.LetE (x0, xs0, ys0, denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.LetRecE (x0, xs0, ys0, e0, e1)) ->
    Syntax.LetRecE (x0, xs0, ys0, denorm_term (L.SmallE e0), denorm_term (L.SmallE e1))
  | L.SmallE (S.FunE (x0, e0)) ->
    Syntax.FunE (x0, denorm_term (L.SmallE e0))
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
  | L.LetE (x0, xs0, ys0, e0, e1) ->
    Syntax.LetE (x0, xs0, ys0, denorm_term e0, denorm_term e1)
  | L.LetRecE (x0, xs0, ys0, e0, e1) ->
    Syntax.LetRecE (x0, xs0, ys0, denorm_term e0, denorm_term e1)
  | L.LetModE (x0, e0, e1) ->
    Syntax.LetModE (x0, denorm_term e0, denorm_term e1)
  | L.FunModE (x0, s0, e0) ->
    Syntax.FunModE (x0, denorm_signature s0, denorm_term e0)
  | L.FunE (x0, e0) ->
    Syntax.FunE (x0, denorm_term e0)
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
and denorm_structure_component = function
  | S.TypeM (x0, t0) ->
    Syntax.TypeM (x0, denorm_type (L.SmallT t0))
  | S.LetM (x0, xs0, ys0, e0) ->
    Syntax.LetM (x0, xs0, ys0, denorm_term (L.SmallE e0))
  | S.LetRecM (x0, xs0, ys0, e0) ->
    Syntax.LetRecM (x0, xs0, ys0, denorm_term (L.SmallE e0))

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
