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
open Syntax

external identity: 'a -> 'a = "%identity"

let rec f: (Syntax.mod_decl list * Syntax.toplevel list) -> string =
  fun (decl_list, toplevel_list) ->
    pp_mod_decl_list decl_list ^ "\n" ^ pp_toplevel_list toplevel_list

and pp_toplevel_list: toplevel list -> string =
  fun toplevel_list ->
    String.concat " " @@ List.map pp_toplevel toplevel_list
and pp_toplevel: toplevel -> string = function
  | Toplevel_Let (x0, e0) ->
    Printf.sprintf "let %s = %s;;"
      (pp_var x0)
      (pp_core_term e0)
  | Toplevel_LetRec (x0, xs0, e0) ->
    Printf.sprintf "let rec %s %s = %s;;"
      (pp_var x0)
      (String.concat " " @@ List.map pp_var xs0)
      (pp_core_term e0)

and pp_var: var -> string =
  identity
and pp_core_term: core_term -> string = function
  | VarE (x0) ->
    pp_var x0
  | AccE (p0, x0) ->
    Printf.sprintf "%s.%s" (pp_path p0) (pp_var x0)
  | FunE (x0, e0) ->
    Printf.sprintf "(fun %s -> %s)" (pp_var x0) (pp_core_term e0)
  | AppE (e0, e1) ->
    Printf.sprintf "(%s %s)" (pp_core_term e0) (pp_core_term e1)
  | IfE (e0, e1, e2) ->
    Printf.sprintf "(if %s then %s else %s)" (pp_core_term e0) (pp_core_term e1) (pp_core_term e2)
  | LetE (x0, e0, e1) ->
    Printf.sprintf "let %s = %s in %s" (pp_var x0) (pp_core_term e0) (pp_core_term e1)
  | LetModE (x0, e0, e1) ->
    Printf.sprintf "let module %s = %s in %s" (pp_var x0) (pp_core_term e0) (pp_core_term e1)
  | ModE (m0, s0) ->
    Printf.sprintf "(module %s : %s)"  (pp_mod_term m0) (pp_mod_type s0)
  | CodE e0 ->
    Printf.sprintf ".<%s>." (pp_core_term e0)
  | EscE e0 ->
    Printf.sprintf ".~(%s)" (pp_core_term e0)
  | RunE e0 ->
    Printf.sprintf "Runcode.run (%s)" (pp_core_term e0)

and pp_core_type: core_type -> string = function
  | VarT (x0) ->
    pp_var x0
  | AccT (p0, x0) ->
    Printf.sprintf "%s.%s" (pp_path p0) (pp_var x0)
  | CodT t0 ->
    Printf.sprintf "%s code" (pp_core_type t0)
  | EscT t0 ->
    Printf.sprintf "(%%%s)" (pp_core_type t0)
  | ModT s0 ->
    Printf.sprintf "(module %s)" (pp_mod_type s0)
  | ArrT (t0, t1) ->
    Printf.sprintf "(%s -> %s)" (pp_core_type t0) (pp_core_type t1)

and pp_mod_decl_list: mod_decl list -> string =
  fun decl_list -> String.concat " " @@ List.map pp_mod_decl decl_list

and pp_mod_decl: mod_decl -> string = function
  | StructureDec (x0, m0) ->
    Printf.sprintf "module %s = %s"
      (pp_var x0)
      (pp_mod_term m0)
  | SignatureDec (x0, s0) ->
    Printf.sprintf "module type %s = %s"
      (pp_var x0)
      (pp_mod_type s0)

and pp_mod_term: mod_term -> string = function
  | Structure (cs0) ->
    Printf.sprintf "struct %s end" (pp_structure cs0)
  | VarM x0 -> x0
and pp_structure: structure -> string =
  fun cs0 -> String.concat " " @@ List.map pp_structure_component cs0
and pp_structure_component: structure_component -> string = function
  | TypeDef (x0, t0) ->
    Printf.sprintf "type %s = %s" (pp_var x0) (pp_core_type t0)
  | ValueDef (x0, t0, e0) ->
    Printf.sprintf "let %s : %s = %s" (pp_var x0) (pp_core_type t0) (pp_core_term e0)

and pp_mod_type: mod_type -> string = function
  | Signature (cs0) ->
    Printf.sprintf "sig %s end" (pp_signature cs0)
  | VarS x0 -> x0

and pp_signature: signature -> string =
  fun cs0 -> String.concat " " @@ List.map pp_signature_component cs0
and pp_signature_component: signature_component -> string = function
  | TypeDec (x0, t0) ->
    Printf.sprintf "type %s = %s" (pp_var x0) (pp_core_type t0)
  | ValueDec (x0, t0) ->
    Printf.sprintf "val %s : %s" (pp_var x0) (pp_core_type t0)

and pp_path: path -> string = function
  | VarP x0 ->
    pp_var x0
