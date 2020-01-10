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
  | Toplevel_Let (x0, xs0, ys0, e0) ->
    Printf.sprintf "let %s %s %s = %s;;"
      (pp_var x0)
      (String.concat " " @@ List.map (Printf.sprintf "(type %s)") xs0)
      (String.concat " " @@ ys0)
      (pp_core_term e0)
  | Toplevel_LetRec (x0, xs0, ys0, e0) ->
    Printf.sprintf "let rec %s %s %s = %s;;"
      (pp_var x0)
      (String.concat " " @@ List.map (Printf.sprintf "(type %s)") xs0)
      (String.concat " " @@ ys0)
      (pp_core_term e0)

and pp_var: var -> string =
  identity
and pp_core_term: core_term -> string = function
  | VarE (x0) ->
    pp_var x0
  | AccE (p0, x0) ->
    Printf.sprintf "%s.%s" 
      (pp_path p0)
      (pp_var x0)
  | FunModE (x0, s0, e0) ->
    Printf.sprintf "(fun (module %s : %s) -> %s)"
      (pp_var x0)
      (pp_mod_type s0)
      (pp_core_term e0)
  | FunE (x0, None, e0) ->
    Printf.sprintf "(fun %s -> %s)"
      (pp_var x0)
      (pp_core_term e0)
  | FunE (x0, Some t0, e0) ->
    Printf.sprintf "(fun (%s: %s) -> %s)"
      (pp_var x0)
      (pp_core_type t0)
      (pp_core_term e0)
  | AppE (e0, e1) ->
    Printf.sprintf "(%s %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | IfE (e0, e1, e2) ->
    Printf.sprintf "(if %s then %s else %s)"
      (pp_core_term e0)
      (pp_core_term e1)
      (pp_core_term e2)
  | LetE (x0, xs0, ys0, e0, e1) ->
    Printf.sprintf "let %s %s %s = %s in %s"
      (pp_var x0)
      (String.concat " " @@ List.map (Printf.sprintf "(type %s)") xs0)
      (String.concat " " @@ ys0)
      (pp_core_term e0)
      (pp_core_term e1)
  | LetRecE (x0, xs0, ys0, e0, e1) ->
    Printf.sprintf "let rec %s %s %s = %s in %s"
      (pp_var x0)
      (String.concat " " @@ List.map (Printf.sprintf "(type %s)") xs0)
      (String.concat " " @@ ys0)
      (pp_core_term e0)
      (pp_core_term e1)
  | LetModE (x0, m0, e0) ->
    Printf.sprintf "let module %s = %s in %s"
      (pp_var x0)
      (pp_mod_term m0)
      (pp_core_term e0)
  | ModE (m0, s0) ->
    Printf.sprintf "(module %s : %s)"
      (pp_mod_term m0)
      (pp_mod_type s0)
  | CodE e0 ->
    Printf.sprintf ".<%s>."
      (pp_core_term e0)
  | EscE e0 ->
    Printf.sprintf ".~(%s)"
      (pp_core_term e0)
  | RunE e0 ->
    Printf.sprintf "Runcode.run (%s)"
      (pp_core_term e0)
  | RunModE _ ->
    failwith "[error] ``run_module`` should not appear in pp_core_term"
  | IntE n0 ->
    string_of_int n0
  | BoolE b0 ->
    string_of_bool b0
  | AddE (e0, e1) ->
    Printf.sprintf "(%s + %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | SubE (e0, e1) ->
    Printf.sprintf "(%s - %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | MulE (e0, e1) ->
    Printf.sprintf "(%s * %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | DivE (e0, e1) ->
    Printf.sprintf "(%s / %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | EqE (e0, e1) ->
    Printf.sprintf "(%s = %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | NeE (e0, e1) ->
    Printf.sprintf "(%s <> %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | GtE (e0, e1) ->
    Printf.sprintf "(%s > %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | GtEqE (e0, e1) ->
    Printf.sprintf "(%s >= %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | LeE (e0, e1) ->
    Printf.sprintf "(%s < %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | LeEqE (e0, e1) ->
    Printf.sprintf "(%s <= %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | DisjE (e0, e1) ->
    Printf.sprintf "(%s || %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | ConjE (e0, e1) ->
    Printf.sprintf "(%s && %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | ConsE (e0, e1) ->
    Printf.sprintf "(%s :: %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | PairE (e0, e1) ->
    Printf.sprintf "(%s, %s)"
      (pp_core_term e0)
      (pp_core_term e1)
  | NotE e0 ->
    Printf.sprintf "(not %s)"
      (pp_core_term e0)
  | NegE e0 ->
    Printf.sprintf "(-%s)"
      (pp_core_term e0)
  | MatchE (e0, cs0) ->
    Printf.sprintf "match %s with\n%s\n"
      (pp_core_term e0)
      (String.concat "\n" @@ List.map (fun (pattern, body) ->
          Printf.sprintf "| %s -> %s"
            (pp_pattern pattern)
            (pp_core_term body)) cs0)


and pp_core_type: core_type -> string = function
  | VarT (x0) ->
    pp_var x0
  | AccT (p0, x0) ->
    Printf.sprintf "%s.%s"
      (pp_path p0)
      (pp_var x0)
  | CodT t0 ->
    Printf.sprintf "%s code"
      (pp_core_type t0)
  | EscT t0 ->
    Printf.sprintf "(%%%s)"
      (pp_core_type t0)
  | ModT s0 ->
    Printf.sprintf "(module %s)"
      (pp_mod_type s0)
  | ArrT (t0, t1) ->
    Printf.sprintf "(%s -> %s)"
      (pp_core_type t0)
      (pp_core_type t1)
  | AppT (t0, t1) ->
    Printf.sprintf "(%s %s)"
      (pp_core_type t0)
      (pp_core_type t1)
  | PairT (t0, t1) ->
    Printf.sprintf "(%s * %s)"
      (pp_core_type t0)
      (pp_core_type t1)

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
    Printf.sprintf "struct %s end"
      (pp_structure cs0)
  | UnpackM e0 ->
    Printf.sprintf "(val %s)"
      (pp_core_term e0)
  | VarM x0 ->
    (pp_var x0)

and pp_structure: structure -> string =
  fun cs0 -> String.concat " " @@ List.map pp_structure_component cs0
and pp_structure_component: structure_component -> string = function
  | TypeM (x0, Some t0) ->
    Printf.sprintf "type %s = %s"
      (pp_var x0)
      (pp_core_type t0)
  | TypeM (x0, None) ->
    Printf.sprintf "type %s"
      (pp_var x0)
  | LetRecM (x0, xs0, ys0, e0) ->
    Printf.sprintf "let rec %s %s %s = %s"
      (pp_var x0)
      (String.concat " " @@ List.map (Printf.sprintf "(type %s)") xs0)
      (String.concat " " @@ ys0)
      (pp_core_term e0)
  | LetM (x0, xs0, ys0, e0) ->
    Printf.sprintf "let %s %s %s = %s"
      (pp_var x0)
      (String.concat " " @@ List.map (Printf.sprintf "(type %s)") xs0)
      (String.concat " " @@ ys0)
      (pp_core_term e0)
  | ModM (x0, m0) ->
    Printf.sprintf "module %s = %s"
      (pp_var x0)
      (pp_mod_term m0)

and pp_mod_type: mod_type -> string = function
  | Signature (cs0) ->
    Printf.sprintf "sig %s end"
      (pp_signature cs0)
  | VarS x0 ->
    (pp_var x0)
  | Sharing (Sharing _ as s0, x0, t0) ->
    Printf.sprintf "%s and type %s = %s"
      (pp_mod_type s0)
      (pp_var x0)
      (pp_core_type t0)
  | Sharing (s0, x0, t0) ->
    Printf.sprintf "%s with type %s = %s"
      (pp_mod_type s0)
      (pp_var x0)
      (pp_core_type t0)

and pp_signature: signature -> string =
  fun cs0 -> String.concat " " @@ List.map pp_signature_component cs0
and pp_signature_component: signature_component -> string = function
  | TypeS (x0, Some t0) ->
    Printf.sprintf "type %s = %s"
      (pp_var x0)
      (pp_core_type t0)
  | TypeS (x0, None) ->
    Printf.sprintf "type %s"
      (pp_var x0)
  | ValS (x0, t0) ->
    Printf.sprintf "val %s : %s"
      (pp_var x0)
      (pp_core_type t0)
  | ModS (x0, s0) ->
    Printf.sprintf "module %s : %s"
      (pp_var x0)
      (pp_mod_type s0)

and pp_path: path -> string = function
  | VarP x0 ->
    (pp_var x0)
  | DollarP x0 ->
    "$" ^ (pp_var x0)

and pp_pattern: pattern -> string = function
  | VarPat x0 -> 
    (pp_var x0)
  | ConsPat (pat0, pat1) ->
    Printf.sprintf "(%s :: %s)"
      (pp_pattern pat0)
      (pp_pattern pat1)
  | PairPat (pat0, pat1) ->
    Printf.sprintf "(%s, %s)"
      (pp_pattern pat0)
      (pp_pattern pat1)
  | WildPat ->
    "_"
