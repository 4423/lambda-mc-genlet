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

let rec pp_var: var -> string =
  identity

and pp_core_term: core_term -> string = function
  | VarE (x0) ->
    pp_var x0
  | FunE (x0, t0, e0) ->
    Printf.sprintf "(fun (%s: %s) -> %s)" (pp_var x0) (pp_core_type t0) (pp_core_term e0)
  | AppE (e0, e1) ->
    Printf.sprintf "(%s %s)" (pp_core_term e0) (pp_core_term e1)
  | LetE (x0, e0, e1) ->
    Printf.sprintf "let %s = %s in %s" (pp_var x0) (pp_core_term e0) (pp_core_term e1)
  | _ ->
    failwith "unknown syntax"

and pp_core_type: core_type -> string = function
  | VarT (x0) ->
    pp_var x0
  | ArrT (t0, t1) ->
    Printf.sprintf "(%s -> %s)" (pp_core_type t0) (pp_core_type t1)
  | _ ->
    failwith "unknown syntax"
