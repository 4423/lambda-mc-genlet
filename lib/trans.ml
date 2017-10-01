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

let rec f: core_term -> core_term =
  fun e0 -> core_term0 e0

and core_term0: core_term -> core_term = function
  | VarE x0 ->
    VarE x0
  | AppE (e0, e1) ->
    AppE (core_term0 e0, core_term0 e1)
  | FunE (x0, t0, e0) ->
    FunE (x0, core_type0 t0, core_term0 e0)
  | LetE (x0, e0, e1) ->
    LetE (x0, core_term0 e0, core_term0 e1)
and core_term1: core_term -> core_term = function
  | VarE x0 ->
    VarE x0
  | AppE (e0, e1) ->
    AppE (core_term1 e0, core_term1 e1)
  | FunE (x0, t0, e0) ->
    FunE (x0, core_type1 t0, core_term1 e0)
  | LetE (x0, e0, e1) ->
    LetE (x0, core_term1 e0, core_term1 e1)

and core_type0: core_type -> core_type = function
  | VarT x0 ->
    VarT x0
  | ArrT (t0, t1) ->
    ArrT (core_type0 t0, core_type0 t1)
and core_type1: core_type -> core_type = function
  | VarT x0 ->
    VarT x0
  | ArrT (t0, t1) ->
    ArrT (core_type1 t0, core_type1 t1)
