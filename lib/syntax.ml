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
type var = string
 and toplevel =
   | Toplevel_Let    of var * var list * var list * core_term
   | Toplevel_LetRec of var * var list * var list * core_term
 and core_term =
   | VarE    of var
   | AccE    of path * var
   | FunE    of var * core_term
   | FunModE of var * mod_type * core_term
   | AppE    of core_term * core_term
   | LetE    of var * var list * var list * core_term * core_term
   | LetRecE of var * var list * var list * core_term * core_term
   | LetModE of var * core_term * core_term
   | IfE     of core_term * core_term * core_term
   | ModE    of mod_term * mod_type
   | CodE    of core_term
   | EscE    of core_term
   | RunE    of core_term

 and core_type =
   | VarT of var
   | AccT of path * var
   | ArrT of core_type * core_type
   | CodT of core_type
   | EscT of core_type
   | ModT of mod_type

 and mod_decl =
   | StructureDec of var * mod_term
   | SignatureDec of var * mod_type

 and mod_term  = Structure of structure | VarM of var
 and structure = structure_component list
 and structure_component =
   | TypeM   of var * core_type
   | LetM    of var * var list * var list * core_term
   | LetRecM of var * var list * var list * core_term

 and mod_type  = Signature of signature | VarS of var | Sharing of mod_type * var * core_type
 and signature = signature_component list
 and signature_component =
   | TypeS  of var * core_type option
   | ValS   of var * core_type

 and path =
   | VarP of string
   | DollarP of string
