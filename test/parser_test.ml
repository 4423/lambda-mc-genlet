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
open OUnit
open Syntax
open Parser

let _ =
  run_test_tt_main @@ begin
    "Pretty.main" >::: [
      "Syntax.VarE" >:: begin fun () ->
        let x0 = "x0" in
        let e0 = VarE x0 in
        assert_equal e0 @@ Parser.main Lexer.token (Lexing.from_string x0)
      end;
      "Syntax.FunE" >:: begin fun () ->
        let x0 = "(fun (x0:t0) -> x0)" in
        let e0 = FunE ("x0", VarT "t0", VarE "x0") in
        assert_equal e0 @@ Parser.main Lexer.token (Lexing.from_string x0)
      end;
      "Syntax.AppE" >:: begin fun () ->
        let x0 = "(x0 x1)" in
        let e0 = AppE (VarE "x0", VarE "x1") in
        assert_equal e0 @@ Parser.main Lexer.token (Lexing.from_string x0)
      end;
      "Syntax.LetE" >:: begin fun () ->
        let x0 = "let x0 = x1 in x0" in
        let e0 = LetE ("x0", VarE "x1", VarE "x0") in
        assert_equal e0 @@ Parser.main Lexer.token (Lexing.from_string x0)
      end;
      "Syntax.CodE" >:: begin fun () ->
        let x0 = ".<x0>." in
        let x1 = "(fun (x0:t0) -> .<x0>.)" in
        let e0 = CodE (VarE "x0") in
        let e1 = FunE ("x0", VarT "t0", CodE (VarE "x0")) in
        assert_equal e0 @@ Parser.main Lexer.token (Lexing.from_string x0);
        assert_equal e1 @@ Parser.main Lexer.token (Lexing.from_string x1)
      end;
      "Syntax.EscE" >:: begin fun () ->
        let x0 = ".~x0" in
        let x1 = ".~(x0)" in
        let e0 = EscE (VarE "x0") in
        assert_equal e0 @@ Parser.main Lexer.token (Lexing.from_string x0);
        assert_equal e0 @@ Parser.main Lexer.token (Lexing.from_string x1)
      end;
      "Syntax.RunE" >:: begin fun () ->
        let x0 = "Runcode.run x0" in
        let e0 = RunE (VarE "x0") in
        assert_equal e0 @@ Parser.main Lexer.token (Lexing.from_string x0)
      end;
    ]
  end
