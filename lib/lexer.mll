{
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
open Parser
}

let whitespace = [' ' '\t' '\n' '\r']
let digit      = ['0'-'9']
let lower      = ['a'-'z']
let upper      = ['A'-'Z']
let alpha      = (lower | upper)
let var        = (lower | "_") (alpha | "_" | digit)*
let con        = (upper) (alpha | "_" | digit)*

rule token = parse
| whitespace+
    { token lexbuf }
| "(*"
    { comment lexbuf;
      token lexbuf }
| eof
    { EOF  }
| "+"
    { ADD }
| "-"
    { SUB }
| "*"
    { MUL }
| "/"
    { DIV }
| "="
    { EQ }
| "<>"
    { NE }
| "<"
    { LE }
| "<="
    { LE_EQ }
| ">"
    { GT }
| ">="
    { GT_EQ }
| "$"
    { DOLLAR }
| "("
    { LPAREN }
| ")"
    { RPAREN }
| ".<"
    { LCOD }
| ">."
    { RCOD }
| ".~"
    { ESC }
| "Runcode.run"
    { RUN }
| "run_module"
    { RUNMOD }
| "->"
    { SINGLE_ARROW }
| "=>"
    { DOUBLE_ARROW }
| ","
    { COMMA }
| ":"
    { COL }
| "::"
    { COL_COL }
| "."
    { DOT }
| ";"
    { SEM }
| ";;"
    { SEM_SEM }
| "()"
    { UNIT }
| "&&"
    { CONJ }
| "|"
    { BAR }
| "||"
    { DISJ }
| "true"
    { TRUE }
| "false"
    { FALSE }
| "not"
    { NOT }
| "fun"
    { FUN }
| "let"
    { LET }
| "rec"
    { REC }
| "in"
    { IN }
| "if"
    { IF }
| "then"
    { THEN }
| "else"
    { ELSE }
| "module"
    { MODULE }
| "struct"
    { STRUCTURE }
| "sig"
    { SIGNATURE }
| "end"
    { END }
| "val"
    { VAL }
| "type"
    { TYPE }
| "and"
    { AND }
| "match"
    { MATCH }
| "with"
    { WITH }
| "code"
    { CODE }
| digit+
    { INT (int_of_string @@ Lexing.lexeme lexbuf) }
| var
    { VAR (Lexing.lexeme lexbuf) }
| con
    { CON (Lexing.lexeme lexbuf) }
| _
    { failwith (Printf.sprintf "unknown token %s" (Lexing.lexeme lexbuf)) }

and comment = parse
| eof
    { Printf.eprintf "warning: unterminated comment" }
| "(*"
    { comment lexbuf;
      comment lexbuf }
| "*)"
    { () }
| _
    { comment lexbuf }
