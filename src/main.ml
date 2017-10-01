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
exception Quit of int

let parse lexbuf =
  Parser.main Lexer.token lexbuf

let parse_file filepath =
  let ichannel = open_in filepath in
  try parse (Lexing.from_channel ichannel) with
  | e -> close_in ichannel; raise e

let usage () =
  Printf.sprintf "usage: %s [<option>] <file0> <file1> ...\n" (Sys.argv.(0))

let _ =
  let open Sys in
  set_signal sigint (Signal_handle (fun n -> raise (Quit n)));
  set_signal sigusr1 (Signal_handle (fun n -> raise (Quit n)));
  let filepaths = ref [] in
  Arg.parse
    []
    (fun path -> filepaths := !filepaths @ path :: [])
    (usage ());
  try
    match !filepaths with
    | [] -> print_string @@ usage ()
    | _  ->
      List.iter begin fun path ->
        print_endline @@ Pretty.pp_core_term @@ Trans.f @@ parse_file path
      end !filepaths
  with
  | Quit n -> exit n
;;     


