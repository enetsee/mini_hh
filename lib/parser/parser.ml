open Core
open Reporting
module I = Program.MenhirInterpreter
module IE = MenhirLib.IncrementalEngine

module Err = struct
  type t =
    | Bad_parse_state
    | File_not_found of string
    | Parse of string option * Span.t
end

let from_menhir_pos (pos : MenhirLib.IncrementalEngine.position) =
  let line = pos.Lexing.pos_lnum
  and offset = pos.Lexing.pos_cnum
  and bol = pos.Lexing.pos_bol in
  Reporting.Pos.create ~line ~offset ~bol ()
;;

let error_msg state =
  try
    let msg = Program_errors.message @@ I.number state in
    Some msg
  with
  | _ -> None
;;

let fail _ = function
  | I.HandlingError env ->
    (match I.stack env with
     | (lazy Nil) -> Error Err.Bad_parse_state
     | (lazy (Cons (I.Element (state, _, start_pos, end_pos), _))) ->
       let start_ = from_menhir_pos start_pos
       and end_ = from_menhir_pos end_pos in
       let msg = error_msg state
       and span = Reporting.Span.create ~start_ ~end_ () in
       Error (Err.Parse (msg, span)))
  | _ -> assert false
;;

let loop st lexbuf result =
  let supplier = I.lexer_lexbuf_to_supplier (Lexer.token st) lexbuf in
  I.loop_handle (fun x -> Ok x) (fail lexbuf) supplier result
;;

let parse_string string =
  let lexbuf = Lexing.from_string string in
  let st =
    Lexer.new_state
      ~strict_lexer:true
      ~verbose_lexer:true
      ~case_sensitive:true
      ~xhp_builtin:true
      ~facebook_lang_extensions:true
      ()
  in
  loop st lexbuf @@ Program.Incremental.start lexbuf.lex_curr_p
;;

let parse_file path =
  try
    In_channel.with_file path ~f:(fun chan ->
      let lexbuf = Lexing.from_channel chan in
      let st =
        Lexer.new_state
          ~strict_lexer:true
          ~verbose_lexer:true
          ~case_sensitive:true
          ~xhp_builtin:true
          ~facebook_lang_extensions:true
          ()
      in
      loop st lexbuf @@ Program.Incremental.start lexbuf.lex_curr_p)
  with
  | _ -> Error (Err.File_not_found path)
;;
