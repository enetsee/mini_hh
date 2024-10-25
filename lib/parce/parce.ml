open Core
open Reporting
module I = Program.MenhirInterpreter
module IE = MenhirLib.IncrementalEngine

module Err = struct
  type t =
    | Bad_parse_state of string
    | File_not_found of string
    | Parse of string option * Span.t
  [@@deriving show]
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

let fail lexbuf = function
  | I.HandlingError env ->
    (match I.stack env with
     | (lazy Nil) -> Error (Err.Bad_parse_state (Lexing.lexeme lexbuf))
     | (lazy (Cons (I.Element (state, _, start_pos, end_pos), _))) ->
       let start_ = from_menhir_pos start_pos
       and end_ = from_menhir_pos end_pos in
       let msg = error_msg state
       and span = Reporting.Span.create ~start_ ~end_ () in
       Error (Err.Parse (msg, span)))
  | _ -> assert false
;;

let loop lexbuf result =
  let supplier = I.lexer_lexbuf_to_supplier Lexer.token lexbuf in
  I.loop_handle (fun x -> Ok x) (fail lexbuf) supplier result
;;

let parse_string str =
  let lexbuf = Lexing.from_string str in
  loop lexbuf @@ Program.Incremental.program lexbuf.lex_curr_p
;;

let parse_string_exn str = Result.ok_or_failwith @@ Result.map_error ~f:Err.show @@ parse_string str

let parse_file path =
  try
    In_channel.with_file path ~f:(fun chan ->
      let lexbuf = Lexing.from_channel chan in
      loop lexbuf @@ Program.Incremental.program lexbuf.lex_curr_p)
  with
  | _ -> Error (Err.File_not_found path)
;;
