open Core

module Action = struct
  type t =
    | Select_file of string
    | Select_def of Lang.Def.t
    | Toggle_breakpoint of int
    | Restart
    | Next
    | Prev
    | Run
end

module File_ok = struct
  type t =
    { start_directory : string
    ; current_file : string
    ; source : string list
    ; oracle : Oracle.t
    ; oracle_errs : Oracle.Err.t list
    ; defs : Lang.Def.t list
    ; breakpoints : Int.Set.t
    }

  let toggle_breakpoint ({ breakpoints; _ } as t) line =
    let breakpoints =
      if Set.mem breakpoints line
      then Set.remove breakpoints line
      else Set.add breakpoints line
    in
    { t with breakpoints }
  ;;
end

module File_error = struct
  type t =
    { start_directory : string
    ; current_file : string
    ; parse_err : Source.Parse.Err.t
    }
end

module Debugging = struct
  type t =
    { file : File_ok.t
    ; history : History.t
    ; alt : History.Alt.t
    }

  let alt { alt; _ } = alt
  let history { history; _ } = history

  let debug_def file def =
    let alt = History.Alt.init def ~oracle:file.File_ok.oracle in
    let history = History.init def in
    { file; history; alt }
  ;;

  let toggle_breakpoint ({ file; _ } as t) line =
    let file = File_ok.toggle_breakpoint file line in
    { t with file }
  ;;

  let restart ({ history; alt; _ } as t) =
    let alt = History.Alt.start alt in
    let history = History.start history in
    { t with history; alt }
  ;;

  let next ({ history; alt; _ } as t) =
    let history =
      Option.value ~default:history
      @@ History.next history ~oracle:t.file.oracle
    in
    let alt = Option.value ~default:alt @@ History.Alt.next alt in
    { t with history; alt }
  ;;

  let run ({ history; file; _ } as t) =
    let start_line =
      Reporting.Span.start_line @@ Step.span @@ fst @@ History.current history
    in
    (* let start_line =
      Reporting.Span.start_line @@ Step.span @@ History.current history
    in *)
    let breakpoints = file.breakpoints in
    let rec aux history =
      match History.next history ~oracle:file.oracle with
      | None -> t
      | Some history ->
        let line =
          Reporting.Span.start_line
          @@ Step.span
          @@ fst
          @@ History.current history
          (* Reporting.Span.start_line @@ Step.span @@ History.current history *)
        in
        if line > start_line && Set.mem breakpoints line
        then { t with history }
        else aux history
    in
    aux history
  ;;

  let prev ({ history; _ } as t) =
    Option.value_map ~default:t ~f:(fun history -> { t with history })
    @@ History.prev history
  ;;

  let current { history; _ } = History.current history
  let span t = Step.span @@ fst @@ current t
  let status t = Step.status @@ fst @@ current t
  let ctxt_def t = Step.ctxt_def @@ fst @@ current t
  let ctxt_cont t = Step.ctxt_cont @@ fst @@ current t
end

type t =
  | Uninit
  | Init of { start_directory : string }
  | File_ok of File_ok.t
  | File_error of File_error.t
  | Debugging of Debugging.t

let is_uninit = function
  | Uninit -> true
  | Init _ | File_ok _ | File_error _ | Debugging _ -> false
;;

let is_file_error = function
  | File_error _ -> true
  | Init _ | File_ok _ | Uninit | Debugging _ -> false
;;

(** Given a directory and a file, try initialise a [File_ok.t] or a [File_error.t] *)
let init_file start_directory current_file =
  match
    Result.map ~f:Lang.Prog.elab_to_generic
    @@ Source.Parse.parse_file current_file
  with
  | Error parse_err ->
    File_error File_error.{ start_directory; current_file; parse_err }
  | Ok prog ->
    let oracle, oracle_errs = Oracle.of_program prog
    and source = In_channel.read_lines current_file
    and Lang.Prog.{ defs } = prog
    and breakpoints = Int.Set.empty in
    File_ok
      File_ok.
        { start_directory
        ; current_file
        ; source
        ; oracle
        ; oracle_errs
        ; defs
        ; breakpoints
        }
;;

let start_directory = function
  | Uninit -> None
  | Init { start_directory }
  | File_ok { start_directory; _ }
  | File_error { start_directory; _ }
  | Debugging { file = { start_directory; _ }; _ } -> Some start_directory
;;

let update t ~action =
  match action, t with
  | _, Uninit -> t
  | Action.Select_file file, _ ->
    Option.value_map
      ~default:Uninit
      ~f:(fun dir -> init_file dir file)
      (start_directory t)
  | Action.Toggle_breakpoint line, File_ok file_ok ->
    File_ok (File_ok.toggle_breakpoint file_ok line)
  | Action.Toggle_breakpoint line, Debugging debugging ->
    Debugging (Debugging.toggle_breakpoint debugging line)
  | Action.Toggle_breakpoint _, (Init _ | File_error _) -> t
  | Action.Select_def def, (File_ok file | Debugging { file; _ }) ->
    Debugging (Debugging.debug_def file def)
  | Action.Select_def _, _ -> t
  | Action.Next, Debugging debugging -> Debugging (Debugging.next debugging)
  | Action.Next, (Init _ | File_ok _ | File_error _) -> t
  | Action.Prev, Debugging debugging -> Debugging (Debugging.prev debugging)
  | Action.Prev, (Init _ | File_ok _ | File_error _) -> t
  | Action.Run, Debugging debugging -> Debugging (Debugging.run debugging)
  | Action.Run, (Init _ | File_ok _ | File_error _) -> t
  | Action.Restart, Debugging debugging ->
    Debugging (Debugging.restart debugging)
  | Action.Restart, (Init _ | File_ok _ | File_error _) -> t
;;

let state = function
  | Debugging t -> Some (Step.state @@ fst @@ Debugging.current t)
  | File_error _ | File_ok _ | Init _ | Uninit -> None
;;

let definitions = function
  | File_ok model | Debugging { file = model; _ } -> model.defs
  | _ -> []
;;

let source_opt = function
  | File_ok model | Debugging { file = model; _ } -> Some model.source
  | _ -> None
;;

let span_opt = function
  | Debugging model -> Some (Debugging.span model)
  | _ -> None
;;

let status_opt = function
  | Debugging model -> Some (Debugging.status model)
  | _ -> None
;;

let history_opt = function
  | Debugging model -> Some (Debugging.history model)
  | _ -> None
;;

let alt_opt = function
  | Debugging model -> Some (Debugging.alt model)
  | _ -> None
;;

let ctxt_def_opt = function
  | Debugging model -> Some (Debugging.ctxt_def model)
  | _ -> None
;;

let ctxt_cont_opt = function
  | Debugging model -> Some (Debugging.ctxt_cont model)
  | _ -> None
;;

let breakpoints = function
  | File_ok model | Debugging { file = model; _ } -> model.breakpoints
  | _ -> Int.Set.empty
;;

let is_debugging = function
  | Debugging _ -> true
  | _ -> false
;;

let parse_err_opt = function
  | File_error { parse_err; _ } -> Some parse_err
  | _ -> None
;;
