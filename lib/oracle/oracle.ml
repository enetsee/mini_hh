open Core
module Classish = Classish
open Reporting

type t = { classish : Classish.t } [@@deriving show]

let empty = { classish = Classish.empty }
let up { classish } ~of_ ~at = Classish.up classish ~of_ ~at
let down { classish } ~of_ ~at = Classish.down classish ~of_ ~at
let param_bounds_opt { classish } ~ctor = Classish.param_bounds_opt classish ~ctor
let param_variances_opt { classish } ~ctor = Classish.param_variances_opt classish ctor
let find_ctor { classish } id = Classish.find classish id

let add_classish { classish } classish_def span =
  Result.map ~f:(fun (classish, errs) -> { classish }, errs) @@ Classish.add classish classish_def span
;;

let add_def_res t def =
  match def with
  | Lang.Def.Classish Located.{ elem = classish_def; span } -> add_classish t classish_def span
  | Lang.Def.Fn _ -> Ok (t, [])
;;

let of_program Lang.Prog.{ defs } =
  List.fold_left defs ~init:(empty, []) ~f:(fun (t, errs) def ->
    match add_def_res t def with
    | Ok (t, errs') -> t, errs' @ errs
    | Error (err, errs') -> t, (err :: errs') @ errs)
;;
