open Core
module Classish = Classish

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
