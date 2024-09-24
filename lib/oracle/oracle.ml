module Classish = Classish

type t = { classish : Classish.t } [@@deriving show]

let empty = { classish = Classish.empty }
let up { classish } ~of_ ~at = Classish.up classish ~of_ ~at
let down { classish } ~of_ ~at = Classish.down classish ~of_ ~at
let param_bounds_opt { classish } ~ctor = Classish.param_bounds_opt classish ~ctor
let param_variances_opt { classish } ~ctor = Classish.param_variances_opt classish ctor
let find_ctor { classish } id = Classish.find classish id

let add_classish_exn { classish } ~id ~ty_params ~supers =
  let classish = Classish.add_exn classish ~id ~ty_params ~supers in
  { classish }
;;

let add_classishes_exn { classish } ls =
  let classish = Classish.add_all_exn classish ls in
  { classish }
;;

(* module Example = struct
  let oracle = { classish = Classish.Example.data }
end *)
