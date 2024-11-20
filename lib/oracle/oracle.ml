open Core
module Classish = Classish
module Fns = Fns
open Reporting

module Err = struct
  type t =
    | Classish of Classish.Err.t
    | Fns of Fns.Err.t
end

type t =
  { classish : Classish.t
  ; fns : Fns.t
  }
[@@deriving show]

let empty = { classish = Classish.empty; fns = Fns.empty }
let up { classish; _ } ~of_ ~at = Classish.up classish ~of_ ~at

let param_bounds_opt { classish; _ } ~ctor =
  Classish.param_bounds_opt classish ~ctor
;;

let param_variances_opt { classish; _ } ~ctor =
  Classish.param_variances_opt classish ctor
;;

let find_ctor { classish; _ } id = Classish.find classish id

let add_classish ({ classish; _ } as t) classish_def span =
  Result.map ~f:(fun (classish, errs) -> { t with classish }, errs)
  @@ Classish.add classish classish_def span
;;

let find_fn { fns; _ } id = Fns.find fns id

let add_fn ({ fns; _ } as t) fn_def span =
  Result.map ~f:(fun fns -> { t with fns }) @@ Fns.add fns fn_def span
;;

(* let add_def_res t def =
  match def with
  | Lang.Def.Classish Located.{ elem = classish_def; span } ->
    add_classish t classish_def span
  | Lang.Def.Fn Located.{elem = fn_def;span} -> 
  | Lang.Def.Ty _ -> Ok (t, [])
;; *)

let of_program Lang.Prog.{ defs } =
  List.fold_left defs ~init:(empty, []) ~f:(fun (t, errs) def ->
    match def with
    | Lang.Def.Classish Located.{ elem = classish_def; span } ->
      (match add_classish t classish_def span with
       | Ok (t, errs') ->
         t, List.map ~f:(fun err -> Err.Classish err) errs' @ errs
       | Error (err, errs') ->
         t, List.map ~f:(fun err -> Err.Classish err) (err :: errs') @ errs)
    | Lang.Def.Fn Located.{ elem = fn_def; span } ->
      (match add_fn t fn_def span with
       | Ok t -> t, errs
       | Error err -> t, Err.(Fns err) :: errs)
    | Lang.Def.Ty _ -> t, errs)
;;
