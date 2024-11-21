open Core
open Reporting

module Minimal = struct
  type t =
    { tys : (Span.t * Ty.t) list
    ; errs : Typing.Err.t list
    ; warns : Typing.Warn.t list
    ; subtyping : Subtyping.State.t
    ; ty_param_name_source : int
    }
  [@@deriving create]

  let empty =
    { tys = []
    ; errs = []
    ; warns = []
    ; ty_param_name_source = 0
    ; subtyping = Subtyping.State.empty
    }
  ;;

  let pp ppf t =
    Fmt.(
      vbox
      @@ record
           ~sep:cut
           [ field "types" (fun { tys; _ } -> tys)
             @@ vbox
             @@ list ~sep:cut
             @@ pair ~sep:sp Span.pp Ty.pp
           ; field "errors" (fun { errs; _ } -> errs)
             @@ vbox
             @@ list ~sep:cut Typing.Err.pp
           ; field "warnings " (fun { warns; _ } -> warns)
             @@ vbox
             @@ list ~sep:cut Typing.Warn.pp
           ; field
               "type parameter name source"
               (fun { ty_param_name_source; _ } -> ty_param_name_source)
               int
           ])
      ppf
      t
  ;;
end

include Minimal
include Pretty.Make (Minimal)

let add_error t err = { t with errs = err :: t.errs }
let add_warning t warn = { t with warns = warn :: t.warns }
let add_ty_span t ty span = { t with tys = (span, ty) :: t.tys }

let fresh_ty_params t n =
  let { ty_param_name_source; _ } = t in
  let offset = ty_param_name_source in
  let ty_param_name_source = offset + n in
  let names =
    List.init n ~f:(fun i ->
      Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset))
  in
  { t with ty_param_name_source }, names
;;

let add_upper_bound ({ subtyping; _ } as t) ~var ~bound =
  let subtyping = Subtyping.State.add_upper_bound subtyping ~var ~bound in
  { t with subtyping }
;;

let add_lower_bound ({ subtyping; _ } as t) ~var ~bound =
  let subtyping = Subtyping.State.add_lower_bound subtyping ~var ~bound in
  { t with subtyping }
;;

let get_upper_bounds { subtyping; _ } ~var =
  Subtyping.State.get_upper_bounds_exn subtyping ~var
;;

let get_lower_bounds { subtyping; _ } ~var =
  Subtyping.State.get_lower_bounds_exn subtyping ~var
;;

let get_fresh_tyvar ({ subtyping; _ } as t) ~prov =
  let ty, subtyping = Subtyping.State.fresh_tyvar subtyping ~prov in
  ty, { t with subtyping }
;;

let observe_variance ({ subtyping; _ } as t) ~var ~variance =
  let subtyping =
    Subtyping.State.observe_variance_exn subtyping ~var ~variance
  in
  { t with subtyping }
;;
