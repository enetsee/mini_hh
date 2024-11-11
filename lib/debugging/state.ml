open Core
open Reporting

module Minimal = struct
  type t =
    { tys : (Span.t * Ty.t) list
    ; errs : Typing.Err.t list
    ; warns : Typing.Warn.t list
    ; ty_param_name_source : int
    }
  [@@deriving create]

  let empty = { tys = []; errs = []; warns = []; ty_param_name_source = 0 }

  let pp ppf t =
    Fmt.(
      vbox
      @@ record
           ~sep:cut
           [ field "types" (fun { tys; _ } -> tys) @@ vbox @@ list ~sep:cut @@ pair ~sep:sp Span.pp Ty.pp
           ; field "errors" (fun { errs; _ } -> errs) @@ vbox @@ list ~sep:cut Typing.Err.pp
           ; field "warnings " (fun { warns; _ } -> warns) @@ vbox @@ list ~sep:cut Typing.Warn.pp
           ; field "type parameter name source" (fun { ty_param_name_source; _ } -> ty_param_name_source) int
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
  let names = List.init n ~f:(fun i -> Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + offset)) in
  { t with ty_param_name_source }, names
;;
