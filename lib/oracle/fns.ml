open Core
open Reporting

module Err = struct
  type t =
    | Already_declared of
        { name : Name.Fn.t
        ; span_prev : Span.t
        ; span_curr : Span.t
        }
  [@@deriving eq, compare, sexp, show, variants]
end

module Entry = struct
  type t =
    { span : Span.t
    ; ty : Ty.t
    }
  [@@deriving show]
end

type t = Entry.t Name.Fn.Map.t [@@deriving show]

let empty = Name.Fn.Map.empty

let add
  t
  Lang.Fn_def.
    { name = Located.{ elem = name; span = span_name }
    ; lambda
    ; where_constraints
    }
  span
  : (t, Err.t) result
  =
  if Map.mem t name
  then (
    let Entry.{ span = span_prev; _ } = Map.find_exn t name in
    let err = Err.already_declared ~name ~span_prev ~span_curr:span in
    Error err)
  else (
    let Lang.Lambda.{ lambda_sig; _ } = lambda in
    let Lang.Lambda_sig.{ ty_params; params; return } =
      Located.elem lambda_sig
    in
    let prov =
      let span_sig = Span.join span_name @@ Located.span_of lambda_sig in
      Prov.witness span_sig
    in
    (* Build the function type from the declaration *)
    let body =
      let Lang.Fn_param_defs.{ required; optional; variadic } = params in
      let required =
        List.map
          required
          ~f:(fun Located.{ elem = Lang.Fn_param_def.{ ty; _ }; _ } -> ty)
      and optional =
        List.map
          optional
          ~f:(fun (Located.{ elem = Lang.Fn_param_def.{ ty; _ }; _ }, _) -> ty)
      and variadic =
        Option.map
          variadic
          ~f:(fun Located.{ elem = Lang.Fn_param_def.{ ty; _ }; _ } -> ty)
      in
      Ty.fn prov ~required ~optional ~variadic ~return
    in
    (* Merge where constraints with the type parameter definitions
       TODO(mjt) this is buggy and will drop constraints only appearing in
       where constraints
    *)
    let quants =
      let m =
        Name.Ty_param.Map.of_alist_exn
          (List.map where_constraints ~f:(fun Ty.Param.{ name; param_bounds } ->
             Located.elem name, (Located.span_of name, param_bounds)))
      in
      List.map ty_params ~f:(fun Lang.Ty_param_def.{ name; param_bounds; _ } ->
        let param_bounds =
          Option.value_map ~default:param_bounds ~f:(fun (span, where_bounds) ->
            let prov = Prov.witness span in
            Ty.Param_bounds.meet param_bounds where_bounds ~prov)
          @@ Map.find m (Located.elem name)
        in
        Ty.Param.create ~name ~param_bounds ())
    in
    let ty = Ty.forall prov ~body ~quants in
    let entry = Entry.{ span; ty } in
    Ok (Map.add_exn t ~key:name ~data:entry))
;;

let find (t : t) id = Option.map ~f:(fun Entry.{ ty; _ } -> ty) @@ Map.find t id
