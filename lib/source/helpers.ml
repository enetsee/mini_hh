open Core
open Reporting
open Common
open Lang

let build_tuple_like elems ~ctor =
  let rec aux elems ~k =
    match elems with
    | `Required elem :: rest ->
      aux rest ~k:(fun ~required ~optional ~variadic ->
        let required = elem :: required in
        k ~required ~optional ~variadic)
    | `Optional elem :: rest ->
      aux rest ~k:(fun ~required ~optional ~variadic ->
        let optional = elem :: optional in
        k ~required ~optional ~variadic)
    | `Variadic elem :: _ -> k ~required:[] ~optional:[] ~variadic:(Some elem)
    | [] -> k ~required:[] ~optional:[] ~variadic:None
  in
  aux elems ~k:ctor
;;

let build_tuple tys =
  build_tuple_like tys ~ctor:(fun ~required ~optional ~variadic ->
    Ty.Tuple.create ~required ~optional ?variadic ())
;;

let build_fn_param_defs param_defs =
  build_tuple_like param_defs ~ctor:(fun ~required ~optional ~variadic ->
    Fn_param_defs.create ~required ~optional ?variadic ())
;;

let build_shape
  (fields :
    [ `Required of Ty.Shape_field_label.t * Ty.t
    | `Optional of Ty.Shape_field_label.t * Ty.t
    | `Variadic of Ty.t
    ]
      list)
  : Ty.Shape.t
  =
  build_tuple_like fields ~ctor:(fun ~required ~optional ~variadic ->
    let required = Ty.Shape_field_label.Map.of_alist_exn required
    and optional = Ty.Shape_field_label.Map.of_alist_exn optional in
    Ty.Shape.create ~required ~optional ?variadic ())
;;

let build_class_kind mods =
  let rec aux mods is_abstract is_final span =
    match mods, is_abstract, is_final, span with
    | `Abstract span :: rest, None, None, None ->
      aux rest (Some span) None (Some span)
    | `Abstract _ :: rest, Some _, None, _ -> aux rest is_abstract is_final span
    | `Abstract _ :: rest, Some _, Some _, _ -> is_abstract, is_final, span
    | `Final span :: rest, None, None, None ->
      aux rest None (Some span) (Some span)
    | `Final _ :: rest, Some _, None, _ -> aux rest is_abstract is_final span
    | `Final _ :: rest, Some _, Some _, _ -> is_abstract, is_final, span
    | [], _, _, _ -> is_abstract, is_final, span
    | _ -> failwith "impossible"
  in
  aux mods None None None
;;

let ty_param_bounds_of_constraints (cstrs : Ty_param_bound_def.t Located.t list)
  =
  let rec aux cstrs ~k =
    match cstrs with
    | [] -> k ([], []) ([], [])
    | Located.{ elem = Ty_param_bound_def.As upper; span } :: rest ->
      aux rest ~k:(fun (lowers, span_lower) (uppers, span_upper) ->
        k (lowers, span_lower) (upper :: uppers, span :: span_upper))
    | Located.{ elem = Ty_param_bound_def.Super lower; span } :: rest ->
      aux rest ~k:(fun (lowers, span_lower) (uppers, span_upper) ->
        k (lower :: lowers, span :: span_lower) (uppers, span_upper))
  in
  aux cstrs ~k:(fun (lowers, span_lowers) (uppers, span_uppers) ->
    let lower = Ty.union ~prov:(Prov.witnesses span_lowers) lowers
    and upper = Ty.inter ~prov:(Prov.witnesses span_uppers) uppers in
    Ty.Param_bounds.create ~lower ~upper ())
;;

let ty_param_bounds_of_where_constraints
  (where_constraints :
    (Name.Ty_param.t Located.t * Ty_param_bound_def.t Located.t) list)
  =
  let rec aux acc = function
    | [] -> Map.to_alist acc
    | (Located.{ elem; span }, bound) :: rest ->
      let acc = Map.add_multi acc ~key:elem ~data:(span, bound) in
      aux acc rest
  in
  List.map ~f:(fun (elem, span_cstrs) ->
    let spans, cstrs = List.unzip span_cstrs in
    let span = List.hd_exn spans in
    let param_bounds = ty_param_bounds_of_constraints cstrs in
    let name = Located.create ~elem ~span () in
    Ty.Param.create ~name ~param_bounds ())
  @@ aux Name.Ty_param.Map.empty where_constraints
;;

let unzip_class_elems elems =
  let rec aux elems ~k =
    match elems with
    | [] -> k ([], [], [], [], [], [])
    | next :: rest ->
      aux rest ~k:(fun (req_exts, req_impls, uses, methods, props, ty_consts) ->
        match next with
        | `Require_extends elem ->
          k @@ (elem :: req_exts, req_impls, uses, methods, props, ty_consts)
        | `Require_implements elem ->
          k @@ (req_exts, elem :: req_impls, uses, methods, props, ty_consts)
        | `Use elem ->
          k @@ (req_exts, req_impls, elem :: uses, methods, props, ty_consts)
        | `Method elem ->
          k @@ (req_exts, req_impls, uses, elem :: methods, props, ty_consts)
        | `Property elem ->
          k @@ (req_exts, req_impls, uses, methods, elem :: props, ty_consts)
        | `Type_constant elem ->
          k @@ (req_exts, req_impls, uses, methods, props, elem :: ty_consts))
  in
  aux elems ~k:(fun x -> x)
;;

let build_call_args
  (args : [ `Normal of Lang.Expr.t | `Unpacked of Lang.Expr.t ] list)
  =
  let rec aux elems args =
    match elems with
    | [] -> List.rev args, None
    | `Unpacked arg :: _ -> List.rev args, Some arg
    | `Normal arg :: rest -> aux rest (arg :: args)
  in
  aux args []
;;
