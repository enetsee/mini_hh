open Core

type t = { defs : Def.t list }
[@@ocaml.unboxed] [@@deriving compare, eq, sexp, show]

let elab_to_generic { defs } =
  let defs =
    List.map
      defs
      ~f:(Def.elab_to_generic ~bound_ty_params:Name.Ty_param.Set.empty)
  in
  { defs }
;;
