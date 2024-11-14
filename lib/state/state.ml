open Core

type t = { ty_param_source : int } [@@deriving create, show]

let fresh_generic { ty_param_source } =
  let nm = Format.sprintf {|T#%n|} ty_param_source in
  let ty_param_source = ty_param_source + 1 in
  { ty_param_source }, Name.Ty_param.of_string nm
;;

let fresh_generics { ty_param_source } n =
  let ty_param_source = ty_param_source + n in
  let ty_params =
    List.init n ~f:(fun i ->
      Name.Ty_param.of_string @@ Format.sprintf {|T#%n|} (i + n))
  in
  { ty_param_source }, ty_params
;;
