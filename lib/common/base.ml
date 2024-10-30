module Minimal = struct
  type t =
    | Bool
    | Int
    | Float
    | String
    | Null
  [@@deriving compare, eq, sexp, variants]

  let pp ppf t =
    match t with
    | Bool -> Fmt.any "bool" ppf t
    | Int -> Fmt.any "int" ppf t
    | Float -> Fmt.any "float" ppf t
    | String -> Fmt.any "string" ppf t
    | Null -> Fmt.any "null" ppf t
  ;;
end

include Minimal
include Pretty.Make (Minimal)
