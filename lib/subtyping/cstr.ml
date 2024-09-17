module Is_subtype = struct
  type t =
    { ty_sub : Ty.t
    ; ty_super : Ty.t
    }
  [@@deriving compare, create, eq, sexp]

  let pp ppf { ty_sub; ty_super } = Fmt.(hovbox @@ pair ~sep:(any " <: ") Ty.pp Ty.pp) ppf (ty_sub, ty_super)
  let show t = Fmt.to_to_string pp t
end

type t = Is_subtype of Is_subtype.t [@@deriving compare, eq, sexp, variants]

let pp ppf = function
  | Is_subtype is_subtype -> Is_subtype.pp ppf is_subtype
;;

let show t = Fmt.to_to_string pp t
let is_subtype ~ty_sub ~ty_super = is_subtype @@ Is_subtype.create ~ty_sub ~ty_super ()
