module Variance_dir = struct
  type t =
    | Cov
    | Contrav
  [@@deriving compare, eq, sexp, show, yojson, variants]
end

module Asymm = struct
  type t =
    | Union
    | Inter
  [@@deriving compare, eq, sexp, show, yojson, variants]
end

module Symm = struct
  type t = Nullable [@@deriving compare, eq, sexp, show, yojson, variants]
end
