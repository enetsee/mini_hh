open Core

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
  type t =
    | Nullable
    | Tuple of
        { idx_sub : int
        ; idx_super : int
        }
    | Fn_arg of
        { idx_sub : int
        ; idx_super : int
        }
    | Fn_ret
  [@@deriving compare, eq, sexp, show, yojson, variants]
end
