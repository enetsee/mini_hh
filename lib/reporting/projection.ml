open Core

module Variance_dir = struct
  type t =
    | Cov
    | Contrav
  [@@deriving compare, eq, sexp, show, yojson, variants]
end

module Cstr_variance = struct
  type t =
    | Dir of Variance_dir.t
    | Inv of Variance_dir.t
  [@@deriving compare, eq, sexp, show, yojson, variants]
end

module Asymm = struct
  type t =
    | Union
    | Inter
  [@@deriving compare, eq, sexp, show, yojson, variants]
end

module Ctor_kind = struct
  type t = Classish [@@deriving compare, eq, sexp, show, yojson, variants]
end

module Symm = struct
  type t =
    | Nullable
    | Ctor of
        { kind : Ctor_kind.t
        ; name : Name.Ty_param.t
        ; idx : int
        ; cstr_variance : Cstr_variance.t
        }
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
