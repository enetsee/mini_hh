open Core
open Reporting

module rec Node : sig
  type t =
    | Wildcard
    | Base of Common.Base.t
    | Generic of Name.Ty_param.t
    | Tuple of Tuple.t
    | Fn of Fn.t
    | Ctor of Ctor.t
    | Exists of Exists.t
    | Union of Hint.t list
    | Inter of Hint.t list
    | Nonnull
  [@@deriving eq, compare, sexp, show]
end = struct
  type t =
    | Wildcard
    | Base of Common.Base.t
    | Generic of Name.Ty_param.t
    | Tuple of Tuple.t
    | Fn of Fn.t
    | Ctor of Ctor.t
    | Exists of Exists.t
    | Union of Hint.t list
    | Inter of Hint.t list
    | Nonnull
  [@@deriving compare, equal, sexp, variants, show]
end

and Hint : sig
  type t = Node.t Located.t [@@deriving compare, equal, sexp, show]
end = struct
  type t = Node.t Located.t [@@deriving compare, equal, sexp, show]
end

and Fn : sig
  type t =
    { params : Tuple.t
    ; return : Hint.t
    }
  [@@deriving compare, create, equal, create, sexp, show]
end = struct
  type t =
    { params : Tuple.t
    ; return : Hint.t
    }
  [@@deriving compare, create, equal, create, sexp, show]
end

and Tuple : sig
  type t = Tuple_elem.t list [@@deriving compare, equal, sexp, show]
end = struct
  type t = Tuple_elem.t list [@@deriving compare, equal, sexp, show]
end

and Tuple_elem : sig
  type t =
    | Required of Hint.t
    | Optional of Hint.t
    | Variadic of Hint.t
  [@@deriving compare, equal, sexp, variants, show]
end = struct
  type t =
    | Required of Hint.t
    | Optional of Hint.t
    | Variadic of Hint.t
  [@@deriving compare, equal, sexp, variants, show]
end

and Ctor : sig
  type t =
    { name : Name.Ctor.t
    ; args : Hint.t list
    }
  [@@deriving compare, create, equal, sexp, show]
end = struct
  type t =
    { name : Name.Ctor.t
    ; args : Hint.t list
    }
  [@@deriving compare, create, equal, sexp, show]
end

and Exists : sig
  type t =
    { quants : Param.t list
    ; body : Hint.t
    }
  [@@deriving eq, compare, create, sexp, show]
end = struct
  type t =
    { quants : Param.t list
    ; body : Hint.t
    }
  [@@deriving eq, compare, create, sexp, show]
end

and Param : sig
  type t =
    { name : Name.Ty_param.t Located.t
    ; param_bounds : Param_bounds.t
    }
  [@@deriving eq, compare, create, sexp, show]
end = struct
  type t =
    { name : Name.Ty_param.t Located.t
    ; param_bounds : Param_bounds.t
    }
  [@@deriving eq, compare, create, sexp, show]
end

and Param_bounds : sig
  type t =
    { lower : Hint.t option
    ; upper : Hint.t option
    }
  [@@deriving eq, compare, create, sexp, show]
end = struct
  type t =
    { lower : Hint.t option
    ; upper : Hint.t option
    }
  [@@deriving eq, compare, create, sexp, show]
end
