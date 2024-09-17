open Core

module Ctor = struct
  module Minimal = struct
    type t = Ctor of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
  end

  include Minimal

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf @@ Map.to_alist t
  end
end

module Fn = struct
  type t = Fn of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
end

module Member = struct
  type t = Member of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
end

module Ty_param = struct
  module Minimal = struct
    type t = Ty_param of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
  end

  include Minimal

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf @@ Map.to_alist t
  end
end

module Tm_var = struct
  module Minimal = struct
    type t = Tm_var of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
  end

  include Minimal

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf @@ Map.to_alist t
  end
end
