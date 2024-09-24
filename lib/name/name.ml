open Core

module Ctor = struct
  module Minimal = struct
    type t = Ctor of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
  end

  include Minimal

  let of_string nm = Ctor nm

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf @@ Map.to_alist t
  end
end

module Fn = struct
  type t = Fn of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]

  let of_string nm = Fn nm
end

module Member = struct
  type t = Member of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]

  let of_string nm = Member nm
end

module Ty_param = struct
  module Minimal = struct
    type t = Ty_param of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
  end

  include Minimal

  let of_string nm = Ty_param nm

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf @@ Map.to_alist t
  end

  module Set = struct
    include Set.Make (Minimal)

    let pp ppf t = Fmt.(hovbox @@ braces @@ list ~sep:comma Minimal.pp) ppf @@ Set.elements t
  end
end

module Tm_var = struct
  module Minimal = struct
    type t = Tm_var of string [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
  end

  include Minimal

  let of_string nm = Tm_var nm

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf @@ Map.to_alist t
  end
end
