open Core

module Ctor = struct
  module Minimal = struct
    type t = Ctor of string
    [@@deriving compare, equal, sexp, yojson] [@@ocaml.unboxed]

    let pp ppf (Ctor name) = Fmt.(string) ppf name
  end

  include Minimal
  include Pretty.Make (Minimal)

  let of_string nm = Ctor nm
  let to_string (Ctor nm) = nm

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t =
      Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf
      @@ Map.to_alist t
    ;;
  end
end

module Fn = struct
  module Minimal = struct
    type t = Fn of string
    [@@deriving compare, equal, sexp, show, yojson] [@@ocaml.unboxed]

    let pp ppf (Fn name) = Fmt.string ppf name
  end

  include Minimal
  include Pretty.Make (Minimal)

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t =
      Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf
      @@ Map.to_alist t
    ;;
  end

  let of_string nm = Fn nm
end

module Member = struct
  type t = Member of string
  [@@deriving compare, equal, sexp, show, yojson] [@@ocaml.unboxed]

  let of_string nm = Member nm
end

module Ty_param = struct
  module Minimal = struct
    type t =
      | This
      | Ty_param of string
    [@@deriving compare, equal, sexp, yojson]

    let from_ctor_name ctor_name =
      let nm = Ctor.to_string ctor_name in
      if String.equal nm "this" then This else Ty_param nm
    ;;

    let pp ppf t =
      match t with
      | Ty_param name -> Fmt.(string) ppf name
      | This -> Fmt.any "this" ppf ()
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let of_string nm = Ty_param nm
  let this = This

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t =
      Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf
      @@ Map.to_alist t
    ;;
  end

  module Set = struct
    include Set.Make (Minimal)

    let pp ppf t =
      Fmt.(hovbox @@ braces @@ list ~sep:comma Minimal.pp) ppf @@ Set.elements t
    ;;
  end
end

module Tm_var = struct
  module Minimal = struct
    type t = Tm_var of string
    [@@deriving compare, equal, sexp, show, yojson] [@@ocaml.unboxed]

    let pp ppf (Tm_var name) = Fmt.string ppf name
  end

  include Minimal
  include Pretty.Make (Minimal)

  let of_string nm = Tm_var nm

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t =
      Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") pp pp_a) ppf
      @@ Map.to_alist t
    ;;
  end

  module Set = struct
    include Set.Make (Minimal)

    let pp ppf t = Fmt.(hovbox @@ braces @@ list ~sep:comma pp) ppf t
  end
end

module Shape_field_label = struct
  module Minimal = struct
    type t = Label of string
    [@@deriving compare, equal, sexp, show, yojson] [@@ocaml.unboxed]

    let pp ppf (Label name) = Fmt.string ppf name
  end

  include Minimal
  include Pretty.Make (Minimal)

  let of_string nm = Label nm
end
