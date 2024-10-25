open Reporting

(** A function context gives us
    - the function name (not sure we need it)
    - the return type
    - type parameter and this refinements apply to any enclosing class, interface
      or trait*)
type t =
  { name : Name.Fn.t Located.t
  ; return : Ty.t
  }
[@@deriving create, show]
