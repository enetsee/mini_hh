open Reporting

type t =
  { name : Name.Ctor.t Located.t (** The name of the enclosing class, interface or trait. *)
  (** The declared bounds for [this]:

      For a class, the upper-bound of [this] is just the enclosing class since we will use subsumption for everything
      else. If the class is declared [final] then it will also be the lower bound.

      For a trait, the intersection of the trait and
      - upper-bounds from all [require extends] and [require implements] declarations
      - upper and lower-bounds from any [require class] declaration

      For an interface, the intersection of the enclosing interface and upper-bounds from any [require extends]
      declarations *)
  }
[@@deriving create, show]
