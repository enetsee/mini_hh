open Common
open Reporting

type _ Effect.t +=
  | Fresh_ty_params : int -> Name.Ty_param.t list Effect.t (** Get n globally fresh type parameter names *)
  | Up :
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      }
      -> Ty.t list option Effect.t
      (** Get the instantation of the constructor type [of_] at a superclass given by the constructor [at]. This will be
          [None] if [of_] does not extend or implement [at] *)
  | Down :
      { of_ : Ty.Ctor.t
      ; at : Name.Ctor.t
      }
      -> Ty.t list option Effect.t
      (** Get the instantation of the constructor type [of_] at a subclass given by the constructor [at]. This will be
          [None] if [at] does not extend or implement [of_] *)
  | Ty_param_variances : Name.Ctor.t -> Variance.t Located.t list option Effect.t
      (** Get the declared variances for the type parameters of a constructor name. The will be [None] is the
          constructor is not bound*)

let fresh_ty_params n = Effect.perform (Fresh_ty_params n)
let up ~of_ ~at = Effect.perform (Up { of_; at })
let down ~of_ ~at = Effect.perform (Down { of_; at })
let ty_param_variances_opt ctor = Effect.perform (Ty_param_variances ctor)
