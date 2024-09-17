module Err : sig
  type t =
    | Unbound_ctor of Identifier.Ctor.t
    | Invariant_param of Identifier.Ctor.t * Ty.Generic.t
  [@@deriving compare, equal, sexp, show, variants]

  module Set : Core.Set.S with type Elt.t := t
end

exception Exposure of Err.t list

(** Promote a type [ty] by finding its least supertype not containing any type parameter mentioned in [ty_params] *)
val promote : Ty.t -> Envir.Ty_param.t -> oracle:Oracle.t -> (Ty.t, Err.Set.t) result

(** Promote a type [ty] by finding its least supertype not containing any type parameter mentioned in [ty_params].
    Raises a [Exposure] exception if a type parameter is unbound in the provided environment *)
val promote_exn : Ty.t -> Envir.Ty_param.t -> oracle:Oracle.t -> Ty.t

(** Demote a type [ty] by finding its greatest subtype not containing any type parameter mentioned in [ty_params] *)
val demote : Ty.t -> Envir.Ty_param.t -> oracle:Oracle.t -> (Ty.t, Err.Set.t) result

(** Demote a type [ty] by finding its greatest subtype not containing any type parameter mentioned in [ty_params]
    Raises a [Exposure] exception if a type parameter is unbound in the provided environment *)
val demote_exn : Ty.t -> Envir.Ty_param.t -> oracle:Oracle.t -> Ty.t
