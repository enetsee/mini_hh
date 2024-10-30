(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the "hack" directory of this source tree.
 *
 *)
module type Minimal = sig
  type t

  val pp : Format.formatter -> t -> unit
end

module type Minimal_prec = sig
  type t

  val pp_prec : int -> Format.formatter -> t -> unit
end

module type Minimal1 = sig
  type 'a t

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

module type Minimal1_prec = sig
  type 'a t

  val pp_prec : (int -> Format.formatter -> 'a -> unit) -> int -> Format.formatter -> 'a t -> unit
end

module type S = sig
  type t

  val pp : Format.formatter -> t -> unit
  val pp_prec : int -> Format.formatter -> t -> unit
  val to_string : t -> string
  val show : t -> string
  val print : t -> unit
  val print_err : t -> unit
end

module type S1 = sig
  type 'a t

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
  val pp_prec : (int -> Format.formatter -> 'a -> unit) -> int -> Format.formatter -> 'a t -> unit
  val to_string : 'a t -> pp_a:(Format.formatter -> 'a -> unit) -> string
  val show : (Format.formatter -> 'a -> unit) -> 'a t -> string
  val print : 'a t -> pp_a:(Format.formatter -> 'a -> unit) -> unit
  val print_err : 'a t -> pp_a:(Format.formatter -> 'a -> unit) -> unit
end

module type Pretty = sig
  module type Minimal = Minimal
  module type Minimal_prec = Minimal_prec
  module type Minimal1 = Minimal1
  module type Minimal1_prec = Minimal1_prec
  module type S = S
  module type S1 = S1

  module Make (X : Minimal) : S with type t := X.t
  module Make_prec (X : Minimal_prec) : S with type t := X.t
  module Make1 (X : Minimal1) : S1 with type 'a t := 'a X.t
  module Make1_prec (X : Minimal1_prec) : S1 with type 'a t := 'a X.t
end
