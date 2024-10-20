(** The possible context available within a given top-level definition:
    - for a function definition, just the function context
    - within a class:

    + the *)
type t =
  | Classish of Classish.t
  | Fn of Fn.t
  | Method of Classish.t * Fn.t
