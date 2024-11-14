open Core
open Reporting

(* : sig (** A type parameteter context is a map from type paramter names to type parameter bounds *) type t

   val pp : t Fmt.t val empty : t val is_empty : t -> bool val bind : t -> Name.Ty_param.t -> Ty.Param_bounds.t -> t val
   merge_disjoint_exn : t -> t -> t val meet : t -> t -> prov:Reporting.Prov.t -> t val find : t -> Name.Ty_param.t ->
   Ty.Param_bounds.t option val transform : t -> f:(Ty.Param_bounds.t -> Ty.Param_bounds.t) -> t end *)

module Ctxt = struct
  module Minimal = struct
    type t = Ty.Param_bounds.t Name.Ty_param.Map.t
    [@@deriving compare, eq, sexp]

    let pp ppf t = Name.Ty_param.Map.pp Ty.Param_bounds.pp ppf t
  end

  include Minimal
  include Pretty.Make (Minimal)

  let pp t = Name.Ty_param.Map.pp Ty.Param_bounds.pp t
  let empty : t = Name.Ty_param.Map.empty
  let is_empty t = Map.is_empty t
  let bindings t = Map.to_alist t

  let bind (t : t) ty_param bounds : t =
    (* Invariant: we should never rebind a type parameter *)
    Map.add_exn t ~key:ty_param ~data:bounds
  ;;

  let bind_all t ty_params =
    List.fold_left
      ty_params
      ~init:t
      ~f:(fun t Ty.Param.{ name; param_bounds } ->
        bind t (Located.elem name) param_bounds)
  ;;

  let of_alist nm_bounds : t = Name.Ty_param.Map.of_alist_exn nm_bounds

  let extend t ~with_ : t =
    let f ~key:_ = function
      | `Left v | `Right v | `Both (_, v) -> Some v
    in
    Map.merge t with_ ~f
  ;;

  let meet t1 t2 ~prov =
    let f ~key:_ = function
      | `Left bounds | `Right bounds -> Some bounds
      | `Both (bounds_l, bounds_r) ->
        Some (Ty.Param_bounds.meet ~prov bounds_l bounds_r)
    in
    Map.merge t1 t2 ~f
  ;;

  let join t1 t2 ~prov =
    let f ~key:_ = function
      | `Left _bounds | `Right _bounds -> None
      | `Both (bounds_l, bounds_r) ->
        Some (Ty.Param_bounds.join ~prov bounds_l bounds_r)
    in
    Map.merge t1 t2 ~f
  ;;

  let find (t : t) id = Map.find t id
  let transform t ~f = Name.Ty_param.Map.map t ~f
end

module Refinement : sig
  (** Represents the refinement to the bounds of a type parameter occuring in the type parameter context
      Any type parameter which is bound in that context but doesn't explicitly appear in the refinement context
      has an implicit refinement of [nothing] and [mixed] i.e. [top] for type parameter bounds *)
  type t [@@deriving compare, eq, sexp, show]

  val top : t

  (** Same as top *)
  val empty : t

  val bottom : t
  val singleton : Name.Ty_param.t -> Ty.Param_bounds.t -> t
  val bounds : (Name.Ty_param.t * Ty.Param_bounds.t) list -> t
  val transform : t -> f:(Ty.Param_bounds.t -> Ty.Param_bounds.t) -> t
  val meet : t -> t -> prov:Prov.t -> t
  val meet_many : t list -> prov:Prov.t -> t
  val join : t -> t -> prov:Prov.t -> t
  val join_many : t list -> prov:Prov.t -> t
  val unbind : t -> Name.Ty_param.t -> t
  val unbind_all : t -> Name.Ty_param.t list -> t

  val bindings
    :  t
    -> [> `Bottom
       | `Bounds of (Name.Ty_param.t * Ty.Param_bounds.t) list
       | `Top
       ]

  type result =
    | Bounds_top
    | Bounds_bottom
    | Bounds of Ty.Param_bounds.t

  val find : t -> Name.Ty_param.t -> result
end = struct
  module Minimal = struct
    type t =
      | Top
      (** The top element:
          meet top t = meet t top = t
          join top _ = join _ top = top *)
      | Bounds of Ty.Param_bounds.t Name.Ty_param.Map.t
      | Bottom
      (** The bottom element:
          meet bottom _ = meet _ bottom = bottom
          join bottom t = join t bottom = t *)
    [@@deriving compare, eq, sexp]

    let pp ppf t =
      match t with
      | Top -> Fmt.(any "⊤") ppf ()
      | Bottom -> Fmt.(any "⊥") ppf ()
      | Bounds b -> Name.Ty_param.Map.pp Ty.Param_bounds.pp ppf b
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let top = Top
  let bottom = Bottom
  let bounds ty_params = Bounds (Name.Ty_param.Map.of_alist_exn ty_params)

  let singleton generic param_bounds =
    Bounds (Name.Ty_param.Map.singleton generic param_bounds)
  ;;

  let pp ppf = function
    | Top -> Fmt.any "T" ppf ()
    | Bottom -> Fmt.any "F" ppf ()
    | Bounds b -> Name.Ty_param.Map.pp Ty.Param_bounds.pp ppf b
  ;;

  let bindings t =
    match t with
    | Top -> `Top
    | Bottom -> `Bottom
    | Bounds b -> `Bounds (Map.to_alist b)
  ;;

  let show = Fmt.to_to_string pp
  let empty = top

  let transform t ~f =
    match t with
    | Top -> Top
    | Bottom -> Bottom
    | Bounds m -> Bounds (Name.Ty_param.Map.map m ~f)
  ;;

  (** meet / greatest lower bound / intersection *)
  let meet t1 t2 ~prov =
    match t1, t2 with
    | Top, t | t, Top -> t
    | Bottom, _ | _, Bottom -> Bottom
    | Bounds b1, Bounds b2 ->
      let f ~key:_ = function
        | `Left bounds | `Right bounds ->
          (* If the bounds are missing in the left (resp. right) refinement then they are implicitly top so the meet is
             the bounds in the right (resp. left) refinement *)
          Some bounds
        | `Both (bounds_l, bounds_r) ->
          Some (Ty.Param_bounds.meet bounds_l bounds_r ~prov)
      in
      Bounds (Map.merge b1 b2 ~f)
  ;;

  let meet_many ts ~prov =
    match ts with
    | [ t ] -> t
    | _ -> List.fold_left ts ~init:top ~f:(meet ~prov)
  ;;

  (** join / least upper bound  / union *)
  let join t1 t2 ~prov =
    match t1, t2 with
    | Top, _ | _, Top -> Top
    | Bottom, t | t, Bottom -> t
    | Bounds b1, Bounds b2 ->
      let f ~key:_ = function
        | `Left _ | `Right _ ->
          (* If the bounds are missing in the left (resp. right) refinement they are implicitly top so the join so the
             union is also top which is encoded as [None] *)
          None
        | `Both (bounds_l, bounds_r) ->
          Some (Ty.Param_bounds.join bounds_l bounds_r ~prov)
      in
      Bounds (Map.merge b1 b2 ~f)
  ;;

  let join_many ts ~prov = List.fold_left ts ~init:bottom ~f:(join ~prov)

  type result =
    | Bounds_top
    | Bounds_bottom
    | Bounds of Ty.Param_bounds.t

  let find t name =
    match t with
    | Top -> Bounds_top
    | Bottom -> Bounds_bottom
    | Bounds m ->
      Option.value_map ~f:(fun b -> Bounds b) ~default:Bounds_top
      @@ Map.find m name
  ;;

  let unbind t generic =
    match t with
    | Top | Bottom -> t
    | Bounds bounds -> Bounds (Map.remove bounds generic)
  ;;

  let unbind_all t generics =
    match List.fold_left generics ~init:t ~f:unbind with
    | Bounds bounds when Map.is_empty bounds -> Top
    | t -> t
  ;;
end

include Ctxt
