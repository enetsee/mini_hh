open Core

(* ~~ Base types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module Base : sig
  type t =
    | Bool
    | Int
    | String
    | Null
  [@@deriving compare, eq, sexp, show, variants]
end = struct
  type t =
    | Bool
    | Int
    | String
    | Null
  [@@deriving compare, eq, sexp, show, variants]
end

(* ~~ Types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module rec Minimal : sig
  type t =
    | Base of Base.t (** Base types *)
    | Generic of Generic.t (** Generics *)
    | Fn of Fn.t (** Functions *)
    | Ctor of Ctor.t (** Type constructors *)
    | Exists of Exists.t (* Existentially quantified types *)
    | Union of t list
    | Inter of t list
  [@@deriving compare, equal, sexp, show]

  type 'acc ops =
    { on_base : 'acc -> Base.t -> 'acc
    ; on_generic : 'acc -> Generic.t -> 'acc
    ; on_fn : 'acc -> Fn.t -> 'acc
    ; on_ctor : 'acc -> Ctor.t -> 'acc
    ; on_exists : 'acc -> Exists.t -> 'acc
    ; on_union : 'acc -> t list -> 'acc
    ; on_inter : 'acc -> t list -> 'acc
    }

  val id_ops : unit -> 'a ops
  val bool : t
  val null : t
  val int : t
  val string : t
  val arraykey : t
  val nullable : t -> t
  val generic : Identifier.Ty_param.t -> t
  val fn : required:t list -> optional:t list -> variadic:t -> t -> t
  val ctor : Identifier.Ctor.t -> t list -> t
  val exists : Param.t list -> t -> t
  val mixed : t
  val nothing : t
  val union : t list -> t
  val inter : t list -> t
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Minimal.t Generic.Map.t -> t
  val unpack_opt : t -> (Param_bounds.t Generic.Map.t * t) option
end = struct
  type t =
    | Base of Base.t (** Base types *)
    | Generic of Generic.t (** Generics *)
    | Fn of Fn.t (** Functions *)
    | Ctor of Ctor.t (** Type constructors *)
    | Exists of Exists.t (* Existentially quantified types *)
    | Union of t list
    | Inter of t list
  [@@deriving compare, equal, sexp, show]

  let bool = Base Base.bool
  let null = Base Base.null
  let int = Base Base.int
  let string = Base Base.string
  let generic id = Generic (Generic id)

  let fn ~required ~optional ~variadic return =
    let params = Fn_params.create ~required ~optional ~variadic () in
    Fn (Fn.create ~params ~return ())
  ;;

  let ctor ctor args = Ctor (Ctor.create ~ctor ~args ())
  let exists quants body = Exists (Exists.create ~body ~quants ())
  let nothing = Union []
  let mixed = Inter []

  let union = function
    | [] -> Union []
    | [ t ] -> t
    | ts -> Union ts
  ;;

  let inter = function
    | [] -> Inter []
    | [ t ] -> t
    | ts -> Inter ts
  ;;

  let arraykey = union [ int; string ]
  let nullable t = union [ t; null ]

  let unpack_opt = function
    | Exists Exists.{ body; quants } ->
      let ty_param =
        Generic.Map.of_alist_exn
        @@ List.map quants ~f:(fun Param.{ ident; param_bounds } -> Generic.Generic ident, param_bounds)
      in
      Some (ty_param, body)
    | _ -> None
  ;;

  type 'acc ops =
    { on_base : 'acc -> Base.t -> 'acc
    ; on_generic : 'acc -> Generic.t -> 'acc
    ; on_fn : 'acc -> Fn.t -> 'acc
    ; on_ctor : 'acc -> Ctor.t -> 'acc
    ; on_exists : 'acc -> Exists.t -> 'acc
    ; on_union : 'acc -> t list -> 'acc
    ; on_inter : 'acc -> t list -> 'acc
    }

  let id_ops =
    let ops =
      { on_base = (fun acc _ -> acc)
      ; on_generic = (fun acc _ -> acc)
      ; on_fn = (fun acc _ -> acc)
      ; on_ctor = (fun acc _ -> acc)
      ; on_exists = (fun acc _ -> acc)
      ; on_union = (fun acc _ -> acc)
      ; on_inter = (fun acc _ -> acc)
      }
    in
    fun _ -> ops
  ;;

  let rec apply_subst t ~subst =
    match t with
    | Base _ -> t
    | Generic generic -> Option.value ~default:t @@ Map.find subst generic
    | Fn fn -> Fn (Fn.apply_subst fn ~subst)
    | Ctor ctor -> Ctor (Ctor.apply_subst ctor ~subst)
    | Exists exists -> Exists (Exists.apply_subst exists ~subst)
    | Union union -> Union (List.map ~f:(apply_subst ~subst) union)
    | Inter inter -> Inter (List.map ~f:(apply_subst ~subst) inter)
  ;;

  let rec bottom_up t ~ops ~init =
    let ty_ops = ops.Ops.ty in
    match t with
    | Base base -> ty_ops.on_base init base
    | Generic generic -> ty_ops.on_generic init generic
    | Fn fn ->
      let init = Fn.bottom_up fn ~ops ~init in
      ty_ops.on_fn init fn
    | Ctor ctor ->
      let init = Ctor.bottom_up ctor ~ops ~init in
      ty_ops.on_ctor init ctor
    | Exists exists ->
      let init = Exists.bottom_up exists ~ops ~init in
      ty_ops.on_exists init exists
    | Union ts ->
      let init = List.fold_left ts ~init ~f:(fun init t -> bottom_up t ~ops ~init) in
      ty_ops.on_union init ts
    | Inter ts ->
      let init = List.fold_left ts ~init ~f:(fun init t -> bottom_up t ~ops ~init) in
      ty_ops.on_inter init ts
  ;;
end

(* ~~ Generic types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Generic : sig
  type t = Generic of Identifier.Ty_param.t [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]

  module Map : sig
    include Map.S with type Key.t := t

    val pp : 'a Fmt.t -> 'a t Fmt.t
  end

  module Set : sig
    include Set.S with type Elt.t := t

    val pp : t Fmt.t
    val show : t -> string
  end
end = struct
  module Minimal = struct
    type t = Generic of Identifier.Ty_param.t [@@deriving compare, equal, sexp, show] [@@ocaml.unboxed]
  end

  include Minimal

  module Map = struct
    include Map.Make (Minimal)

    let pp pp_a ppf t = Fmt.(vbox @@ list ~sep:cut @@ pair ~sep:(any " => ") Minimal.pp pp_a) ppf @@ Map.to_alist t
  end

  module Set = struct
    include Set.Make (Minimal)

    let pp ppf t = Fmt.(braces @@ hovbox @@ list ~sep:comma pp) ppf @@ Set.to_list t
    let show t = Fmt.to_to_string pp t
  end
end

(* ~~ Functions types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Fn : sig
  type t =
    { params : Fn_params.t
    ; return : Minimal.t
    }
  [@@deriving compare, equal, create, sexp, show]

  type 'a ops =
    { on_params : 'a -> Fn_params.t -> 'a
    ; on_return : 'a -> Minimal.t -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Minimal.t Generic.Map.t -> t
end = struct
  type t =
    { params : Fn_params.t
    ; return : Minimal.t
    }
  [@@deriving compare, equal, create, sexp, show]

  type 'a ops =
    { on_params : 'a -> Fn_params.t -> 'a
    ; on_return : 'a -> Minimal.t -> 'a
    }

  let id_ops =
    let ops = { on_params = (fun acc _ -> acc); on_return = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let apply_subst { params; return } ~subst =
    let params = Fn_params.apply_subst params ~subst
    and return = Minimal.apply_subst return ~subst in
    { params; return }
  ;;

  let bottom_up { params; return } ~ops ~init =
    let fn_ops = ops.Ops.fn in
    let init = Fn_params.bottom_up ~ops ~init params in
    let init = fn_ops.on_params init params in
    let init = Minimal.bottom_up ~ops ~init return in
    fn_ops.on_return init return
  ;;
end

and Fn_params : sig
  type t =
    { required : Minimal.t list
    ; optional : Minimal.t list
    ; variadic : Minimal.t option
    }
  [@@deriving compare, equal, create, sexp, show]

  type 'a ops =
    { on_required : 'a -> Minimal.t list -> 'a
    ; on_optional : 'a -> Minimal.t list -> 'a
    ; on_variadic : 'a -> Minimal.t option -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Minimal.t Generic.Map.t -> t
end = struct
  type t =
    { required : Minimal.t list
    ; optional : Minimal.t list
    ; variadic : Minimal.t option
    }
  [@@deriving compare, equal, create, sexp, show]

  type 'a ops =
    { on_required : 'a -> Minimal.t list -> 'a
    ; on_optional : 'a -> Minimal.t list -> 'a
    ; on_variadic : 'a -> Minimal.t option -> 'a
    }

  let apply_subst { required; optional; variadic } ~subst =
    let required = List.map required ~f:(Minimal.apply_subst ~subst) in
    let optional = List.map optional ~f:(Minimal.apply_subst ~subst) in
    let variadic = Option.map variadic ~f:(Minimal.apply_subst ~subst) in
    { required; optional; variadic }
  ;;

  let bottom_up { required; optional; variadic } ~ops ~init =
    let fn_params_ops = ops.Ops.fn_params in
    let init = List.fold_left required ~init ~f:(fun init ty -> Minimal.bottom_up ~ops ~init ty) in
    let init = fn_params_ops.on_required init required in
    let init = List.fold_left optional ~init ~f:(fun init ty -> Minimal.bottom_up ~ops ~init ty) in
    let init = fn_params_ops.on_optional init optional in
    let init = Option.fold variadic ~init ~f:(fun init ty -> Minimal.bottom_up ~ops ~init ty) in
    let init = fn_params_ops.on_variadic init variadic in
    init
  ;;

  let id_ops =
    let ops =
      { on_required = (fun acc _ -> acc); on_optional = (fun acc _ -> acc); on_variadic = (fun acc _ -> acc) }
    in
    fun _ -> ops
  ;;
end

(* ~~ Type constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Ctor : sig
  type t =
    { ctor : Identifier.Ctor.t
    ; args : Minimal.t list
    }
  [@@deriving compare, create, equal, sexp, show]

  type 'a ops =
    { on_ctor : 'a -> Identifier.Ctor.t -> 'a
    ; on_args : 'a -> Minimal.t list -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Minimal.t Generic.Map.t -> t
end = struct
  type t =
    { ctor : Identifier.Ctor.t
    ; args : Minimal.t list
    }
  [@@deriving compare, create, equal, sexp, show]

  type 'a ops =
    { on_ctor : 'a -> Identifier.Ctor.t -> 'a
    ; on_args : 'a -> Minimal.t list -> 'a
    }

  let id_ops =
    let ops = { on_ctor = (fun acc _ -> acc); on_args = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let apply_subst { ctor; args } ~subst =
    let args = List.map args ~f:(Minimal.apply_subst ~subst) in
    { ctor; args }
  ;;

  let bottom_up { ctor; args } ~ops ~init =
    let ctor_ops = ops.Ops.ctor in
    let init = ctor_ops.on_ctor init ctor in
    let init = List.fold_left args ~init ~f:(fun init ty -> Minimal.bottom_up ~ops ~init ty) in
    let init = ctor_ops.on_args init args in
    init
  ;;
end

(* ~~ Existentially quantified types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Exists : sig
  type t =
    { quants : Param.t list
    ; body : Minimal.t
    }
  [@@deriving eq, compare, create, sexp, show]

  type 'a ops =
    { on_quants : 'a -> Param.t list -> 'a
    ; on_body : 'a -> Minimal.t -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Minimal.t Generic.Map.t -> t
end = struct
  type t =
    { quants : Param.t list
    ; body : Minimal.t
    }
  [@@deriving eq, compare, create, sexp, show]

  type 'a ops =
    { on_quants : 'a -> Param.t list -> 'a
    ; on_body : 'a -> Minimal.t -> 'a
    }

  let id_ops =
    let ops = { on_quants = (fun acc _ -> acc); on_body = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let apply_subst { quants; body } ~subst =
    let body = Minimal.apply_subst body ~subst
    and quants = List.map quants ~f:(Param.apply_subst ~subst) in
    { body; quants }
  ;;

  let bottom_up { quants; body } ~ops ~init =
    let exists_ops = ops.Ops.exists in
    let init = List.fold_left quants ~init ~f:(fun init param -> Param.bottom_up ~ops ~init param) in
    let init = exists_ops.on_quants init quants in
    let init = Minimal.bottom_up ~ops ~init body in
    let init = exists_ops.on_body init body in
    init
  ;;
end

and Param : sig
  type t =
    { ident : Identifier.Ty_param.t
    ; param_bounds : Param_bounds.t
    }
  [@@deriving eq, compare, sexp, show]

  type 'a ops =
    { on_ident : 'a -> Identifier.Ty_param.t -> 'a
    ; on_param_bounds : 'a -> Param_bounds.t -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Minimal.t Generic.Map.t -> t
end = struct
  type t =
    { ident : Identifier.Ty_param.t
    ; param_bounds : Param_bounds.t
    }
  [@@deriving eq, compare, sexp, show]

  type 'a ops =
    { on_ident : 'a -> Identifier.Ty_param.t -> 'a
    ; on_param_bounds : 'a -> Param_bounds.t -> 'a
    }

  let id_ops =
    let ops = { on_ident = (fun acc _ -> acc); on_param_bounds = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let apply_subst { ident; param_bounds } ~subst =
    let param_bounds = Param_bounds.apply_subst param_bounds ~subst in
    { ident; param_bounds }
  ;;

  let bottom_up { ident; param_bounds } ~ops ~init =
    let param_ops = ops.Ops.param in
    let init = param_ops.on_ident init ident in
    let init = Param_bounds.bottom_up param_bounds ~init ~ops in
    let init = param_ops.on_param_bounds init param_bounds in
    init
  ;;
end

and Param_bounds : sig
  type t =
    { lower_bound : Minimal.t option
    ; upper_bound : Minimal.t option
    }
  [@@deriving eq, compare, create, sexp, show]

  val eq : Minimal.t -> t

  type 'a ops =
    { on_lower_bound : 'a -> Minimal.t option -> 'a
    ; on_upper_bound : 'a -> Minimal.t option -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Minimal.t Generic.Map.t -> t

  (* TODO(mjt) add order sigs *)
  val meet : t -> t -> t
  val meet_many : t list -> t
  val bottom : t
  val join : t -> t -> t
  val join_many : t list -> t
  val top : t
end = struct
  type t =
    { lower_bound : Minimal.t option
    ; upper_bound : Minimal.t option
    }
  [@@deriving eq, compare, create, sexp, show]

  let eq ty = create ~lower_bound:ty ~upper_bound:ty ()

  (** The meet (greatest lower bound) of parameter bounds is the greatest lower bound of the upper bounds  and the
      least upper bound of the lower bounds  i.e.
      `A <: T <: B`  /\  `C <: T <: D`
      is
      `A \/ C <: T <: B /\ D`, or
      `A | C <: T <: B & D` *)
  let meet { lower_bound = lb1; upper_bound = ub1 } { lower_bound = lb2; upper_bound = ub2 } =
    (* If either lower-bound is `None` (nothing) the least upper bound is the other *)
    let lower_bound = Option.merge lb1 lb2 ~f:(fun lb1 lb2 -> Minimal.union [ lb1; lb2 ])
    (* If either upper-bound is `None` (mixed) the greatest lower bound is the other *)
    and upper_bound = Option.merge ub1 ub2 ~f:(fun ub1 ub2 -> Minimal.inter [ ub1; ub2 ]) in
    { lower_bound; upper_bound }
  ;;

  (** The bottom element:  meet bottom _ = meet _ bottom = bottom *)
  let bottom = { lower_bound = Some Minimal.mixed; upper_bound = Some Minimal.nothing }

  (** The join (least upper bound) of parameter bounds is the greatest lower bound of the lower bounds and the
      least upper bound of the upper bounds i.e
      `A <: T <: B`  \/  `C <: T <: D`
      is
      `A & C <: T <: B | D` *)
  let join { lower_bound = lb1; upper_bound = ub1 } { lower_bound = lb2; upper_bound = ub2 } =
    (* If either lower-bound is `None` (nothing) it is the greatest lower bound *)
    let lower_bound = Option.map2 lb1 lb2 ~f:(fun lb1 lb2 -> Minimal.inter [ lb1; lb2 ])
    (* If either upper-bound is `None` (mixed) it is the least upper bound *)
    and upper_bound = Option.map2 ub1 ub2 ~f:(fun ub1 ub2 -> Minimal.union [ ub1; ub2 ]) in
    { lower_bound; upper_bound }
  ;;

  (** The top element: join top _ = join _ top = top *)
  let top = { lower_bound = None; upper_bound = None }

  let meet_many ts = List.fold ts ~init:top ~f:meet
  let join_many ts = List.fold ts ~init:bottom ~f:join

  type 'a ops =
    { on_lower_bound : 'a -> Minimal.t option -> 'a
    ; on_upper_bound : 'a -> Minimal.t option -> 'a
    }

  let id_ops =
    let ops = { on_lower_bound = (fun acc _ -> acc); on_upper_bound = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let bottom_up { lower_bound; upper_bound } ~ops ~init =
    let param_bounds_ops = ops.Ops.param_bounds in
    let init = Option.fold lower_bound ~init ~f:(fun init ty -> Minimal.bottom_up ~ops ~init ty) in
    let init = param_bounds_ops.on_lower_bound init lower_bound in
    let init = Option.fold upper_bound ~init ~f:(fun init ty -> Minimal.bottom_up ty ~ops ~init) in
    let init = param_bounds_ops.on_upper_bound init upper_bound in
    init
  ;;

  let apply_subst { lower_bound; upper_bound } ~subst =
    let lower_bound = Option.map lower_bound ~f:Minimal.(apply_subst ~subst)
    and upper_bound = Option.map upper_bound ~f:Minimal.(apply_subst ~subst) in
    { lower_bound; upper_bound }
  ;;
end

and Ops : sig
  type 'a t =
    { ty : 'a Minimal.ops
    ; fn : 'a Fn.ops
    ; fn_params : 'a Fn_params.ops
    ; ctor : 'a Ctor.ops
    ; exists : 'a Exists.ops
    ; param : 'a Param.ops
    ; param_bounds : 'a Param_bounds.ops
    }

  val id_ops : unit -> 'a t
  val collect_generics : unit -> Generic.Set.t t
end = struct
  type 'a t =
    { ty : 'a Minimal.ops
    ; fn : 'a Fn.ops
    ; fn_params : 'a Fn_params.ops
    ; ctor : 'a Ctor.ops
    ; exists : 'a Exists.ops
    ; param : 'a Param.ops
    ; param_bounds : 'a Param_bounds.ops
    }

  let id_ops _ =
    { ty = Minimal.id_ops ()
    ; fn = Fn.id_ops ()
    ; fn_params = Fn_params.id_ops ()
    ; ctor = Ctor.id_ops ()
    ; exists = Exists.id_ops ()
    ; param = Param.id_ops ()
    ; param_bounds = Param_bounds.id_ops ()
    }
  ;;

  let collect_generics _ : Generic.Set.t t =
    let ty =
      let ops = Minimal.id_ops () in
      Minimal.{ ops with on_generic = (fun acc generic -> Set.add acc generic) }
    in
    let ops = id_ops () in
    { ops with ty }
  ;;
end

include Minimal
module Set = Set.Make (Minimal)
module Refinement = Dnf.Make (Minimal)

let refine t refinement =
  match Refinement.to_list_opt refinement with
  | None -> nothing
  | Some disjs -> union @@ List.map disjs ~f:(fun (poss, _negs) -> inter (t :: poss))
;;
