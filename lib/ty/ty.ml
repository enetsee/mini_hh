open Core
open Reporting

(* ~~ Base types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module Base : sig
  type t =
    | Bool
    | Int
    | Float
    | String
    | Null
  [@@deriving compare, eq, sexp, show, variants]
end = struct
  type t =
    | Bool
    | Int
    | Float
    | String
    | Null
  [@@deriving compare, eq, sexp, show, variants]
end

(* ~~ Types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module rec Node : sig
  type t =
    | Base of Base.t (** Base types *)
    | Generic of Name.Ty_param.t (** Generics *)
    | Tuple of Tuple.t
    | Fn of Fn.t (** Functions *)
    | Ctor of Ctor.t (** Type constructors *)
    | Exists of Exists.t (* Existentially quantified types *)
    | Union of Annot.t list
    | Inter of Annot.t list
  [@@deriving compare, equal, sexp, show, variants]
end = struct
  type t =
    | Base of Base.t (** Base types *)
    | Generic of Name.Ty_param.t (** Generics *)
    | Tuple of Tuple.t (** Tuples *)
    | Fn of Fn.t (** Functions *)
    | Ctor of Ctor.t (** Type constructors *)
    | Exists of Exists.t (* Existentially quantified types *)
    | Union of Annot.t list
    | Inter of Annot.t list
  [@@deriving compare, equal, sexp, show, variants]
end

and Annot : sig
  type t =
    { prov : Prov.t
    ; node : Node.t
    }
  [@@deriving compare, create, equal, sexp, show]

  val prj : t -> Prov.t * Node.t

  type 'acc ops =
    { on_base : 'acc -> Prov.t -> Base.t -> 'acc
    ; on_generic : 'acc -> Prov.t -> Name.Ty_param.t -> 'acc
    ; on_fn : 'acc -> Prov.t -> Fn.t -> 'acc
    ; on_tuple : 'acc -> Prov.t -> Tuple.t -> 'acc
    ; on_ctor : 'acc -> Prov.t -> Ctor.t -> 'acc
    ; on_exists : 'acc -> Prov.t -> Exists.t -> 'acc
    ; on_union : 'acc -> Prov.t -> t list -> 'acc
    ; on_inter : 'acc -> Prov.t -> t list -> 'acc
    }

  val bottom_up : t -> ops:'acc Ops.t -> init:'acc -> 'acc
  val id_ops : unit -> 'acc ops
  val map_prov : t -> f:(Prov.t -> Prov.t) -> t
  val with_prov : t -> Prov.t -> t
  val apply_subst : t -> subst:Annot.t Name.Ty_param.Map.t -> combine_prov:(Prov.t -> Prov.t -> Prov.t) -> t
  val bool : Prov.t -> t
  val null : Prov.t -> t
  val int : Prov.t -> t
  val float : Prov.t -> t
  val string : Prov.t -> t
  val generic : Prov.t -> Name.Ty_param.t -> t
  val tuple : Prov.t -> required:t list -> optional:t list -> variadic:t option -> t
  val fn : Prov.t -> required:t list -> optional:t list -> variadic:t option -> return:t -> t
  val ctor : Prov.t -> name:Name.Ctor.t -> args:t list -> t
  val exists : Prov.t -> quants:Param.t list -> body:t -> t
  val union : t list -> prov:Prov.t -> t
  val inter : t list -> prov:Prov.t -> t
  val arraykey : Prov.t -> t
  val nullable : Prov.t -> t -> t
  val num : Prov.t -> t
  val mixed : Prov.t -> t
  val nothing : Prov.t -> t
end = struct
  type t =
    { prov : Prov.t
    ; node : Node.t
    }
  [@@deriving compare, create, equal, sexp, show]

  let prj { prov; node } = prov, node
  (* ~~ Traversals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  type 'acc ops =
    { on_base : 'acc -> Prov.t -> Base.t -> 'acc
    ; on_generic : 'acc -> Prov.t -> Name.Ty_param.t -> 'acc
    ; on_fn : 'acc -> Prov.t -> Fn.t -> 'acc
    ; on_tuple : 'acc -> Prov.t -> Tuple.t -> 'acc
    ; on_ctor : 'acc -> Prov.t -> Ctor.t -> 'acc
    ; on_exists : 'acc -> Prov.t -> Exists.t -> 'acc
    ; on_union : 'acc -> Prov.t -> t list -> 'acc
    ; on_inter : 'acc -> Prov.t -> t list -> 'acc
    }

  let id_ops =
    let ops =
      { on_base = (fun acc _ _ -> acc)
      ; on_generic = (fun acc _ _ -> acc)
      ; on_fn = (fun acc _ _ -> acc)
      ; on_tuple = (fun acc _ _ -> acc)
      ; on_ctor = (fun acc _ _ -> acc)
      ; on_exists = (fun acc _ _ -> acc)
      ; on_union = (fun acc _ _ -> acc)
      ; on_inter = (fun acc _ _ -> acc)
      }
    in
    fun _ -> ops
  ;;

  let rec bottom_up { prov; node } ~ops ~init =
    let ty_ops = ops.Ops.ty in
    match node with
    | Base base -> ty_ops.on_base init prov base
    | Generic generic -> ty_ops.on_generic init prov generic
    | Fn fn ->
      let init = Fn.bottom_up fn ~ops ~init in
      ty_ops.on_fn init prov fn
    | Ctor ctor ->
      let init = Ctor.bottom_up ctor ~ops ~init in
      ty_ops.on_ctor init prov ctor
    | Tuple tuple ->
      let init = Tuple.bottom_up tuple ~ops ~init in
      ty_ops.on_tuple init prov tuple
    | Exists exists ->
      let init = Exists.bottom_up exists ~ops ~init in
      ty_ops.on_exists init prov exists
    | Union ts ->
      let init = List.fold_left ts ~init ~f:(fun init t -> bottom_up t ~ops ~init) in
      ty_ops.on_union init prov ts
    | Inter ts ->
      let init = List.fold_left ts ~init ~f:(fun init t -> bottom_up t ~ops ~init) in
      ty_ops.on_inter init prov ts
  ;;

  (* ~~ Modify provenance ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  let map_prov { prov; node } ~f = { node; prov = f prov }
  let with_prov t prov = map_prov ~f:(fun _ -> prov) t

  (* ~~ Generic substitution ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  let rec apply_subst ({ prov; node } as t) ~subst ~combine_prov =
    match node with
    | Base _ -> t
    | Generic name ->
      (match Map.find subst name with
       | Some t -> map_prov t ~f:(combine_prov prov)
       | _ -> t)
    | Fn fn ->
      let node = Node.fn (Fn.apply_subst fn ~subst ~combine_prov) in
      { prov; node }
    | Tuple tuple ->
      let node = Node.tuple (Tuple.apply_subst tuple ~subst ~combine_prov) in
      { prov; node }
    | Ctor ctor ->
      let node = Node.ctor (Ctor.apply_subst ctor ~subst ~combine_prov) in
      { prov; node }
    | Exists exists ->
      let node = Node.exists (Exists.apply_subst exists ~subst ~combine_prov) in
      { prov; node }
    | Union union ->
      let node = Node.union (List.map ~f:(apply_subst ~subst ~combine_prov) union) in
      { prov; node }
    | Inter inter ->
      let node = Node.inter (List.map ~f:(apply_subst ~subst ~combine_prov) inter) in
      { prov; node }
  ;;

  (* ~~ Constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  let base prov base = create ~prov ~node:base ()
  let bool prov = base prov @@ Node.base Base.bool
  let null prov = base prov @@ Node.base Base.null
  let int prov = base prov @@ Node.base Base.int
  let float prov = base prov @@ Node.base Base.float
  let string prov = base prov @@ Node.base Base.string
  let generic prov name = create ~prov ~node:(Node.generic name) ()

  let tuple prov ~required ~optional ~variadic =
    let node = Node.tuple @@ Tuple.create ~required ~optional ?variadic () in
    create ~prov ~node ()
  ;;

  let fn prov ~required ~optional ~variadic ~return =
    let params = Tuple.create ~required ~optional ?variadic () in
    let node = Node.fn @@ Fn.create ~params ~return () in
    create ~prov ~node ()
  ;;

  let ctor prov ~name ~args =
    let node = Node.ctor @@ Ctor.create ~name ~args () in
    create ~prov ~node ()
  ;;

  let exists prov ~quants ~body =
    let node = Node.exists @@ Exists.create ~quants ~body () in
    create ~prov ~node ()
  ;;

  let union elems ~prov =
    match elems with
    | [ ty ] -> ty
    | _ ->
      let node = Node.union elems in
      create ~prov ~node ()
  ;;

  let inter elems ~prov =
    match elems with
    | [ ty ] -> ty
    | _ ->
      let node = Node.inter elems in
      create ~prov ~node ()
  ;;

  let arraykey prov = union ~prov [ int prov; string prov ]
  let num prov = union ~prov [ int prov; float prov ]
  let nullable prov t = union ~prov [ t; null prov ]
  let nothing prov = union ~prov []
  let mixed prov = inter ~prov []
end

(* ~~ Functions types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Fn : sig
  type t =
    { params : Tuple.t
    ; return : Annot.t
    }
  [@@deriving compare, create, equal, create, sexp, show]

  type 'a ops =
    { on_params : 'a -> Tuple.t -> 'a
    ; on_return : 'a -> Annot.t -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Annot.t Name.Ty_param.Map.t -> combine_prov:(Prov.t -> Prov.t -> Prov.t) -> t
end = struct
  type t =
    { params : Tuple.t
    ; return : Annot.t
    }
  [@@deriving compare, create, equal, create, sexp, show]

  let apply_subst { params; return } ~subst ~combine_prov =
    let params = Tuple.apply_subst params ~subst ~combine_prov
    and return = Annot.apply_subst return ~subst ~combine_prov in
    { params; return }
  ;;

  type 'a ops =
    { on_params : 'a -> Tuple.t -> 'a
    ; on_return : 'a -> Annot.t -> 'a
    }

  let id_ops =
    let ops = { on_params = (fun acc _ -> acc); on_return = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let bottom_up { params; return } ~ops ~init =
    let fn_ops = ops.Ops.fn in
    let init = Tuple.bottom_up ~ops ~init params in
    let init = fn_ops.on_params init params in
    let init = Annot.bottom_up ~ops ~init return in
    fn_ops.on_return init return
  ;;
end

and Tuple : sig
  type t =
    { required : Annot.t list
    ; optional : Annot.t list
    ; variadic : Annot.t option
    }
  [@@deriving compare, create, equal, create, map, sexp, show]

  type 'acc ops =
    { on_required : 'acc -> Annot.t list -> 'acc
    ; on_optional : 'acc -> Annot.t list -> 'acc
    ; on_variadic : 'acc -> Annot.t option -> 'acc
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'acc Ops.t -> init:'acc -> 'acc
  val apply_subst : t -> subst:Annot.t Name.Ty_param.Map.t -> combine_prov:(Prov.t -> Prov.t -> Prov.t) -> t
end = struct
  type t =
    { required : Annot.t list
    ; optional : Annot.t list
    ; variadic : Annot.t option
    }
  [@@deriving compare, create, equal, create, map, sexp, show]

  type 'acc ops =
    { on_required : 'acc -> Annot.t list -> 'acc
    ; on_optional : 'acc -> Annot.t list -> 'acc
    ; on_variadic : 'acc -> Annot.t option -> 'acc
    }

  let bottom_up { required; optional; variadic } ~ops ~init =
    let tuple_ops = ops.Ops.tuple in
    let init = List.fold_left required ~init ~f:(fun init ty -> Annot.bottom_up ~ops ~init ty) in
    let init = tuple_ops.on_required init required in
    let init = List.fold_left optional ~init ~f:(fun init ty -> Annot.bottom_up ~ops ~init ty) in
    let init = tuple_ops.on_optional init optional in
    let init = Option.fold variadic ~init ~f:(fun init ty -> Annot.bottom_up ~ops ~init ty) in
    let init = tuple_ops.on_variadic init variadic in
    init
  ;;

  let id_ops =
    let ops =
      { on_required = (fun acc _ -> acc); on_optional = (fun acc _ -> acc); on_variadic = (fun acc _ -> acc) }
    in
    fun _ -> ops
  ;;

  let apply_subst { required; optional; variadic } ~subst ~combine_prov =
    let required = List.map required ~f:(Annot.apply_subst ~subst ~combine_prov) in
    let optional = List.map optional ~f:(Annot.apply_subst ~subst ~combine_prov) in
    let variadic = Option.map variadic ~f:(Annot.apply_subst ~subst ~combine_prov) in
    { required; optional; variadic }
  ;;
end

(* ~~ Type constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Ctor : sig
  type t =
    { name : Name.Ctor.t
    ; args : Annot.t list
    }
  [@@deriving compare, create, equal, sexp, show]

  type 'a ops =
    { on_name : 'a -> Name.Ctor.t -> 'a
    ; on_args : 'a -> Annot.t list -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Annot.t Name.Ty_param.Map.t -> combine_prov:(Prov.t -> Prov.t -> Prov.t) -> t
end = struct
  type t =
    { name : Name.Ctor.t
    ; args : Annot.t list
    }
  [@@deriving compare, create, equal, sexp, show]

  type 'a ops =
    { on_name : 'a -> Name.Ctor.t -> 'a
    ; on_args : 'a -> Annot.t list -> 'a
    }

  let id_ops =
    let ops = { on_name = (fun acc _ -> acc); on_args = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let bottom_up { name; args } ~ops ~init =
    let ctor_ops = ops.Ops.ctor in
    let init = ctor_ops.on_name init name in
    let init = List.fold_left args ~init ~f:(fun init ty -> Annot.bottom_up ~ops ~init ty) in
    let init = ctor_ops.on_args init args in
    init
  ;;

  let apply_subst { name; args } ~subst ~combine_prov =
    let args = List.map args ~f:(Annot.apply_subst ~subst ~combine_prov) in
    { name; args }
  ;;
end

(* ~~ Existentially quantified types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Exists : sig
  type t =
    { quants : Param.t list
    ; body : Annot.t
    }
  [@@deriving eq, compare, create, sexp, show]

  type 'a ops =
    { on_quants : 'a -> Param.t list -> 'a
    ; on_body : 'a -> Annot.t -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Annot.t Name.Ty_param.Map.t -> combine_prov:(Prov.t -> Prov.t -> Prov.t) -> t
end = struct
  type t =
    { quants : Param.t list
    ; body : Annot.t
    }
  [@@deriving eq, compare, create, sexp, show]

  type 'a ops =
    { on_quants : 'a -> Param.t list -> 'a
    ; on_body : 'a -> Annot.t -> 'a
    }

  let id_ops =
    let ops = { on_quants = (fun acc _ -> acc); on_body = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let bottom_up { quants; body } ~ops ~init =
    let exists_ops = ops.Ops.exists in
    let init = List.fold_left quants ~init ~f:(fun init param -> Param.bottom_up ~ops ~init param) in
    let init = exists_ops.on_quants init quants in
    let init = Annot.bottom_up ~ops ~init body in
    let init = exists_ops.on_body init body in
    init
  ;;

  let apply_subst { quants; body } ~subst ~combine_prov =
    let body = Annot.apply_subst body ~subst ~combine_prov
    and quants = List.map quants ~f:(Param.apply_subst ~subst ~combine_prov) in
    { body; quants }
  ;;
end

and Param : sig
  type t =
    { name : Name.Ty_param.t
    ; param_bounds : Param_bounds.t
    }
  [@@deriving eq, compare, create, sexp, show]

  type 'a ops =
    { on_name : 'a -> Name.Ty_param.t -> 'a
    ; on_param_bounds : 'a -> Param_bounds.t -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Annot.t Name.Ty_param.Map.t -> combine_prov:(Prov.t -> Prov.t -> Prov.t) -> t
end = struct
  type t =
    { name : Name.Ty_param.t
    ; param_bounds : Param_bounds.t
    }
  [@@deriving eq, compare, create, sexp, show]

  type 'a ops =
    { on_name : 'a -> Name.Ty_param.t -> 'a
    ; on_param_bounds : 'a -> Param_bounds.t -> 'a
    }

  let id_ops =
    let ops = { on_name = (fun acc _ -> acc); on_param_bounds = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let bottom_up { name; param_bounds } ~ops ~init =
    let param_ops = ops.Ops.param in
    let init = param_ops.on_name init name in
    let init = Param_bounds.bottom_up param_bounds ~init ~ops in
    let init = param_ops.on_param_bounds init param_bounds in
    init
  ;;

  let apply_subst { name; param_bounds } ~subst ~combine_prov =
    let param_bounds = Param_bounds.apply_subst param_bounds ~subst ~combine_prov in
    { name; param_bounds }
  ;;
end

and Param_bounds : sig
  type t =
    { lower : Annot.t
    ; upper : Annot.t
    }
  [@@deriving eq, compare, create, sexp, show]

  val create_equal : Annot.t -> t

  type 'a ops =
    { on_lower : 'a -> Annot.t -> 'a
    ; on_upper : 'a -> Annot.t -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a
  val apply_subst : t -> subst:Annot.t Name.Ty_param.Map.t -> combine_prov:(Prov.t -> Prov.t -> Prov.t) -> t

  (* TODO(mjt) add order sigs *)
  val top : Prov.t -> t
  val bottom : Prov.t -> t
  val meet : t -> t -> prov:Prov.t -> t
  val meet_many : t list -> prov:Prov.t -> t
  val join : t -> t -> prov:Prov.t -> t
  val join_many : t list -> prov:Prov.t -> t
  (* val top : t *)
end = struct
  type t =
    { lower : Annot.t
    ; upper : Annot.t
    }
  [@@deriving eq, compare, create, sexp, show]

  let create_equal ty = { lower = ty; upper = ty }

  type 'a ops =
    { on_lower : 'a -> Annot.t -> 'a
    ; on_upper : 'a -> Annot.t -> 'a
    }

  let id_ops =
    let ops = { on_lower = (fun acc _ -> acc); on_upper = (fun acc _ -> acc) } in
    fun _ -> ops
  ;;

  let bottom_up { lower; upper } ~ops ~init =
    let param_bounds_ops = ops.Ops.param_bounds in
    let init = Annot.bottom_up ~ops ~init lower in
    let init = Annot.bottom_up ~ops ~init upper in
    let init = param_bounds_ops.on_lower init lower in
    let init = param_bounds_ops.on_upper init upper in
    init
  ;;

  let apply_subst { lower; upper } ~subst ~combine_prov =
    let lower = Annot.apply_subst lower ~subst ~combine_prov
    and upper = Annot.apply_subst upper ~subst ~combine_prov in
    { lower; upper }
  ;;

  (** The meet (greatest lower bound) of parameter bounds is the greatest lower bound of the upper bounds  and the
      least upper bound of the lower bounds  i.e.
      `A <: T <: B`  /\  `C <: T <: D`
      is
      `A \/ C <: T <: B /\ D`, or
      `A | C <: T <: B & D` *)
  let meet { lower = lb1; upper = ub1 } { lower = lb2; upper = ub2 } ~prov =
    let lower = Annot.union ~prov [ lb1; lb2 ]
    (* If either upper-bound is `None` (mixed) the greatest lower bound is the other *)
    and upper = Annot.inter ~prov [ ub1; ub2 ] in
    { lower; upper }
  ;;

  (** The bottom element:  meet bottom _ = meet _ bottom = bottom *)
  (* let bottom prov = { lower = Some (Annot.mixed prov); upper = Some (Annot.nothing prov) } *)

  (** The join (least upper bound) of parameter bounds is the greatest lower bound of the lower bounds and the
      least upper bound of the upper bounds i.e
      `A <: T <: B`  \/  `C <: T <: D`
      is
      `A & C <: T <: B | D` *)
  let join { lower = lb1; upper = ub1 } { lower = lb2; upper = ub2 } ~prov =
    let lower = Annot.inter ~prov [ lb1; lb2 ]
    and upper = Annot.union ~prov [ ub1; ub2 ] in
    { lower; upper }
  ;;

  (** The top element: join top _ = join _ top = top *)
  let top prov = { lower = Annot.nothing prov; upper = Annot.mixed prov }

  let meet_many ts ~prov =
    let lowers, uppers =
      List.fold_left ts ~init:([], []) ~f:(fun (lowers, uppers) { lower; upper } ->
        let lowers = lower :: lowers
        and uppers = upper :: uppers in
        lowers, uppers)
    in
    let lower = Annot.union ~prov lowers
    and upper = Annot.inter ~prov uppers in
    { lower; upper }
  ;;

  let bottom prov = { lower = Annot.mixed prov; upper = Annot.nothing prov }

  let join_many ts ~prov =
    let lowers, uppers =
      List.fold_left ts ~init:([], []) ~f:(fun (lowers, uppers) { lower; upper } ->
        let lowers = lower :: lowers
        and uppers = upper :: uppers in
        lowers, uppers)
    in
    let lower = Annot.inter ~prov lowers
    and upper = Annot.union ~prov uppers in
    { lower; upper }
  ;;
end

and Ops : sig
  type 'a t =
    { ty : 'a Annot.ops
    ; fn : 'a Fn.ops
    ; tuple : 'a Tuple.ops
    ; ctor : 'a Ctor.ops
    ; exists : 'a Exists.ops
    ; param : 'a Param.ops
    ; param_bounds : 'a Param_bounds.ops
    }

  val id_ops : unit -> 'a t
  val collect_generics : unit -> Name.Ty_param.Set.t t
end = struct
  type 'a t =
    { ty : 'a Annot.ops
    ; fn : 'a Fn.ops
    ; tuple : 'a Tuple.ops
    ; ctor : 'a Ctor.ops
    ; exists : 'a Exists.ops
    ; param : 'a Param.ops
    ; param_bounds : 'a Param_bounds.ops
    }

  let id_ops _ =
    { ty = Annot.id_ops ()
    ; fn = Fn.id_ops ()
    ; tuple = Tuple.id_ops ()
    ; ctor = Ctor.id_ops ()
    ; exists = Exists.id_ops ()
    ; param = Param.id_ops ()
    ; param_bounds = Param_bounds.id_ops ()
    }
  ;;

  let collect_generics _ =
    let ty =
      let ops = Annot.id_ops () in
      Annot.{ ops with on_generic = (fun acc _ generic -> Set.add acc generic) }
    in
    let ops = id_ops () in
    { ops with ty }
  ;;
end

include Annot
module Refinement = Dnf.Make (Annot)

(* let refine t refinement =
  match Refinement.to_list_opt refinement with
  | None -> nothing
  | Some disjs -> union @@ List.map disjs ~f:(fun (poss, _negs) -> inter (t :: poss)) *)
