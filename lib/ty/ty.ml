open Core
open Reporting

(* ~~ Type variables ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module Var : sig
  type t [@@deriving compare, equal, sexp, show]

  val of_int : int -> t
end = struct
  module Minimal = struct
    type t = Var of int [@@ocaml.unboxed] [@@deriving compare, equal, sexp]

    let pp ppf (Var n) = Fmt.(any "#" ++ int) ppf n
  end

  include Minimal
  include Pretty.Make (Minimal)

  let of_int n = Var n
end

(* ~~ Types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
module rec Node : sig
  type t =
    (* | Var of Var.t *)
    | Base of Common.Base.t
    | Generic of Name.Ty_param.t
    | Tuple of Tuple.t
    | Shape of Shape.t
    | Fn of Fn.t
    | Ctor of Ctor.t
    | Exists of Exists.t
    | Union of Annot.t list
    | Inter of Annot.t list
    | Nonnull
  [@@deriving compare, equal, sexp, show, variants]
end = struct
  module Minimal = struct
    type t =
      (* | Var of Var.t *)
      | Base of Common.Base.t
      | Generic of Name.Ty_param.t
      | Tuple of Tuple.t
      | Shape of Shape.t
      | Fn of Fn.t
      | Ctor of Ctor.t
      | Exists of Exists.t
      | Union of Annot.t list
      | Inter of Annot.t list
      | Nonnull
    [@@deriving compare, equal, sexp, variants]

    let pp ppf t =
      match t with
      | Base base -> Fmt.(styled `Magenta Common.Base.pp) ppf base
      | Generic name -> Fmt.(styled `Green Name.Ty_param.pp) ppf name
      | Tuple tuple -> Tuple.pp ppf tuple
      | Shape shape -> Shape.pp ppf shape
      | Fn fn -> Fn.pp ppf fn
      | Ctor ctor -> Ctor.pp ppf ctor
      | Exists exists -> Exists.pp ppf exists
      | Union [] -> Fmt.any "nothing" ppf ()
      | Union tys ->
        Fmt.(hovbox @@ parens @@ list ~sep:(any " | ") Annot.pp) ppf tys
      | Inter [] -> Fmt.any "mixed" ppf ()
      | Inter tys ->
        Fmt.(hovbox @@ parens @@ list ~sep:(any " & ") Annot.pp) ppf tys
      | Nonnull -> Fmt.any "nonnull" ppf ()
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)
end

and Annot : sig
  type t =
    { prov : Prov.t
    ; node : Node.t
    }
  [@@deriving compare, create, equal, sexp, show]

  val prj : t -> Prov.t * Node.t

  type 'acc ops =
    { on_base : 'acc -> Prov.t -> Common.Base.t -> 'acc
    ; on_generic : 'acc -> Prov.t -> Name.Ty_param.t -> 'acc
    ; on_fn : 'acc -> Prov.t -> Fn.t -> 'acc
    ; on_tuple : 'acc -> Prov.t -> Tuple.t -> 'acc
    ; on_shape : 'acc -> Prov.t -> Shape.t -> 'acc
    ; on_ctor : 'acc -> Prov.t -> Ctor.t -> 'acc
    ; on_exists : 'acc -> Prov.t -> Exists.t -> 'acc
    ; on_union : 'acc -> Prov.t -> t list -> 'acc
    ; on_inter : 'acc -> Prov.t -> t list -> 'acc
    ; on_nonnull : 'acc -> Prov.t -> 'acc
    }

  val prov_of : t -> Prov.t
  val bottom_up : t -> ops:'acc Ops.t -> init:'acc -> 'acc
  val id_ops : unit -> 'acc ops
  val map_prov : t -> f:(Prov.t -> Prov.t) -> t
  val with_prov : t -> Prov.t -> t

  val apply_subst
    :  t
    -> subst:Annot.t Name.Ty_param.Map.t
    -> combine_prov:(Prov.t -> Prov.t -> Prov.t)
    -> t

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
  val bool : Prov.t -> t
  val null : Prov.t -> t
  val int : Prov.t -> t
  val float : Prov.t -> t
  val string : Prov.t -> t
  val generic : Prov.t -> Name.Ty_param.t -> t

  val tuple
    :  Prov.t
    -> required:t list
    -> optional:t list
    -> variadic:t option
    -> t

  val fn
    :  Prov.t
    -> required:t list
    -> optional:t list
    -> variadic:t option
    -> return:t
    -> t

  val shape
    :  Prov.t
    -> required:(Shape_field_label.t * t) list
    -> optional:(Shape_field_label.t * t) list
    -> variadic:t option
    -> t

  val ctor : Prov.t -> name:Name.Ctor.t -> args:t list -> t
  val exists : Prov.t -> quants:Param.t list -> body:t -> t
  val union : t list -> prov:Prov.t -> t
  val inter : t list -> prov:Prov.t -> t
  val arraykey : Prov.t -> t
  val nullable : Prov.t -> t -> t
  val num : Prov.t -> t
  val mixed : Prov.t -> t
  val nothing : Prov.t -> t
  val this : Prov.t -> t
  val nonnull : Prov.t -> t
end = struct
  type t =
    { prov : Prov.t
         [@equal.opaque] [@compare.opaque] [@equal.ignore] [@compare.ignore]
    ; node : Node.t
    }
  [@@deriving compare, create, equal, sexp]

  module Minimal = struct
    type nonrec t = t

    let pp ppf { node; _ } = Node.pp ppf node
  end

  include Pretty.Make (Minimal)

  let prov_of { prov; _ } = prov
  let prj { prov; node } = prov, node

  (* ~~ Traversals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  type 'acc ops =
    { on_base : 'acc -> Prov.t -> Common.Base.t -> 'acc
    ; on_generic : 'acc -> Prov.t -> Name.Ty_param.t -> 'acc
    ; on_fn : 'acc -> Prov.t -> Fn.t -> 'acc
    ; on_tuple : 'acc -> Prov.t -> Tuple.t -> 'acc
    ; on_shape : 'acc -> Prov.t -> Shape.t -> 'acc
    ; on_ctor : 'acc -> Prov.t -> Ctor.t -> 'acc
    ; on_exists : 'acc -> Prov.t -> Exists.t -> 'acc
    ; on_union : 'acc -> Prov.t -> t list -> 'acc
    ; on_inter : 'acc -> Prov.t -> t list -> 'acc
    ; on_nonnull : 'acc -> Prov.t -> 'acc
    }

  let id_ops =
    let ops =
      { on_base = (fun acc _ _ -> acc)
      ; on_generic = (fun acc _ _ -> acc)
      ; on_fn = (fun acc _ _ -> acc)
      ; on_tuple = (fun acc _ _ -> acc)
      ; on_shape = (fun acc _ _ -> acc)
      ; on_ctor = (fun acc _ _ -> acc)
      ; on_exists = (fun acc _ _ -> acc)
      ; on_union = (fun acc _ _ -> acc)
      ; on_inter = (fun acc _ _ -> acc)
      ; on_nonnull = (fun acc _ -> acc)
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
    | Shape shape ->
      let init = Shape.bottom_up shape ~ops ~init in
      ty_ops.on_shape init prov shape
    | Exists exists ->
      let init = Exists.bottom_up exists ~ops ~init in
      ty_ops.on_exists init prov exists
    | Union ts ->
      let init =
        List.fold_left ts ~init ~f:(fun init t -> bottom_up t ~ops ~init)
      in
      ty_ops.on_union init prov ts
    | Inter ts ->
      let init =
        List.fold_left ts ~init ~f:(fun init t -> bottom_up t ~ops ~init)
      in
      ty_ops.on_inter init prov ts
    | Nonnull -> ty_ops.on_nonnull init prov
  ;;

  (* ~~ Modify provenance ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  let map_prov { prov; node } ~f = { node; prov = f prov }
  let with_prov t prov = map_prov ~f:(fun _ -> prov) t

  (* ~~ Generic substitution ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
  let rec apply_subst ({ prov; node } as t) ~subst ~combine_prov =
    match node with
    | Base _ | Nonnull -> t
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
    | Shape shape ->
      let node = Node.shape (Shape.apply_subst shape ~subst ~combine_prov) in
      { prov; node }
    | Ctor ctor ->
      let node = Node.ctor (Ctor.apply_subst ctor ~subst ~combine_prov) in
      { prov; node }
    | Exists exists ->
      let node = Node.exists (Exists.apply_subst exists ~subst ~combine_prov) in
      { prov; node }
    | Union union ->
      let node =
        Node.union (List.map ~f:(apply_subst ~subst ~combine_prov) union)
      in
      { prov; node }
    | Inter inter ->
      let node =
        Node.inter (List.map ~f:(apply_subst ~subst ~combine_prov) inter)
      in
      { prov; node }
  ;;

  (** Quick hack to turn type which have been parsed as constructors into generics
      TODO(mjt) Ideally we will do this when we elaborate from CST to AST *)
  let rec elab_to_generic ({ prov; node } as t) ~bound_ty_params =
    match node with
    | Base _ | Generic _ | Nonnull -> t
    | Fn fn ->
      let node = Node.fn (Fn.elab_to_generic fn ~bound_ty_params) in
      { prov; node }
    | Tuple tuple ->
      let node = Node.tuple (Tuple.elab_to_generic tuple ~bound_ty_params) in
      { prov; node }
    | Shape shape ->
      let node = Node.shape (Shape.elab_to_generic shape ~bound_ty_params) in
      { prov; node }
    | Ctor Ctor.{ name; args = [] } ->
      let ty_param_name = Name.Ty_param.from_ctor_name name in
      if Set.mem bound_ty_params ty_param_name
      then (
        let node = Node.generic ty_param_name in
        { prov; node })
      else t
    | Ctor ctor ->
      let node = Node.ctor (Ctor.elab_to_generic ctor ~bound_ty_params) in
      { prov; node }
    | Exists exists ->
      let node = Node.exists (Exists.elab_to_generic exists ~bound_ty_params) in
      { prov; node }
    | Union union ->
      let node =
        Node.union (List.map ~f:(elab_to_generic ~bound_ty_params) union)
      in
      { prov; node }
    | Inter inter ->
      let node =
        Node.inter (List.map ~f:(elab_to_generic ~bound_ty_params) inter)
      in
      { prov; node }
  ;;

  (* ~~ Constructors ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

  let base prov base = create ~prov ~node:base ()
  let bool prov = base prov @@ Node.base Common.Base.bool
  let null prov = base prov @@ Node.base Common.Base.null
  let int prov = base prov @@ Node.base Common.Base.int
  let float prov = base prov @@ Node.base Common.Base.float
  let string prov = base prov @@ Node.base Common.Base.string
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

  let shape prov ~required ~optional ~variadic =
    let required = Shape_field_label.Map.of_alist_exn required
    and optional = Shape_field_label.Map.of_alist_exn optional in
    let node = Node.shape @@ Shape.create ~required ~optional ?variadic () in
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

  let nonnull prov =
    let node = Node.nonnull in
    create ~prov ~node ()
  ;;

  let is_nothing t =
    match t.node with
    | Node.Union [] -> true
    | _ -> false
  ;;

  let is_mixed t =
    match t.node with
    | Node.Inter [] -> true
    | _ -> false
  ;;

  let expand_union t =
    match t.node with
    | Node.Union ts -> ts
    | _ -> [ t ]
  ;;

  (** This is an expensive and impractical smart constructor without fast equality
      but fine for demo purposes *)
  let union elems ~prov =
    match
      List.dedup_and_sort ~compare
      @@ List.filter ~f:(fun t -> not @@ is_nothing t)
      @@ List.concat_map ~f:expand_union elems
    with
    | [ ty ] -> ty
    | elems when List.exists ~f:is_mixed elems ->
      let node = Node.inter [] in
      create ~prov ~node ()
    | elems ->
      let node = Node.union @@ elems in
      create ~prov ~node ()
  ;;

  let expand_inter t =
    match t.node with
    | Node.Inter ts -> ts
    | _ -> [ t ]
  ;;

  (** This is an expensive and impractical smart constructor without fast equality
      but fine for demo purposes *)
  let inter elems ~prov =
    match
      List.dedup_and_sort ~compare
      @@ List.filter ~f:(fun t -> not @@ is_mixed t)
      @@ List.concat_map ~f:expand_inter elems
    with
    | [ ty ] -> ty
    | elems when List.exists ~f:is_nothing elems -> union [] ~prov
    | elems ->
      let node = Node.inter elems in
      create ~prov ~node ()
  ;;

  let arraykey prov = union ~prov [ int prov; string prov ]
  let num prov = union ~prov [ int prov; float prov ]
  let nullable prov t = union ~prov [ t; null prov ]
  let nothing prov = union ~prov []
  let mixed prov = inter ~prov []
  let this prov = generic prov Name.Ty_param.this
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

  val apply_subst
    :  t
    -> subst:Annot.t Name.Ty_param.Map.t
    -> combine_prov:(Prov.t -> Prov.t -> Prov.t)
    -> t

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  module Minimal = struct
    type t =
      { params : Tuple.t
      ; return : Annot.t
      }
    [@@deriving compare, create, equal, create, sexp]

    let pp ppf { params; return } =
      Fmt.(hovbox @@ pair ~sep:(any ": ") Tuple.pp Annot.pp) ppf (params, return)
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let apply_subst { params; return } ~subst ~combine_prov =
    let params = Tuple.apply_subst params ~subst ~combine_prov
    and return = Annot.apply_subst return ~subst ~combine_prov in
    { params; return }
  ;;

  let elab_to_generic { params; return } ~bound_ty_params =
    let params = Tuple.elab_to_generic params ~bound_ty_params
    and return = Annot.elab_to_generic return ~bound_ty_params in
    { params; return }
  ;;

  type 'a ops =
    { on_params : 'a -> Tuple.t -> 'a
    ; on_return : 'a -> Annot.t -> 'a
    }

  let id_ops =
    let ops =
      { on_params = (fun acc _ -> acc); on_return = (fun acc _ -> acc) }
    in
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

(* ~~ Tuple types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
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

  val apply_subst
    :  t
    -> subst:Annot.t Name.Ty_param.Map.t
    -> combine_prov:(Prov.t -> Prov.t -> Prov.t)
    -> t

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  module Minimal = struct
    type t =
      { required : Annot.t list
      ; optional : Annot.t list
      ; variadic : Annot.t option
      }
    [@@deriving compare, create, equal, create, map, sexp]

    let pp_optional ppf annot =
      Fmt.(hbox @@ (any "optional " ++ Annot.pp)) ppf annot
    ;;

    let pp_variadic ppf annot =
      Fmt.(hbox @@ (any ", ..." ++ Annot.pp)) ppf annot
    ;;

    let pp ppf { required; optional; variadic } =
      Fmt.(
        hovbox
        @@ parens
        @@ pair ~sep:comma (list ~sep:comma Annot.pp)
        @@ pair (list ~sep:comma pp_optional)
        @@ option pp_variadic)
        ppf
        (required, (optional, variadic))
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  type 'acc ops =
    { on_required : 'acc -> Annot.t list -> 'acc
    ; on_optional : 'acc -> Annot.t list -> 'acc
    ; on_variadic : 'acc -> Annot.t option -> 'acc
    }

  let bottom_up { required; optional; variadic } ~ops ~init =
    let tuple_ops = ops.Ops.tuple in
    let init =
      List.fold_left required ~init ~f:(fun init ty ->
        Annot.bottom_up ~ops ~init ty)
    in
    let init = tuple_ops.on_required init required in
    let init =
      List.fold_left optional ~init ~f:(fun init ty ->
        Annot.bottom_up ~ops ~init ty)
    in
    let init = tuple_ops.on_optional init optional in
    let init =
      Option.fold variadic ~init ~f:(fun init ty ->
        Annot.bottom_up ~ops ~init ty)
    in
    let init = tuple_ops.on_variadic init variadic in
    init
  ;;

  let id_ops =
    let ops =
      { on_required = (fun acc _ -> acc)
      ; on_optional = (fun acc _ -> acc)
      ; on_variadic = (fun acc _ -> acc)
      }
    in
    fun _ -> ops
  ;;

  let apply_subst { required; optional; variadic } ~subst ~combine_prov =
    let required =
      List.map required ~f:(Annot.apply_subst ~subst ~combine_prov)
    in
    let optional =
      List.map optional ~f:(Annot.apply_subst ~subst ~combine_prov)
    in
    let variadic =
      Option.map variadic ~f:(Annot.apply_subst ~subst ~combine_prov)
    in
    { required; optional; variadic }
  ;;

  let elab_to_generic { required; optional; variadic } ~bound_ty_params =
    let required =
      List.map required ~f:(Annot.elab_to_generic ~bound_ty_params)
    in
    let optional =
      List.map optional ~f:(Annot.elab_to_generic ~bound_ty_params)
    in
    let variadic =
      Option.map variadic ~f:(Annot.elab_to_generic ~bound_ty_params)
    in
    { required; optional; variadic }
  ;;
end

(* ~~ Shape types ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Shape : sig
  type t =
    { required : Annot.t Shape_field_label.Map.t
    ; optional : Annot.t Shape_field_label.Map.t
    ; variadic : Annot.t option
    }
  [@@deriving compare, create, equal, create, sexp, show]

  type 'acc ops =
    { on_required : 'acc -> Annot.t Shape_field_label.Map.t -> 'acc
    ; on_optional : 'acc -> Annot.t Shape_field_label.Map.t -> 'acc
    ; on_variadic : 'acc -> Annot.t option -> 'acc
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'acc Ops.t -> init:'acc -> 'acc

  val apply_subst
    :  t
    -> subst:Annot.t Name.Ty_param.Map.t
    -> combine_prov:(Prov.t -> Prov.t -> Prov.t)
    -> t

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  module Minimal = struct
    type t =
      { required : Annot.t Shape_field_label.Map.t
      ; optional : Annot.t Shape_field_label.Map.t
      ; variadic : Annot.t option
      }
    [@@deriving compare, create, equal, create, sexp]

    let pp_shape_field ppf (label, ty) =
      Fmt.(hovbox @@ pair ~sep:(any " => ") Shape_field_label.pp Annot.pp)
        ppf
        (label, ty)
    ;;

    let pp_optional_shape_field ppf (label, ty) =
      Fmt.(
        hovbox
        @@ pair ~sep:(any " => ") (any "?" ++ Shape_field_label.pp) Annot.pp)
        ppf
        (label, ty)
    ;;

    let pp ppf { required; optional; variadic } =
      match Map.to_alist required, Map.to_alist optional, variadic with
      | [], [], None -> Fmt.(any "shape ()") ppf ()
      | reqs, [], None ->
        Fmt.(
          any "shape" ++ (hovbox @@ parens @@ list ~sep:comma pp_shape_field))
          ppf
          reqs
      | [], opts, None ->
        Fmt.(
          any "shape"
          ++ (hovbox @@ parens @@ list ~sep:comma pp_optional_shape_field))
          ppf
          opts
      | [], [], Some ty ->
        Fmt.(any "shape" ++ (hovbox @@ parens @@ (Annot.pp ++ any "...")))
          ppf
          ty
      | reqs, opts, None ->
        Fmt.(
          any "shape"
          ++ (hovbox
              @@ parens
              @@ pair
                   ~sep:comma
                   (list ~sep:comma pp_shape_field)
                   (list ~sep:comma pp_optional_shape_field)))
          ppf
          (reqs, opts)
      | reqs, [], Some ty ->
        Fmt.(
          any "shape"
          ++ (hovbox
              @@ parens
              @@ pair
                   ~sep:comma
                   (list ~sep:comma pp_shape_field)
                   (Annot.pp ++ any "...")))
          ppf
          (reqs, ty)
      | [], opts, Some ty ->
        Fmt.(
          any "shape"
          ++ (hovbox
              @@ parens
              @@ pair
                   ~sep:comma
                   (list ~sep:comma pp_optional_shape_field)
                   (Annot.pp ++ any "...")))
          ppf
          (opts, ty)
      | reqs, opts, Some ty ->
        Fmt.(
          any "shape"
          ++ (hovbox
              @@ parens
              @@ pair
                   ~sep:comma
                   (pair
                      ~sep:comma
                      (list ~sep:comma pp_shape_field)
                      (list ~sep:comma pp_optional_shape_field))
                   (Annot.pp ++ any "...")))
          ppf
          ((reqs, opts), ty)
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  type 'acc ops =
    { on_required : 'acc -> Annot.t Shape_field_label.Map.t -> 'acc
    ; on_optional : 'acc -> Annot.t Shape_field_label.Map.t -> 'acc
    ; on_variadic : 'acc -> Annot.t option -> 'acc
    }

  let id_ops _ =
    { on_required = (fun acc _ -> acc)
    ; on_optional = (fun acc _ -> acc)
    ; on_variadic = (fun acc _ -> acc)
    }
  ;;

  let bottom_up { required; optional; variadic } ~ops ~init =
    let shape_ops = ops.Ops.shape in
    let init =
      Map.fold required ~init ~f:(fun ~key:_ ~data:ty init ->
        Annot.bottom_up ~ops ~init ty)
    in
    let init = shape_ops.on_required init required in
    let init =
      Map.fold optional ~init ~f:(fun ~key:_ ~data:ty init ->
        Annot.bottom_up ~ops ~init ty)
    in
    let init = shape_ops.on_optional init optional in
    let init =
      Option.fold variadic ~init ~f:(fun init ty ->
        Annot.bottom_up ~ops ~init ty)
    in
    let init = shape_ops.on_variadic init variadic in
    init
  ;;

  let apply_subst { required; optional; variadic } ~subst ~combine_prov =
    let required =
      Map.map required ~f:(Annot.apply_subst ~subst ~combine_prov)
    in
    let optional =
      Map.map optional ~f:(Annot.apply_subst ~subst ~combine_prov)
    in
    let variadic =
      Option.map variadic ~f:(Annot.apply_subst ~subst ~combine_prov)
    in
    { required; optional; variadic }
  ;;

  let elab_to_generic { required; optional; variadic } ~bound_ty_params =
    let required =
      Map.map required ~f:(Annot.elab_to_generic ~bound_ty_params)
    in
    let optional =
      Map.map optional ~f:(Annot.elab_to_generic ~bound_ty_params)
    in
    let variadic =
      Option.map variadic ~f:(Annot.elab_to_generic ~bound_ty_params)
    in
    { required; optional; variadic }
  ;;
end

and Shape_field_label : sig
  type t = Lit of Name.Shape_field_label.t
  [@@deriving compare, equal, sexp, show, variants]

  module Map : Map.S with type Key.t := t
end = struct
  module Minimal = struct
    type t = Lit of Name.Shape_field_label.t
    [@@deriving compare, equal, sexp, variants]

    let pp ppf = function
      | Lit name -> Name.Shape_field_label.pp ppf name
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)
  module Map = Map.Make (Minimal)
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

  val apply_subst
    :  t
    -> subst:Annot.t Name.Ty_param.Map.t
    -> combine_prov:(Prov.t -> Prov.t -> Prov.t)
    -> t

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  module Minimal = struct
    type t =
      { name : Name.Ctor.t
      ; args : Annot.t list
      }
    [@@deriving compare, create, equal, sexp]

    let surround s1 s2 pp_v ppf v =
      Format.(
        pp_print_string ppf s1;
        pp_v ppf v;
        pp_print_string ppf s2)
    ;;

    let angles pp_v = Fmt.(hovbox ~indent:1 (surround "<" ">" pp_v))

    let pp ppf { name; args } =
      if List.is_empty args
      then Name.Ctor.pp ppf name
      else
        Fmt.(
          hovbox
          @@ pair ~sep:nop (styled `Cyan Name.Ctor.pp)
          @@ angles
          @@ list ~sep:comma Annot.pp)
          ppf
          (name, args)
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

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
    let init =
      List.fold_left args ~init ~f:(fun init ty ->
        Annot.bottom_up ~ops ~init ty)
    in
    let init = ctor_ops.on_args init args in
    init
  ;;

  let apply_subst { name; args } ~subst ~combine_prov =
    let args = List.map args ~f:(Annot.apply_subst ~subst ~combine_prov) in
    { name; args }
  ;;

  let elab_to_generic { name; args } ~bound_ty_params =
    let args = List.map args ~f:(Annot.elab_to_generic ~bound_ty_params) in
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

  val apply_subst
    :  t
    -> subst:Annot.t Name.Ty_param.Map.t
    -> combine_prov:(Prov.t -> Prov.t -> Prov.t)
    -> t

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  module Minimal = struct
    type t =
      { quants : Param.t list
      ; body : Annot.t
      }
    [@@deriving eq, compare, create, sexp, show]

    let pp ppf { quants; body } =
      if List.is_empty quants
      then Annot.pp ppf body
      else
        Fmt.(
          hovbox
          @@ pair ~sep:(any ". ") (any "∃ " ++ list ~sep:sp Param.pp) Annot.pp)
          ppf
          (quants, body)
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  type 'a ops =
    { on_quants : 'a -> Param.t list -> 'a
    ; on_body : 'a -> Annot.t -> 'a
    }

  let id_ops =
    let ops =
      { on_quants = (fun acc _ -> acc); on_body = (fun acc _ -> acc) }
    in
    fun _ -> ops
  ;;

  let bottom_up { quants; body } ~ops ~init =
    let exists_ops = ops.Ops.exists in
    let init =
      List.fold_left quants ~init ~f:(fun init param ->
        Param.bottom_up ~ops ~init param)
    in
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

  let elab_to_generic { quants; body } ~bound_ty_params =
    (* bind all the quantifiers - do this before elaborating quantifiers as they
       may contain other quantifiers in their bounds *)
    let bound_ty_params =
      let declared_ty_params =
        Name.Ty_param.Set.of_list
        @@ List.map ~f:(fun Param.{ name; _ } -> Located.elem name) quants
      in
      Set.union bound_ty_params declared_ty_params
    in
    let quants = List.map quants ~f:(Param.elab_to_generic ~bound_ty_params)
    and body = Annot.elab_to_generic body ~bound_ty_params in
    { body; quants }
  ;;
end

and Param : sig
  type t =
    { name : Name.Ty_param.t Located.t
    ; param_bounds : Param_bounds.t
    }
  [@@deriving eq, compare, create, sexp, show]

  type 'a ops =
    { on_name : 'a -> Name.Ty_param.t Located.t -> 'a
    ; on_param_bounds : 'a -> Param_bounds.t -> 'a
    }

  val id_ops : unit -> 'a ops
  val bottom_up : t -> ops:'a Ops.t -> init:'a -> 'a

  val apply_subst
    :  t
    -> subst:Annot.t Name.Ty_param.Map.t
    -> combine_prov:(Prov.t -> Prov.t -> Prov.t)
    -> t

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t
end = struct
  module Minimal = struct
    type t =
      { name : Name.Ty_param.t Located.t
      ; param_bounds : Param_bounds.t
      }
    [@@deriving eq, compare, create, sexp]

    let pp ppf { name; param_bounds } =
      Fmt.(hovbox @@ pair ~sep:sp (Located.pp Name.Ty_param.pp) Param_bounds.pp)
        ppf
        (name, param_bounds)
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  type 'a ops =
    { on_name : 'a -> Name.Ty_param.t Located.t -> 'a
    ; on_param_bounds : 'a -> Param_bounds.t -> 'a
    }

  let id_ops =
    let ops =
      { on_name = (fun acc _ -> acc); on_param_bounds = (fun acc _ -> acc) }
    in
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
    let param_bounds =
      Param_bounds.apply_subst param_bounds ~subst ~combine_prov
    in
    { name; param_bounds }
  ;;

  let elab_to_generic { name; param_bounds } ~bound_ty_params =
    let param_bounds =
      Param_bounds.elab_to_generic param_bounds ~bound_ty_params
    in
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

  val apply_subst
    :  t
    -> subst:Annot.t Name.Ty_param.Map.t
    -> combine_prov:(Prov.t -> Prov.t -> Prov.t)
    -> t

  val elab_to_generic : t -> bound_ty_params:Name.Ty_param.Set.t -> t

  (* TODO(mjt) add order sigs *)
  val top : Prov.t -> t
  val bottom : Prov.t -> t
  val meet : t -> t -> prov:Prov.t -> t
  val meet_many : t list -> prov:Prov.t -> t
  val join : t -> t -> prov:Prov.t -> t
  val join_many : t list -> prov:Prov.t -> t
  (* val top : t *)
end = struct
  module Minimal = struct
    type t =
      { lower : Annot.t
      ; upper : Annot.t
      }
    [@@deriving eq, compare, create, sexp]

    let pp ppf { lower; upper } =
      Fmt.(
        hbox @@ pair ~sep:sp (any "as " ++ Annot.pp) (any "super " ++ Annot.pp))
        ppf
        (upper, lower)
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  let create_equal ty = { lower = ty; upper = ty }

  type 'a ops =
    { on_lower : 'a -> Annot.t -> 'a
    ; on_upper : 'a -> Annot.t -> 'a
    }

  let id_ops =
    let ops =
      { on_lower = (fun acc _ -> acc); on_upper = (fun acc _ -> acc) }
    in
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

  let elab_to_generic { lower; upper } ~bound_ty_params =
    let lower = Annot.elab_to_generic lower ~bound_ty_params
    and upper = Annot.elab_to_generic upper ~bound_ty_params in
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
      List.fold_left
        ts
        ~init:([], [])
        ~f:(fun (lowers, uppers) { lower; upper } ->
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
      List.fold_left
        ts
        ~init:([], [])
        ~f:(fun (lowers, uppers) { lower; upper } ->
          let lowers = lower :: lowers
          and uppers = upper :: uppers in
          lowers, uppers)
    in
    let lower = Annot.inter ~prov lowers
    and upper = Annot.union ~prov uppers in
    { lower; upper }
  ;;
end

(* ~~ Helpers for traversals ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
and Ops : sig
  type 'a t =
    { ty : 'a Annot.ops
    ; fn : 'a Fn.ops
    ; tuple : 'a Tuple.ops
    ; shape : 'a Shape.ops
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
    ; shape : 'a Shape.ops
    ; ctor : 'a Ctor.ops
    ; exists : 'a Exists.ops
    ; param : 'a Param.ops
    ; param_bounds : 'a Param_bounds.ops
    }

  let id_ops _ =
    { ty = Annot.id_ops ()
    ; fn = Fn.id_ops ()
    ; tuple = Tuple.id_ops ()
    ; shape = Shape.id_ops ()
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

module Refinement = struct
  module Minimal = struct
    type t =
      | Intersect_with of Prov.t * Annot.t
      (** If we refine to a type which is not a subtype of the scrutinees type
          we end up with an intersection *)
      | Replace_with of Annot.t
      (** If we refine to a type which is a subtype of the scrutinees type it would
          be redundant to construct an intersection - we can simply use the refined
          type. *)
      | Disjoint of Prov.t
      (** If we refine to a type which is disjoint from the scrutiness type the
          result is always [nothing]. This is the same as [Replace_with nothing]
          but we keep this around so we can do partial complements of refinements *)
    [@@deriving compare, eq, sexp, show, variants]

    let pp ppf t =
      match t with
      | Intersect_with (_, ty) -> Fmt.(any "_ & " ++ Annot.pp) ppf ty
      | Replace_with ty -> Fmt.(any "_ ← " ++ Annot.pp) ppf ty
      | Disjoint _ -> Fmt.(any "_ ← ⊥") ppf ()
    ;;
  end

  include Minimal
  include Pretty.Make (Minimal)

  (** Applying the union of two refinements is equivalent to find the union of the types after appying each refinement.
      Given that `Replace_with ty` tells us that [ty] is a subtype of the type it is refining we can simplify as follows:

      apply t (Disjoint `join` ...) ~~>
      (apply t Disjoint) | (apply t ...) ~~>
      nothing | ... ~~> ...

      (same for ... join Disjoint)

      apply t (Replace_with t1 `join` Replace_with t2) ~~(meaning of join)~~>
      (apply t (Replace_with t1)) | (apply t (Replace_with t2)) ~~(definition of apply)~~>
      t1 | t2 ~~(definition of apply)~~>
      apply t Replace_with (t1 | t2)

      apply t (Intersect_with t1 `join` Intersect_with t2) ~~(meaning of join)~~>
      (apply t (Intersect_with t1)) | (apply t (Intersect_with t2)) ~~(definition of apply)~~>
      (t & t1) | (t & t2) ~~(distribute intersection over union)~~>
      (t | t) & (t1 | t2) ~~(simplify union)~~>
      t & (t1 | t2) ~~(definition of apply)~~>
      apply t (Intersect_with (t1 | t2))

      apply t (Replace_with t1 `join` Intersect_with t2) ~~(meaning of join)~~>
      (apply t (Replace_with t1)) | (apply t (Intersect_with t2)) ~~(definition of apply)~~>
      t1 | (t & t2)  ~~(distribute union over intersection)~~>
      (t | t1) & (t1 | t2) ~~(t1 <: t)~~>
      t & (t1 | t2) ~~(definition of apply)~~>
      apply t (Intersect_with  (t1 | t2)) *)
  let join t1 t2 ~prov =
    match t1, t2 with
    | Disjoint _, _ -> t2
    | _, Disjoint _ -> t1
    | Replace_with ty1, Replace_with ty2 ->
      Replace_with (Annot.union [ ty1; ty2 ] ~prov)
    | Intersect_with (prov1, ty1), Intersect_with (_prov2, ty2) ->
      Intersect_with (prov, Annot.union [ ty1; ty2 ] ~prov:prov1)
    | Replace_with ty1, Intersect_with (prov2, ty2)
    | Intersect_with (prov2, ty2), Replace_with ty1 ->
      Intersect_with (prov, Annot.union [ ty1; ty2 ] ~prov:prov2)
  ;;

  (** Applying the intersection of two refinements is equivalent to finding the intersection of the types
      after applying each refinement

      apply t (meet (Replace_with t1) (Replace_with t2)) ~~(meaning of meet)~~>
      (apply t (Replace_with t1)) & (apply t (Replace_with t2)) ~~(definition of apply)~~>
      t1 & t2 ~~(definition of apply)~~>
      apply t (Replace_with (t1 & t2))

      apply t (inter (Intersect_with t1) (Intersect_with t2)) =
      (apply t (Intersect_with t1)) & (apply t (Intersect_with t2)) =
      (t & t1) & (t & t2) =
      (t & t1) & t2 =
      apply t (Intersect_with (t1&t2))

      apply t (inter (Replace_with t1) (Intersect_with t2)) =
      (apply t (Replace_with t1)) & (apply t (Intersect_with t2)) =
      t1 & (t & t2) =
      t1 & t2 =
      apply t (Replace_with (t1 & t2)) *)
  let meet t1 t2 ~prov =
    match t1, t2 with
    | Disjoint _, _ -> t1
    | _, Disjoint _ -> t2
    | Replace_with ty1, Replace_with ty2 ->
      Replace_with (Annot.inter [ ty1; ty2 ] ~prov)
      (* TODO(mjt) We lose provenance in the other cases so maybe rexamine this in the prov language *)
    | Intersect_with (prov1, ty1), Intersect_with (_prov2, ty2) ->
      Intersect_with (prov, Annot.inter [ ty1; ty2 ] ~prov:prov1)
    | Replace_with ty1, Intersect_with (_prov, ty2)
    | Intersect_with (_prov, ty2), Replace_with ty1 ->
      Replace_with (Annot.inter [ ty1; ty2 ] ~prov)
  ;;
end

include Annot

let refine t ~rfmt =
  match rfmt with
  | Refinement.Replace_with ty -> ty
  | Refinement.Intersect_with (prov, ty) -> inter [ t; ty ] ~prov
  | Refinement.Disjoint prov -> nothing prov
;;
