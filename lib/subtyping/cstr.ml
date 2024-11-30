open Core

module Is_subtype = struct
  type t =
    { ty_sub : Ty.t
    ; ty_super : Ty.t
    ; polarity : bool
    }
  [@@deriving equal, create, compare, sexp]

  let pp ppf { ty_sub; ty_super; _ } =
    Fmt.(hovbox @@ pair ~sep:(any " <: ") Ty.pp Ty.pp) ppf (ty_sub, ty_super)
  ;;

  let show t = Fmt.to_to_string pp t
end

module Can_instantiate_with = struct
  type t =
    { ty : Ty.t
    ; args : Ty.t list
    }
  [@@deriving equal, create, compare, sexp]

  let pp ppf { ty; args } =
    Fmt.(
      hovbox @@ pair ~sep:(any " @ ") Ty.pp @@ parens @@ list ~sep:comma Ty.pp)
      ppf
      (ty, args)
  ;;

  let show t = Fmt.to_to_string pp t
end

type t =
  | Is_subtype of Is_subtype.t
  | Can_instantiate_with of Can_instantiate_with.t
[@@deriving compare, eq, sexp, variants]

let pp ppf = function
  | Is_subtype is_subtype -> Is_subtype.pp ppf is_subtype
  | Can_instantiate_with can_instantiate_with ->
    Can_instantiate_with.pp ppf can_instantiate_with
;;

let show t = Fmt.to_to_string pp t

let is_subtype_with_polarity ~ty_sub ~ty_super ~polarity =
  is_subtype @@ Is_subtype.create ~ty_sub ~ty_super ~polarity ()
;;

let is_subtype ~ty_sub ~ty_super =
  is_subtype @@ Is_subtype.create ~ty_sub ~ty_super ~polarity:true ()
;;

let can_instantiate_with ~ty ~args =
  can_instantiate_with @@ Can_instantiate_with.create ~ty ~args ()
;;

module Store = struct
  module Status = struct
    type cstrs =
      { lower_bounds : Ty.t list
      ; upper_bounds : Ty.t list
      ; instantiations : Ty.t list list
      }
    [@@deriving compare, eq, sexp, show]

    type t =
      | Solved of Ty.t
      | Cstrs of cstrs
      | Err
    [@@deriving compare, eq, sexp, show, variants]

    let empty =
      Cstrs { lower_bounds = []; upper_bounds = []; instantiations = [] }
    ;;

    let get_upper_bounds = function
      | Solved ty -> [ ty ]
      | Cstrs { upper_bounds; _ } -> upper_bounds
      | Err -> []
    ;;

    let get_lower_bounds = function
      | Solved ty -> [ ty ]
      | Cstrs { lower_bounds; _ } -> lower_bounds
      | Err -> []
    ;;

    let get_instantiations = function
      | Solved _ -> []
      | Cstrs { instantiations; _ } -> instantiations
      | Err -> []
    ;;

    let add_lower_bound t ~bound =
      match t with
      | Cstrs ({ lower_bounds; _ } as cstrs) ->
        let lower_bounds = bound :: lower_bounds in
        Cstrs { cstrs with lower_bounds }
      | Solved _ -> failwith "Already solved"
      | Err -> Err
    ;;

    let add_upper_bound t ~bound =
      match t with
      | Cstrs ({ upper_bounds; _ } as cstrs) ->
        let upper_bounds = bound :: upper_bounds in
        Cstrs { cstrs with upper_bounds }
      | Solved _ -> failwith "Already solved"
      | Err -> Err
    ;;

    let add_instantiation t ~args =
      match t with
      | Cstrs ({ instantiations; _ } as cstrs) ->
        let instantiations = args :: instantiations in
        Cstrs { cstrs with instantiations }
      | Solved _ -> failwith "Already solved"
      | Err -> Err
    ;;
  end

  module Entry = struct
    type t =
      { status : Status.t
      ; variance : Common.Variance.t option
      }

    let add_upper_bound ({ status; _ } as t) ~bound =
      let status = Status.add_upper_bound status ~bound in
      { t with status }
    ;;

    let add_lower_bound ({ status; _ } as t) ~bound =
      let status = Status.add_lower_bound status ~bound in
      { t with status }
    ;;

    let add_instantiation ({ status; _ } as t) ~args =
      let status = Status.add_instantiation status ~args in
      { t with status }
    ;;

    let solve_to t ty =
      let status = Status.solved ty in
      { t with status }
    ;;

    let observe_variance ({ variance = var_opt; _ } as t) ~variance =
      let variance =
        Some
          (Option.value_map var_opt ~default:variance ~f:(fun v ->
             Common.Variance.meet v variance))
      in
      { t with variance }
    ;;

    let empty = { status = Status.empty; variance = None }
    let get_lower_bounds { status; _ } = Status.get_lower_bounds status
    let get_upper_bounds { status; _ } = Status.get_upper_bounds status
    let get_instantiations { status; _ } = Status.get_instantiations status
  end

  type t = Entry.t Ty.Var.Map.t

  let empty = Ty.Var.Map.empty
  let entries (t : t) = Map.to_alist t

  let add_upper_bound t ~var ~bound =
    Map.update t var ~f:(function
      | Some entry -> Entry.add_upper_bound entry ~bound
      | _ -> failwith "Unbound type variable")
  ;;

  let add_lower_bound t ~var ~bound =
    Map.update t var ~f:(function
      | Some entry -> Entry.add_lower_bound entry ~bound
      | _ -> failwith "Unbound type variable")
  ;;

  let add_instantiation t ~var ~args =
    Map.update t var ~f:(function
      | Some entry -> Entry.add_instantiation entry ~args
      | _ -> failwith "Unbound type variable")
  ;;

  let observe_variance_exn t ~var ~variance =
    Map.update t var ~f:(function
      | Some entry -> Entry.observe_variance entry ~variance
      | _ -> failwith "Unbound type variable")
  ;;

  let add (t : t) ~var : t = Map.add_exn t ~key:var ~data:Entry.empty
  let get_lower_bounds_exn t ~var = Entry.get_lower_bounds @@ Map.find_exn t var
  let get_upper_bounds_exn t ~var = Entry.get_upper_bounds @@ Map.find_exn t var
  let get_instantiations t ~var = Entry.get_instantiations @@ Map.find_exn t var
end
