open Core

module Is_subtype = struct
  type t =
    { ty_sub : Ty.t
    ; ty_super : Ty.t
    }
  [@@deriving compare, create, eq, sexp]

  let pp ppf { ty_sub; ty_super } =
    Fmt.(hovbox @@ pair ~sep:(any " <: ") Ty.pp Ty.pp) ppf (ty_sub, ty_super)
  ;;

  let show t = Fmt.to_to_string pp t
end

type t = Is_subtype of Is_subtype.t [@@deriving compare, eq, sexp, variants]

let pp ppf = function
  | Is_subtype is_subtype -> Is_subtype.pp ppf is_subtype
;;

let show t = Fmt.to_to_string pp t

let is_subtype ~ty_sub ~ty_super =
  is_subtype @@ Is_subtype.create ~ty_sub ~ty_super ()
;;

module Store = struct
  module Status = struct
    type t =
      | Solved of Ty.t
      | Cstrs of
          { lower_bounds : Ty.t list
          ; upper_bounds : Ty.t list
          }
      | Err
    [@@deriving compare, eq, sexp, show, variants]

    let empty = Cstrs { lower_bounds = []; upper_bounds = [] }

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

    let add_lower_bound t ~bound =
      match t with
      | Cstrs { upper_bounds; lower_bounds } ->
        let lower_bounds = bound :: lower_bounds in
        Cstrs { upper_bounds; lower_bounds }
      | Solved _ -> failwith "Already solved"
      | Err -> Err
    ;;

    let add_upper_bound t ~bound =
      match t with
      | Cstrs { upper_bounds; lower_bounds } ->
        let upper_bounds = bound :: upper_bounds in
        Cstrs { upper_bounds; lower_bounds }
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

    let solve_to t ty =
      let status = Status.solved ty in
      { t with status }
    ;;

    let empty = { status = Status.empty; variance = None }
    let get_lower_bounds { status; _ } = Status.get_lower_bounds status
    let get_upper_bounds { status; _ } = Status.get_upper_bounds status
  end

  type t = Entry.t Ty.Var.Map.t

  let empty = Ty.Var.Map.empty

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

  let add (t : t) ~var : t = Map.add_exn t ~key:var ~data:Entry.empty
  let get_lower_bounds_exn t ~var = Entry.get_lower_bounds @@ Map.find_exn t var
  let get_upper_bounds_exn t ~var = Entry.get_upper_bounds @@ Map.find_exn t var
end
