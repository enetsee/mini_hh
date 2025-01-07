open Core

module Alt = struct
  type tree =
    | Leaf of Step.t
    | Branch of tree list

  (* if this is an enter event, acccumulate until we hit an exit *)
  let unfold def ~oracle =
    let rec aux step_opt acc acc_branch =
      match step_opt with
      | None ->
        let acc =
          match acc_branch with
          | [] -> List.rev acc
          | _ -> List.rev (Branch acc_branch :: acc)
        in
        Branch acc, None
      | Some step ->
        let event = Step.event step in
        if Status.Event.is_enter event
        then (
          let delta, step_opt =
            aux (Step.next step ~oracle) (Leaf step :: acc) []
          in
          aux step_opt acc (delta :: acc_branch))
        else if Status.Event.is_exit event
        then (
          let acc = Leaf step :: Branch acc_branch :: acc in
          aux (Step.next step ~oracle) acc [])
        else (
          let acc_branch = Leaf step :: acc_branch in
          aux (Step.next step ~oracle) acc acc_branch)
    in
    let init = Handler.run (fun _ -> Typing.Def.synth def) () in
    fst @@ aux (Some init) [] []
  ;;

  type path =
    | Empty
    | Path of
        { left : tree list
        ; up : path
        ; right : tree list
        }

  type t =
    { cursor : tree
    ; path : path
    }

  let of_tree t = { cursor = t; path = Empty }
  let init def ~oracle = of_tree @@ unfold def ~oracle

  let move_up t =
    match t with
    | { path = Empty; _ } -> None
    | { cursor; path = Path { left; up = path; right } } ->
      Some { cursor = Branch (List.rev left @ (cursor :: right)); path }
  ;;

  let move_down { cursor; path } =
    match cursor with
    | Leaf _ ->
      (* We can't move down from a leaf *)
      None
    | Branch ts ->
      (match ts with
       | cursor :: right ->
         Some { cursor; path = Path { left = []; up = path; right } }
       | [] -> None)
  ;;

  let move_left { cursor; path } =
    match path with
    | Path { left = prev :: left; up; right } ->
      Some { cursor = prev; path = Path { left; up; right = cursor :: right } }
    | Path _ | Empty -> None
  ;;

  let move_right { cursor; path } =
    match path with
    | Path { left; up; right = next :: right } ->
      Some { cursor = next; path = Path { left = cursor :: left; up; right } }
    | Empty | Path _ -> None
  ;;

  let rec move_up_until_right t =
    match move_up t with
    | Some t ->
      (match move_right t with
       | Some t -> Some t
       | _ -> move_up_until_right t)
    | _ -> None
  ;;

  let rec move_up_until_left t =
    match move_up t with
    | Some t ->
      (match move_left t with
       | Some t -> Some t
       | _ -> move_up_until_left t)
    | _ -> None
  ;;

  let next t =
    match t.cursor with
    | Leaf _ -> move_right t
    | Branch _ -> move_down t
  ;;

  let prev t =
    let next_opt = move_left t in
    if Option.is_some next_opt then next_opt else move_up_until_left t
  ;;

  let start t =
    let rec aux t =
      match prev t with
      | Some t -> aux t
      | _ -> t
    in
    aux t
  ;;

  let rec first t =
    match t with
    | Leaf step -> step
    | Branch (next :: _) -> first next
    | _ -> failwith "Empty branch"
  ;;

  let current { cursor; _ } = first cursor
end

type t =
  { prev : (Step.t * int) list
  ; current : Step.t * int
  ; next : (Step.t * int) list
  }

let init def =
  let step = Handler.run (fun _ -> Typing.Def.synth def) () in
  let current = step, 0 in
  { prev = []; current; next = [] }
;;

let current { current; _ } = current

let next { prev; current; next } ~oracle =
  let mk cursor next = { prev = current :: prev; current = cursor; next } in
  match next with
  | cursor :: next -> Some (mk cursor next)
  | [] ->
    let depth =
      let step, depth = current in
      let event = Step.event step in
      if Status.Event.is_enter event then depth + 1 else depth
    in
    Option.map ~f:(fun step ->
      let depth =
        let event = Step.event step in
        if Status.Event.is_exit event then depth - 1 else depth
      in
      let cursor = step, depth in
      mk cursor [])
    @@ Step.next (fst current) ~oracle
;;

let prev { prev; current; next } =
  match prev with
  | [] -> None
  | cursor :: prev -> Some { prev; current = cursor; next = current :: next }
;;

let start ({ prev; current; next } as t) =
  match List.rev prev with
  | [] -> t
  | first :: rest ->
    { prev = []; current = first; next = rest @ (current :: next) }
;;

let rec next_until ({ current; _ } as t) ~oracle ~pred =
  if pred current
  then t
  else (
    match next t ~oracle with
    | None -> t
    | Some t -> next_until t ~oracle ~pred)
;;

let next_while t ~oracle ~pred =
  next_until t ~oracle ~pred:(fun t -> not @@ pred t)
;;
