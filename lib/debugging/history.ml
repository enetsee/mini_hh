open Core

type t =
  { prev : Step.t list
  ; current : Step.t
  ; next : Step.t list
  }

let init def =
  let current = Handler.run (fun _ -> Typing.Def.synth def) () in
  { prev = []; current; next = [] }
;;

let current { current; _ } = current

let next { prev; current; next } ~oracle =
  let mk cursor next = { prev = current :: prev; current = cursor; next } in
  match next with
  | cursor :: next -> Some (mk cursor next)
  | [] ->
    Option.map ~f:(fun cursor -> mk cursor []) @@ Step.next current ~oracle
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
