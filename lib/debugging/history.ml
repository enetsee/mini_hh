open Core

module Alt = struct
  type tree =
    | Enter of Step.t
    | Step of Step.t
    | Exit of Step.t
    | Branch of tree list

  type path =
    | Empty
    | Path of
        { left : tree list
        ; up : path
        ; right : tree list
        }

  type zipper =
    { cursor : tree
    ; path : path
    }

  let init def =
    let step = Handler.run (fun _ -> Typing.Def.synth def) () in
    let event = Step.event step in
    let _ : unit = assert (Status.Event.is_enter event) in
    { cursor = Step step; path = Path { left = []; up = Empty; right = [] } }
  ;;

  (* let next t ~oracle = 
    match t with 
    | { cursor = Leaf step ; path = None } ->
      (* This is either the end of the computation or we haven't yet run the 
         continuation *)
      begin
        match Step.next step ~oracle with
        | Some next_step  ->
            
           
        | None -> None 
      end *)
end

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
