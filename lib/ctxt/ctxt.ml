open Core
module Local = Local
module Classish = Classish
module Fn = Fn
module Def = Def
module Cont = Cont
module Ty_param = Ty_param

module Minimal = struct
  (** The context across all continuations *)
  type t =
    { next : Cont.t option
    ; exit : Cont.t option (** retained for try.. finally *)
    }
  [@@deriving create, fields, show]

  let empty = { next = None; exit = None }
end

module Delta = struct
  type t =
    { next : Cont.Delta.t option
    ; exit : Cont.Delta.t option
    }
  [@@deriving create, show]

  let empty = { next = None; exit = None }
  let lift { next; exit } ~f = { next = Option.map ~f next; exit = Option.map ~f exit }

  let lift2 { next = next1; exit = exit1 } { next = next2; exit = exit2 } ~f =
    let next = Option.merge ~f next1 next2
    and exit = Option.merge ~f exit1 exit2 in
    { next; exit }
  ;;

  let join t1 t2 ~prov = lift2 t1 t2 ~f:Cont.Delta.(join ~prov)
  let extend t ~with_ = lift2 t with_ ~f:(fun t with_ -> Cont.Delta.extend t ~with_)
end

let update t ~delta =
  let f t delta = Cont.update t ~delta in
  let next = Option.map2 ~f t.Minimal.next delta.Delta.next
  and exit = Option.map2 ~f t.Minimal.exit delta.Delta.exit in
  Minimal.create ?next ?exit ()
;;

include Minimal