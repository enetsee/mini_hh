module Classish = Classish

type t = { classish : Classish.t } [@@deriving show]

(*
   class A extends  B<int>
   class A<T1, T2> extends  B<T1> where T1 as T2
*)

let up { classish } ~of_ ~at = Classish.up classish ~of_ ~at
let find_ctor { classish } id = Classish.find classish id

module Example = struct
  let oracle = { classish = Classish.Example.data }
end
