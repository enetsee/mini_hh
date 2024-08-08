let step Cstr.Is_subtype.{ ty_sub; ty_super } ~ctxt:_ ~env =
  match ty_sub, ty_super with
  | _, _ -> Ok (Prop.true_, env)
;;
