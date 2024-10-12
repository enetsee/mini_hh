let step Cstr.Is_subtype.{ ty_sub; ty_super } ~ctxt:_ ~state =
  match ty_sub, ty_super with
  | _, _ -> Ok (Prop.true_, state)
;;
