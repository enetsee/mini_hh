(* open Reporting

(** When we type a

    - Bounds on type parameters must respect the bounds on extends and implements
    - Bind type parameters ready to check elements
    - Gather bounds for [this]:

    + for a class: current class is the upper bound
    + for a trait: intersection of require extends and implements refine
    + for an interface: intersection of current interface  and require extends

    `uses` can introduce properties, methods and type constants but these are
    dealt with in the oracle

    - Properties: need to check any default values are subtypes of the declared
      type of the property
    - methods: need to *)

let synth
  (Lang.Classish_def.{ kind; name; ty_params; extends; implements; require_extends; require_implements } as t)
  ~ctxt
  ~env
  ~errs
  =

  (* Bind all type parameters *)


;; *)
