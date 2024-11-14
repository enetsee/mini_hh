<?hh


function refine_nonnull(mixed $x): nonnull {
    if($x is null) {
      return "whatever";
    } else {
      return $x;
    }
}