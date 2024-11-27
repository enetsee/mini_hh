<?hh

function refine(shape('a' => arraykey, ?'b' => arraykey, 'c' => arraykey, ?'d' => arraykey, ...) $scrut): void {
    if($scrut is shape('a' => int, 'c' => int, 'e' => int)) {
      $x = 1;
    } else {
      $x = 2;
    }
}

function call(
    shape('a' => int, 'c' => int, 'e' => int) $one,
    shape('a' => string, 'c' => string) $two, 
    shape('a' => string, 'e' => string) $bad, 
    ): void {
  refine($one);
  refine($two);
  refine($bad);
}   