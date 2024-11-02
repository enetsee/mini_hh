<?hh

class Box<T> {
    // TODO(mjt) allow on source programs:
    // - visibility modifiers on function arguments 
    // - missing parameter and return hints
  public function __construct(T $item): void { }
}

interface I {
  // TODO(mjt) allow on source programs:
  // - method signatures
  public function get(): Box<this> {}
}

class C {
  public function whatever(): Box<this> {
    if($this is I) {
       // Upper bound for this modified
       //   return $this->get();
    }
  }
}