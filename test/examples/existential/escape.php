<?hh

interface IBox<T> {
  public function set(T $x): void {}
  public function get(): ?T {}
}

class MyClass {}

function foo(MyClass $scrut): void {
  $x = null;
  if ($scrut is some T. IBox<T>) {
    let {T,$box} = $scrut;
    $x = $scrut;
    // $x = $scrut->get();
  }
  $_ = $x;
}
