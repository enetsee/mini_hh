<?hh

interface IBox<T> {
  public function set(T $x): void {}
  public function get(): ?T {}
}

class MyClass {}

function foo(MyClass $scrut): void {
  $x = null;
  if ($scrut is some T. IBox<T>) {
    // hh implicitly unpacks the existential, here we do it explicitly
    let {T,$box} = $scrut;
    $x = $box;
    // $x = $scrut->get();
  }
  $_ = $x;
}
