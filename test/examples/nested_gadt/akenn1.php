<?hh

class B<Tb> {}
class A<Ta> {}
class C {}
class D extends A<B<C>> {}

function expectC(C $_): void {}
function foo<T>(A<B<T>> $x, T $t): void {
  if ($x is D) {
    // $t should be C here
    // expectC($t);
  }
}