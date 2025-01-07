<?hh

class B<Tb> {}
class A<Ta> {}
class C {}
class D extends A<B<C>> {}

function expectC(C $_): null {}
function foo<T>(A<B<T>> $x, T $t): null {
  if ($x is D) {
    // $t should be C here
    // expectC($t);
    $x = 1;
  }
  return null;
}