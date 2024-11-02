<?hh

class B<Tb> {}
class A<-Ta> {}
class C {}
class D extends A<B<C>> {}
class E<Te> extends B<Te> {}

function expectC(C $_): void {}
function foo<T>(A<E<T>> $x, T $t): void {
  if ($x is D) {
    // $t should be C here 
    // expectC($t);
  }
}