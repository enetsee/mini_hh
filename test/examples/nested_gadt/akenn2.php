<?hh

class B<Tb> {}
class A<-Ta> {}
class C {}
class D extends A<B<C>> {}
class E<Te> extends B<Te> {}

function expectC(C $_): null {}
function foo<T>(A<E<T>> $x, T $t): null {
  if ($x is D) {
    // $t should be C here 
    // expectC($t);
    return null;
  }

  return null;
}