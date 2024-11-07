<?hh

class A {}
class B extends A {}

function blah(B $b): A {
  return $b;
}