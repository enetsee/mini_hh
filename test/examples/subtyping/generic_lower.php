<?hh

class A {}
class B extends A {}

function blah<T super A>(B $b): T {
  return $b;
}