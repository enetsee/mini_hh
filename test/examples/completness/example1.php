<?hh

class Bigly {}
class Small extends Bigly {}
interface ICovContrav<+TCov, -TContrav> {}
class MyClass<T super Small as Bigly> implements ICovContrav<T, T> {}

function refine<T>(ICovContrav<T, T> $i): void {
  if ($i is some (T super Small as Bigly). MyClass<T>) {
    /* We should have refined:
       Small <= T <= Bigly
       T <= Texists <= T */
  }
}