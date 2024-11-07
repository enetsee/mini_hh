<?hh

class Four {}
class Three extends Four {}
class Two extends Three {}
class One extends Two {}

class MySuper<T> {}
class MySub<T as Three super Two> extends MySuper<T> {}

function refine<T as Four super One>(
    MySuper<T> $scrut, 
    Two $at_most_two,
): ?T {
  if ($scrut is some (T as Three super Two). MySub<T>) {
    return $at_most_two;
  }
  return null;
}