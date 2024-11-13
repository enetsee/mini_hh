<?hh

final class MyInt {}
final class MyString {}
final class MyBool {}

case type LiftableTo<+T> as Blah =
  | int where T super MyInt
  | string where T super MyString
  | bool where T super MyBool;
