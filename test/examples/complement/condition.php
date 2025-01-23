<?hh
// (c) Meta Platforms, Inc. and affiliates. Confidential and proprietary.

class Foo {}

interface IMyGenericTaker<T> {
  // public function takes(T $t): void;
}

abstract class FooTaker implements IMyGenericTaker<Foo> {
}

abstract class FooTakerChild extends FooTaker {
}


function split<T>(IMyGenericTaker<T> $taker, T $t): void {
  if ($taker is FooTaker || $taker is FooTakerChild) {
    // $taker->takes($t);
  }
}
