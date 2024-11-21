<?hh

function foo<T>(T $x): T {
    return $x;
}

function bar(): int {
    return foo(1);
}