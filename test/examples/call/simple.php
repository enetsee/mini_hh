<?hh

function foo(int $x): int {
    return $x;
}

function bar(): int {
    return foo(1);
}