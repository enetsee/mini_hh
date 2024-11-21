<?hh

function foo<T>(T $x): T {
    return $x;
}

function bar(): int {
    /* I can't figure out how to get of a shift/reduce conflict 
       so I'm using double angles... */
    return foo<<int>>(1);
}