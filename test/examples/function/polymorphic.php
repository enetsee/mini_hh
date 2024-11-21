<?hh

function rcvr(all T. (function(T): T) $id, T $x): T {
   return ($id)($x);
}

function id<T>(T $x): T {
    return $x;
}

function call(): int {
    rcvr(id, 1);
}