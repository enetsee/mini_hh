<?hh

function rcvr<TIn>(all T. (function(T): T) $id, TIn $x): TIn {
   return ($id)($x);
}

function id<T>(T $x): T {
    return $x;
}

function call(): int {
    rcvr(id, 1);
}