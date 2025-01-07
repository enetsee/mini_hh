<?hh

class C<T> {}
class D<T> extends C<T> {}
function foo(C<num> $scrut): null {
    if($scrut is D<int>) {
        $x = 1;
    }
    return null;
}
