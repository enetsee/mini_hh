<?hh

class Bigly<T>{}
class Smol<T> extends Bigly<T> {}

function scrut_and_test(some T1. Bigly<T1> $bigly): void {
    if($bigly is some T2. Smol<T2>) {
        let {TSmol, $smol} = $bigly;
    }
}