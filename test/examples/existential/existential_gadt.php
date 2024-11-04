<?hh

class Bigly<T>{}
class Smol extends Bigly<int> {}

function exists_gadt(some T1. Bigly<T1> $bigly): void {
    if($bigly is  Smol) {
    }
}