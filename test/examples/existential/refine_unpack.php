<?hh

class Bigly{}
class Smol<T> extends Bigly {}

function refine_unpack(Bigly $bigly): ?Bigly {
    $smol = null;
    if($bigly is some T. Smol<T>) {
        // $x should still be an existential here
        let {TSmol, $smol} = $bigly;
    }
    // Should be promoted to Bigly when we leave the continuation
    return $smol;
}