<?hh

interface I<T> {} 
interface J<T> {} 
interface K {} 
class E implements I<int>, J<int>, K {}

function union_test<T>((I<T> | J<T>) $i_or_j, (I<T> | K) $i_or_k): void {
    $x = null;
    if($i_or_j is E) {
        $x = 1;
        // T should be refined to int
    } else if ($i_or_k is E) {
        // no refinement on T
    }
}
