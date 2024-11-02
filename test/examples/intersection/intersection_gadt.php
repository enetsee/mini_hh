<?hh

interface I<T> {} 
interface J<T> {} 
interface K {} 
class E implements I<int>, J<int>, K {}

function union_test<T>((I<T> & J<T>) $i_and_j, (I<T> & K) $i_and_k): void {
    if($i_and_j is E) {
        // T should be refined to int
    } else if ($i_and_k is E) {
        // T should be refined to int
    }
}
