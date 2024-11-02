<?hh


function union_disj_elim((arraykey | float | bool | null) $union): void {
    if($union is (string | bool)) {
        // $union should be ()
    }
}