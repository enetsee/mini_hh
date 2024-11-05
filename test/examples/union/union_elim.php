<?hh


function union_disj_elim((arraykey | float | bool | null) $union): void {
    if($union is (string | bool)) {
        // $union should be (string | bool)
    } else {
        // We can actually calculate this for types where subtyping is the same 
        // as equality (i.e. base types) so here $union should be 
        // (int | float | null)
    }
}


class C  {}
class B {}
class A extends B {}
interface I {}

function union_general_elim((C | B) $union): void {
    if($union is (I | A)) {
      // $union should be ((C & I | B & I) | (C & A | A))
    } else {
      // $union should be (C | B) 
      // in the general case, we can't say anything unless we have difference types
    }
}