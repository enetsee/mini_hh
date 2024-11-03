<?hh

class C {}
interface I {}
interface J {}

function refine_and(C $x, C $y): void {
    if($x is I && $x is J) {

    }

    if($x is I && $y is J) {

    }
}