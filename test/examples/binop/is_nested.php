<?hh

class C {}
interface I {}
interface J {}

function refine_and(C $x): void {
    if($x is I) { 
      if($x is J) {

      }
    }
}