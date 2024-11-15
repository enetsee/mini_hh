<?hh

function too_few_required((arraykey, arraykey) $tuple): void {
    if($tuple is (int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}

function too_many_required((arraykey, arraykey) $tuple): void {
    if($tuple is (int,int,int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}

function has_variadic((arraykey) $tuple): void {
    if($tuple is (int, int...)) {
       $x = 1;
    } else {
       $x = '1';
    }
}
