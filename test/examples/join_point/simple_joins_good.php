<?hh

function bound_in_all(bool $cond): void {
    $x = false;
    if($cond) {
        $x = 1;
    } else {
        $x = "1";
    }

   // Error
    $y = $x;
}

function bound_in_both(bool $cond): void {
    if($cond) {
        $x = 1;
    } else {
        $x = "1";
    }

   // Error
    $y = $x;
}

function bound_in_left(bool $cond): void {
    $x = false;
    if($cond) {
        $x = 1;
    } else {
    }

   // Error
    $y = $x;
}

function bound_in_right(bool $cond): void {
    $x = false;
    if($cond) {
    } else {
        $x = "1";
    }

   // Error
    $y = $x;
}

