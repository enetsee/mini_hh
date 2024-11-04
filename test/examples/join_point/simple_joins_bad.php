<?hh

function bound_in_left_only(bool $cond): void {
    if($cond) {
        $x = 1;
    } else {
    }

   // Error
    $y = $x;
}

function bound_in_right_only(bool $cond): void {
    if($cond) {
    } else {
        $x = "1";
    }

   // Error
    $y = $x;
}
