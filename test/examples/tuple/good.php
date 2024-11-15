<?hh

function required_required((arraykey, arraykey) $tuple): void {
    if($tuple is (int,int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}

function optional_optional((optional arraykey, optional arraykey) $tuple): void {
    if($tuple is (optional int, optional int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}

function variadic_variadic((arraykey...) $tuple): void {
    if($tuple is (int...)) {
       $x = 1;
    } else {
       $x = '1';
    }
}

function required_optional((optional arraykey) $tuple): void {
    if($tuple is (int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}

function required_variadic((arraykey...) $tuple): void {
    if($tuple is (int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}   

function optional_variadic((arraykey...) $tuple): void {
    if($tuple is (optional int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}   

function variadic_optional((optional arraykey) $tuple): void {
    if($tuple is (int...)) {
       $x = 1;
    } else {
       $x = '1';
    }
}   
