<?hh

function required_required((function (int, int): arraykey) $fn): void {
    if($fn is (function (arraykey,arraykey): int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}

function optional_optional((function (optional int, optional int): arraykey) $fn): void {
    if($fn is (function (optional arraykey,optional arraykey): int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}

function variadic_variadic((function (int...): arraykey) $fn): void {
    if($fn is (function (arraykey...): int)) {
       $x = 1;
    } else {
       $x = '1';
    }
}



