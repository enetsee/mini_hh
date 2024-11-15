<?hh

function required_required(shape ('one' => arraykey) $scrut): void {
    if($scrut is shape ('one' => int)) {
        $x = 1;
    } else {
        $x = 1;
    }
}