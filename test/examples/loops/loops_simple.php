<?hh

function loop_1(): void {
    $x = 1
    
    // ctxt: $x : int
    while(true) {
        if($cond) { break; }
        $x = '1';
    }
    // next: $x: string
    // exit: $x: int
    // delta: $x : #1 , int <: #1 , string <: #1
}

function loop_2(): void {
    $x = 1
    
    // ctxt: $x : int
    while(true) {
        if($cond) { break; }
        $y = '1'
        $x = $y;
    }
    // next: $x: string
    // exit: $x: int
    // delta: $x : #1 , int <: #1 , string <: #1
}

function loop_3(): void {
    $x = 1
    
    // ctxt: $x : int
    while(true) {
        if($cond) { break; }
        $x = vec[$x];
    }
    // next: $x: string
    // exit: $x: int
    // delta: $x : #1 , int <: #1 , string <: #1
}