<?hh

class Bigly {}
class Smol extends Bigly {}

interface IExpr<+T> {}
class BiglyExpr extends IExpr<Bigly> {}

function agree<T as Smol>(IExpr<T> $expr): ?int {
    if($expr is BiglyExpr) {
        return 1;
    } else {
        
    }
    return null;
}