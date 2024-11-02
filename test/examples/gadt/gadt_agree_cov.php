<?hh

class Bigly {}
class Smol extends Bigly {}

interface IExpr<+T> {}
class SmolExpr extends IExpr<Smol> {}

function agree<T as Bigly>(IExpr<T> $expr): ?int {
    if($expr is SmolExpr) {
        return 1;
    } else {
        
    }
    return null;
}