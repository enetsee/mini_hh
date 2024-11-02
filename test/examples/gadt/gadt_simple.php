<?hh

interface IExpr<T> {}

class IntExpr implements IExpr<int> {}

function foo<T>(IExpr<T> $expr): void {
  if($expr is IntExpr) {

  }    
}
