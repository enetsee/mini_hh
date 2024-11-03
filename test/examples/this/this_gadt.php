<?hh


class Expr<T>  {
    public function num_thing(): ?int {
        if($this is IntExpr) {
            return 1;
        }
        return null;
    }
}

class IntExpr extends Expr<int> {}