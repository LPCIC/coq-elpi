Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
Arguments populate {_} _ : assert.

Compute (populate 3).
Compute ({| inhabitant := 3 |}).