Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.
Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.
Record bij{X Y}(f: X -> Y) := mkBij { i: inj f; s: surj f }.
Definition ded_fin(X : Set) := forall f : X -> X, inj f -> surj f.