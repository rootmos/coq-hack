Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.
Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.
Record bij{X Y}(f: X -> Y) := mkBij { i: inj f; s: surj f }.
Definition ded_fin(X : Set) := forall f : X -> X, inj f -> surj f.

Section compose_props.
  Require Import Basics.
  Open Scope program_scope.

  Variable X Y Z: Type.
  Variable f: X -> Y.
  Variable g: Y -> Z.

  Theorem compose_surj: surj f -> surj g -> surj (g ∘ f).
  Proof.
    intros fs gs z.
    destruct (gs z) as [y py].
    destruct (fs y) as [x px].
    exists x.
    rewrite <- px in py.
    assumption.
  Qed.

  Theorem compose_inj: inj f -> inj g -> inj (g ∘ f).
  Proof.
    intros fi gi x x'. exact ((fi x x') ∘ (gi (f x) (f x'))).
  Qed.

  Theorem compose_bij: bij f -> bij g -> bij (g ∘ f).
  Proof.
    repeat destruct 1.
    constructor 1; [ apply compose_inj | apply compose_surj ]; assumption.
  Qed.
End compose_props.
