Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.
Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.
Record bij{X Y}(f: X -> Y) := mkBij { i: inj f; s: surj f }.
Definition ded_fin(X : Set) := forall f : X -> X, inj f -> surj f.

Definition inv{X Y}(f: X -> Y) := {g: Y -> X | forall x y, f x = y <-> g y = x}.

Theorem inj_dec {X Y}: forall f: X -> Y,
  (forall x x': X, {x = x'} + {x <> x'}) -> inj f ->
  (forall x x', {f x = f x'} + {f x <> f x'}).
Proof.
  intros f D i x x'.
  case (D x x').
  + destruct 1. left. reflexivity.
  + intro n. right. intro. apply n, i. assumption.
Qed.

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

Section bij_props.
  Variable X Y: Type.
  Variable f: X -> Y.

  Theorem inv_bij: inv f -> bij f.
  Proof.
    intros [g p].
    constructor 1.
    - intros x x' H.
      rewrite <- (proj1 (p x (f x')) H).
      apply (proj1 (p x' (f x'))).
      reflexivity.
    - intro y.
      exists (g y).
      apply (proj2 (p (g y) y)).
      reflexivity.
  Qed.

  Theorem bij_inv: bij f -> inv f.
  Proof.
    intros [fi fs].
    exists (fun y => projT1 (fs y)).
    intros x y.
    pose (fs y) as p.
    replace (fs y) with p by reflexivity.
    dependent inversion_clear p as [x' q].
    rewrite <- q.
    split.
    - symmetry. apply fi. assumption.
    - intro H. rewrite <- H. reflexivity.
  Qed.
End bij_props.

Section vacuous_props.
  Lemma vacuous_f: forall Y, Empty_set -> Y.
  Proof.
    intros Y a. case a.
  Qed.

  Lemma vacuous_f_inj {Y}: forall f: Empty_set -> Y, inj f.
  Proof.
    intros f x. case x.
  Qed.

  Lemma vacuous_f_surj {X}: forall f: X -> Empty_set, surj f.
  Proof.
    intros f y. case y.
  Qed.
End vacuous_props.
