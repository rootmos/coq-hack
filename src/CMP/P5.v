Definition streamless(X : Set) := forall f : nat -> X,
    {i : nat & {j : nat & i <> j /\ f i = f j}}.

Lemma split_sum {X Y}:
  streamless X -> streamless Y ->
  forall f: nat -> X + Y,
  {g: nat -> ((option X)*(option Y)) &
    forall n, match g n with
      | (Some x, None) => f n = inl x
      | (None, Some y) => f n = inr y
      | _ => False end}.
Proof.
  intros sx sy f.
  exists (fun n => match f n with
    | inl x => (Some x, None)
    | inr y => (None, Some y) end
  ).
  intros n. case (f n); intro; reflexivity.
Qed.

Lemma non_empty_option_streamless {X: Set} {f: nat -> option X} {x0}:
  f 0 = Some x0 -> streamless X ->
  {i : nat & {j : nat & i <> j /\ f i = f j}}.
Proof.
  intros H sx.
  destruct (sx (fun n => match f (S n) with None => x0 | Some x => x end))
    as [i [j [p0 p1]]].
  case_eq (f (S i)); case_eq (f (S j)).
  - intros xj Fj xi Fi.
    exists (S i), (S j).
    split; auto. rewrite Fi, Fj in *. now rewrite p1.
  - intros Fj xi Fi.
    exists (S i), 0.
    split; auto. rewrite Fi, Fj in *. now rewrite H, p1.
  - intros xj Fj Fi.
    exists 0, (S j).
    split; auto. rewrite Fi, Fj in *. now rewrite H, p1.
  - intros Fj Fi.
    exists (S i), (S j).
    split; auto. now rewrite Fj, Fi.
Qed.

Lemma option_streamless {X}: streamless X -> streamless (option X).
Proof.
  intros sx f.
  case_eq (f 0).
  - intros x0 H0.
    apply (non_empty_option_streamless H0 sx).
  - case_eq (f 1).
    + intros x0 H0 _.
      pose (f' := fun n => f (S n)).
      replace (f 1) with (f' 0) in H0 by auto.
      destruct (non_empty_option_streamless H0 sx) as [i [j [p0 p1]]].
      exists (S i), (S j); auto.
    + intros H0 H1. exists 0, 1. split; [auto|now rewrite H0, H1].
Qed.

Lemma product_streamless {X Y}: streamless X -> streamless Y -> streamless (X*Y).
Proof.
  intros sx sy f.
Admitted.

Theorem streamless_sum {X Y}:
  streamless X -> streamless Y -> streamless (X + Y).
Proof.
  intros sx sy f.
  destruct (split_sum sx sy f) as [g gp].
  pose (s := product_streamless (option_streamless sx) (option_streamless sy)).
  destruct (s g) as [i [j [ne eq]]].
  case_eq (g i). case_eq (g j). intros.
  pose (gi := gp i). pose (gj := gp j).
  rewrite H0 in gi, eq.
  rewrite H in gj, eq.
  destruct o, o0, o1, o2; try contradiction; try discriminate eq;
  injection eq; destruct 1, gj; exists i, j; split; assumption.
Qed.
