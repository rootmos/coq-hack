Definition repetition {X Y} (f: X -> Y) := {i: X & {j: X | i <> j & f i = f j}}.
Definition greater (X Y: Type) := forall f: X -> Y, repetition f.
Notation "X |>| Y" := (greater X Y) (at level 0). (* TODO: proper level *)

Definition miss {X Y} (f: X -> Y) := {y | forall x, f x <> y}.
Definition smaller (X Y: Type) := forall f: X -> Y, miss f.
Notation "X |<| Y" := (smaller X Y) (at level 0).

Definition streamless (X: Set) := nat |>| X.

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
  f 0 = Some x0 -> streamless X -> repetition f.
Proof.
  intros H sx.
  destruct (sx (fun n => match f (S n) with None => x0 | Some x => x end))
    as [i [j p0 p1]].
  case_eq (f (S i)); case_eq (f (S j)).
  - intros xj Fj xi Fi.
    exists (S i), (S j); auto. rewrite Fi, Fj in *. now rewrite p1.
  - intros Fj xi Fi.
    exists (S i), 0; auto. rewrite Fi, Fj in *. now rewrite H, p1.
  - intros xj Fj Fi.
    exists 0, (S j); auto. rewrite Fi, Fj in *. now rewrite H, p1.
  - intros Fj Fi.
    exists (S i), (S j); auto. now rewrite Fj, Fi.
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
      destruct (non_empty_option_streamless H0 sx) as [i [j p0 p1]].
      exists (S i), (S j); auto.
    + intros H0 H1. exists 0, 1; [auto|now rewrite H0, H1].
Qed.

Require Coq.Vectors.Fin.

Lemma fin_streamless (n: nat): streamless (Fin.t n).
Proof.
  induction n; intro f.
  - induction (f 0) using Fin.case0.
  - destruct (option_streamless IHn (fun x =>
      match f x in Fin.t (S n) return option (Fin.t n) with
        Fin.F1 => None | Fin.FS s => Some s end)) as [i [j p0 p1]].
    exists i, j; try assumption.
    induction (f i) using Fin.caseS'; induction (f j) using Fin.caseS';
      try discriminate || auto.
    inversion p1. now destruct H0.
Qed.

Require Import Hack.CMP.Fun.

Lemma streamless_inj {X X0: Set} {e: X0 -> X}:
  streamless X -> inj e -> streamless X0.
Proof.
  intros s ei f.
  destruct (s (fun n => e (f n))) as [i [j ne eq]].
  exists i, j; try assumption.
  now pose (ei (f i) (f j) eq).
Qed.

Lemma emb_zero_sum (X: Set): {f: X + Fin.t 0 -> X | inj f}.
Proof.
  assert (forall t: X + Fin.t 0, {x | inl x = t}) as H by
    (intro t; case t; intro u; [now exists u|induction u using Fin.case0]).
  destruct (Specif.Choice H) as [f pf].
  exists f.
  intros x y eq.
  now rewrite <- (pf x), <- (pf y), eq.
Qed.

Lemma fin_sum_streamless {X} (n: nat):
  streamless X -> streamless (X + Fin.t n).
Proof.
  intros sx.
  induction n.
  - destruct (emb_zero_sum X) as [i ii].
    exact (streamless_inj sx ii).
  - pose (i := fun xt: (X + Fin.t (S n)) => match xt with
      | inl x => Some (inl x)
      | inr t => match t with Fin.F1 => None | @Fin.FS n s => Some (inr s) end
      end).
    assert (inj i) as ii.
    {
      intros x x' H.
      destruct x, x'; try (compute in H; now inversion H);
        try (induction t using Fin.caseS'; compute in H; discriminate);
      induction t using Fin.caseS'; induction t0 using Fin.caseS';
      try (auto || discriminate). compute in H. now inversion H.
    }
    exact (streamless_inj (option_streamless IHn) ii).
Qed.

Lemma product_streamless {X Y}:
  streamless X -> streamless Y -> streamless (X*Y).
Proof.
  intros sx sy f.
  pose (fx := fun n => fst (f n)).
  pose (fy := fun n => snd (f n)).
  destruct (sx fx) as [i [j p0 p1]].
  induction i. induction j.
  exfalso.
  now apply p0.
Admitted.

Theorem streamless_sum {X Y}:
  streamless X -> streamless Y -> streamless (X + Y).
Proof.
  intros sx sy f.
  destruct (split_sum sx sy f) as [g gp].
  pose (s := product_streamless (option_streamless sx) (option_streamless sy)).
  destruct (s g) as [i [j ne eq]].
  case_eq (g i). case_eq (g j). intros.
  pose (gi := gp i). pose (gj := gp j).
  rewrite H0 in gi, eq.
  rewrite H in gj, eq.
  destruct o, o0, o1, o2; try contradiction; try discriminate eq;
  injection eq; destruct 1, gj; exists i, j; assumption.
Qed.
