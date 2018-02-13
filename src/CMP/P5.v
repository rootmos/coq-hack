Require Coq.Vectors.Fin.
Require Import Hack.CMP.Fun.
Require Import Omega.

Definition repetition {X Y} (f: X -> Y) := {i: X & {j: X | i <> j & f i = f j}}.
Definition streamless (X: Set) := forall f: nat -> X, repetition f.

Theorem streamless_inj {X X0: Set} {e: X0 -> X}:
  streamless X -> inj e -> streamless X0.
Proof.
  intros s ei f.
  destruct (s (fun n => e (f n))) as [i [j ne eq]].
  exists i, j; try assumption.
  now pose (ei (f i) (f j) eq).
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

Theorem fin_streamless (n: nat): streamless (Fin.t n).
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

Definition aux {X Y: Set} (f: nat -> X + Y) (sx: streamless X) (n M: nat):
  repetition f + {y: Y & {i | inr y = f i & M < i}}.
Proof.
  destruct (option_streamless sx
    (fun n => match f (n + M + 1) with inl x => Some x | _ => None end)
  ) as [i [j p0 p1]].
  case_eq (f (i + M + 1)); case_eq (f (j + M +1));
  try (intros u q0 v q1; now rewrite q0, q1 in p1).
  + intros. left. exists (i + M + 1), (j + M + 1); [omega|].
    rewrite H, H0 in p1. inversion p1. subst. now transitivity (inl (B:=Y) x).
  + intros. right. exists y. exists (j + M + 1); [auto|omega].
Qed.

Definition cadr {A B P} (s: {a: A & {b: B | P a b}}) :=
    match s with existT _ _ (exist _ b _) => b end.

Lemma construct_aux {X Y: Set} (f: nat -> X + Y) (sx: streamless X):
  {g: nat -> repetition f + {y: Y & {i | inr y = f i}} |
      forall n m {sn sm}, inr sn = g n -> inr sm = g m ->
      n <> m -> cadr sn <> cadr sm}.
Admitted.

Theorem streamless_sum {X Y}:
  streamless X -> streamless Y -> streamless (X + Y).
Proof.
  intros sx sy f.
  destruct (construct_aux f sx) as [g pg].
  destruct (option_streamless sy
    (fun n => match g n with inl _ => None | inr s => Some (projT1 s) end)
  ) as [i [j p0 p1]].
  case_eq (g i); case_eq (g j); try now intros.
  intros s0 eq0 s1 eq1.
  pose (pg i j s1 s0 (eq_sym eq1) (eq_sym eq0) p0).
  destruct s0 as [y0 [u pu]].
  destruct s1 as [y1 [v pv]].
  exists u, v; [auto|].
  rewrite eq0, eq1 in p1.
  inversion p1. subst.
  now transitivity (inr (A:=X) y0).
Qed.

Lemma streamless_fin_product {X} (n: nat):
  streamless X -> streamless (X * Fin.t n).
Proof.
  intro sx.
  induction n.
  - intro f. destruct (f 0) as [_ t]. induction t using Fin.case0.
  - pose (i := fun xt: (X * Fin.t (S n)) => let (x, t) := xt in
      match t with Fin.F1 => inr x | Fin.FS s => inl (x, s) end).
    assert (inj i) as ii.
    {
      intros [x t] [x' t'] H.
      induction t using Fin.caseS'; induction t' using Fin.caseS';
        compute in H; try (now inversion H || discriminate).
    }
    refine (streamless_inj _ ii).
    now apply streamless_sum.
Qed.
