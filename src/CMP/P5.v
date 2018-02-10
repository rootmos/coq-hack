Require Coq.Vectors.Fin.
Require Import Hack.CMP.Fun.
Require Import Omega.

Definition repetition {X Y} (f: X -> Y) := {i: X & {j: X | i <> j & f i = f j}}.
Definition greater (X Y: Type) := forall f: X -> Y, repetition f.
Notation "X |>| Y" := (greater X Y) (at level 0). (* TODO: proper level *)

Definition miss {X Y} (f: X -> Y) := {y | forall x, f x <> y}.
Definition smaller (X Y: Type) := forall f: X -> Y, miss f.
Notation "X |<| Y" := (smaller X Y) (at level 0).

Definition streamless (X: Set) := nat |>| X.

Lemma split_sum {X Y}:
  forall f: nat -> X + Y,
  {g: nat -> ((option X)*(option Y)) &
    forall n, match g n with
      | (Some x, None) => f n = inl x
      | (None, Some y) => f n = inr y
      | _ => False end}.
Proof.
  intros f.
  exists (fun n => match f n with
    | inl x => (Some x, None)
    | inr y => (None, Some y) end
  ).
  intros n. case (f n); intro; reflexivity.
Qed.

Record Split {X Y} (f: nat -> X + Y) (n: nat) := mkSplit {
  Split_nx: nat;
  Split_ix: Fin.t Split_nx -> nat;
  Split_fx: Fin.t Split_nx -> X;
  Split_px: forall t, inl (Split_fx t) = f (Split_ix t);
  Split_ny: nat;
  Split_iy: Fin.t Split_ny -> nat;
  Split_fy: Fin.t Split_ny -> Y;
  Split_py: forall t, inr (Split_fy t) = f (Split_iy t);
  Split_pn: Split_nx + Split_ny = n;
}.

Definition split_fin {n} (t: Fin.t (S n)): unit + Fin.t n :=
  match t with
  | Fin.F1 => inl tt
  | Fin.FS s => inr s
  end.

Lemma split {X Y} (f: nat -> X + Y) (n: nat): Split f n.
Proof.
  induction n.
  - assert (forall X, Fin.t 0 -> X) as vacuous by
      (intros Z t; induction t using Fin.case0).
    pose (ix := vacuous nat). pose (fx := vacuous X).
    assert (forall t, inl (fx t) = f (ix t)) as px by
      (intro t; induction t using Fin.case0).
    pose (iy := vacuous nat). pose (fy := vacuous Y).
    assert (forall t, inr (fy t) = f (iy t)) as py by
      (intro t; induction t using Fin.case0).
    now refine (mkSplit _ _ _ _ _ _ _ px _ _ _ py _).
  - destruct IHn as [nx ix fx px ny iy fy py pn].
    case_eq (f (S n)).
    + intros x H.
      pose (fun t => match split_fin t with inl _ => S n | inr s => ix s end)
        as ix'.
      pose (fun t => match split_fin t with inl _ => x | inr s => fx s end)
        as fx'.
      assert (forall t, inl (fx' t) = f (ix' t)) as px' by
        (intro t; induction t using Fin.caseS'; [auto|apply px]).
      refine (mkSplit _ _ _ _ _ _ _ px' _ _ _ py _); omega.
    + intros y H.
      pose (fun t => match split_fin t with inl _ => S n | inr s => iy s end)
        as iy'.
      pose (fun t => match split_fin t with inl _ => y | inr s => fy s end)
        as fy'.
      assert (forall t, inr (fy' t) = f (iy' t)) as py' by
        (intro t; induction t using Fin.caseS'; [auto|apply py]).
      refine (mkSplit _ _ _ _ _ _ _ px _ _ _ py' _); omega.
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
      | inr t => match t with Fin.F1 => None | Fin.FS s => Some (inr s) end
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

Lemma streamless_prod {X Y}:
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
  destruct (split_sum f) as [g gp].
  pose (s := streamless_prod (option_streamless sx) (option_streamless sy)).
  destruct (s g) as [i [j ne eq]].
  case_eq (g i). case_eq (g j). intros.
  pose (gi := gp i). pose (gj := gp j).
  rewrite H0 in gi, eq.
  rewrite H in gj, eq.
  destruct o, o0, o1, o2; try contradiction; try discriminate eq;
  injection eq; destruct 1, gj; exists i, j; assumption.
Qed.

Lemma fin_product_streamless {X} (n: nat):
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
