Require Coq.Vectors.Fin.
Require Import Hack.CMP.Fun.
Require Import Omega.

Definition repetition {X Y: Set} (f: X -> Y) :=
  {i: X & {j | i <> j & f i = f j}}.
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

Inductive AuxT {X Y: Set} (f: nat -> X + Y): Set :=
| Aux_rep: repetition f -> AuxT f
| Aux_right: forall i y, inr y = f i -> AuxT f.

Definition AuxT_bnd {X Y: Set} {f: nat -> X + Y} (a: AuxT f) :=
  match a with
  | Aux_rep _ (existT _ i (exist2 _ _ j _ _)) => max i j
  | Aux_right _ i _ _ => i
  end.

Definition aux {X Y: Set} (f: nat -> X + Y) (sx: streamless X) (M: nat):
  {a: AuxT f | M < AuxT_bnd a}.
Proof.
  destruct (option_streamless sx
    (fun n => match f (n + M + 1) with inl x => Some x | _ => None end)
  ) as [i [j p0 p1]].
  case_eq (f (i + M + 1)); case_eq (f (j + M + 1));
  try (intros u q0 v q1; now rewrite q0, q1 in p1).
  + intros.
    assert (i + M + 1 <> j + M + 1) by omega.
    assert (f (i + M + 1) = f (j + M + 1)).
    { rewrite H, H0 in p1. inversion p1. subst. now transitivity (inl (B:=Y) x). }
    pose (r := existT _ (i + M + 1) (exist2 _ _ (j + M + 1) H1 H2): repetition f).
    refine (exist _ (Aux_rep _ r) _). simpl.
    case (Nat.compare_spec i j); intro;
      [ subst;rewrite Nat.max_id
      | rewrite Nat.max_r by omega
      | rewrite Nat.max_l by omega
      ]; omega.
  + intros. refine (exist _ (Aux_right _ _ _ (eq_sym H0)) _).
    simpl. omega.
Qed.

Definition strict_incr (f : nat -> nat) :=
  forall n, f n < f (S n).

Lemma f_nat_incr {f: nat -> nat}:
  strict_incr f -> forall m, f 0 < f (S m).
Proof.
  intros I.
  induction m; [pose (I 0)|pose (I (S m))]; omega.
Qed.

Lemma f_nat_incr_neq {f: nat -> nat}:
  strict_incr f -> forall {n m}, n <> m -> f n <> f m.
Proof.
  intros I n m.
  case (Nat.compare_spec n m); [now intros| |]; intros t _. 
  + assert (strict_incr (fun i => f (n + i))) as I'.
    { intro i. now replace (n + S i) with (S (n + i)) by omega. }
    replace n with (n + 0) by omega.
    replace m with (n + S (m - n - 1)) by omega.
    apply Nat.lt_neq, (f_nat_incr I').
  + assert (strict_incr (fun i => f (m + i))) as I'.
    { intro i. now replace (m + S i) with (S (m + i)) by omega. }
    replace m with (m + 0) by omega.
    replace n with (m + S (n - m - 1)) by omega.
    apply Nat.neq_sym, Nat.lt_neq, (f_nat_incr I').
Qed.

Lemma aux_with_bounds {X Y: Set} (f: nat -> X + Y) (sx: streamless X):
  {g: nat -> AuxT f | forall n m, n <> m -> AuxT_bnd (g n) <> AuxT_bnd (g m)}.
Proof.
  destruct (dependent_choice
    (fun a => aux f sx (AuxT_bnd a))
    (proj1_sig (aux f sx 0))) as [g [_ p]].
  exists g.
  intros n m neq.
  case (Nat.compare_spec n m); try contradiction;
  intros; exact (f_nat_incr_neq p neq).
Qed.

Theorem streamless_sum {X Y}:
  streamless X -> streamless Y -> streamless (X + Y).
Proof.
  intros sx sy f.
  destruct (aux_with_bounds f sx) as [g pg].
  destruct (option_streamless sy
    (fun n => match g n with
      | Aux_rep _ _ => None
      | Aux_right _ _ y _ => Some y
    end)
  ) as [i [j p0 p1]].
  pose (pg i j p0).
  case_eq (g i); case_eq (g j); try now intros.
  intros u y0 pu eq0 v y1 pv eq1.
  rewrite eq0, eq1 in p1, n.
  exists u, v; [auto|].
  inversion p1. subst. now transitivity (inr (A:=X) y0).
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
