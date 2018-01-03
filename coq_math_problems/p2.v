Require Import PeanoNat.
Require Import Arith.Compare_dec.

Require CMP.Arith.
Require Import CMP.Decr.
Require Import CMP.Translation.

Definition LPO :=
  forall f : nat -> bool,
  (exists x, f x = true) \/ (forall x, f x = false).

Definition infvalley(f : nat -> nat)(x : nat) := forall y, x <= y -> f y = f x.

Lemma f_bool_to_nat:
  forall f: nat -> bool, exists g: nat -> nat,
  forall n, (f n = true /\ g n = 1) \/ (f n = false /\ g n = 0).
Proof.
  intro f.
  refine (ex_intro _ (fun n => if f n then 1 else 0) _).
  intro n.
  case (f n). +auto. +auto.
Qed.

Definition f_has_a_true(f: nat -> bool) := exists x, f x = true.
Definition f_false(f: nat -> bool) := forall x, f x = false.

Lemma LPO_disjoint f:
  (f_has_a_true f -> ~ f_false f) /\ (f_false f -> ~ f_has_a_true f).
Proof.
  split.
  + intros H G.
    destruct H as [x px].
    rewrite (G x) in px.
    discriminate.
  + intros H G.
    destruct G as [x px].
    rewrite (H x) in px.
    discriminate.
Qed.

Lemma infvalley_LPO_aux:
  forall f: nat -> bool, exists g: nat -> nat,
  (forall n,
    (g n = 1 /\ (forall x, x <= n -> f x = false))
    \/ (g n = 0 /\ (exists x, f x = true)))
  /\ decr g.
Proof.
  intro f.
  refine (ex_intro _ (fun n => (* TODO *) n) _).
  split.
  + admit.
  + admit.
Admitted.

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Proof.
  intro H.
  intro f.
  destruct (infvalley_LPO_aux f) as [g pg].
  destruct pg as [p Dg].
  destruct (H g Dg) as [n pn].
  case_eq (g n =? 1).
  + intro G1.
    right.
    intro x.
    unfold infvalley in pn.
    case_eq (le_ge_dec x n).
    -- intros l _.
       case (p n).
       ++ intro F.
          destruct F as [_ F].
          exact (F x l).
       ++ intro F.
          destruct F as [F _].
          rewrite (proj1 (Nat.eqb_eq _ _) G1) in F.
          discriminate.
    -- intros ge _.
       case (p x).
       ++ intro F.
          destruct F as [_ F].
          exact (F x (le_n _)).
       ++ intro F.
          destruct F as [F _].
          rewrite (pn x ge) in F.
          rewrite (proj1 (Nat.eqb_eq _ _) G1) in F.
          discriminate.
  + intro Gn1.
    left.
    case (p n).
    -- intro F.
       destruct F as [F _].
       rewrite (proj2 (Nat.eqb_eq _ _) F) in Gn1.
       discriminate.
    -- intro F.
       destruct F as [_ F].
       assumption.
Qed.

Lemma f_at_level:
  forall f: nat -> nat, forall x, exists g: nat -> bool,
  forall n, (f n = x /\ g n = false) \/ (f n <> x /\ g n = true).
Proof.
  intros f x.
  refine (ex_intro _ (fun n => negb (f n =? x)) _).
  intro n.
  case (Nat.eq_dec (f n) x).
  + intro H.
    left.
    refine (conj H _).
    rewrite (proj2 (Nat.eqb_eq _ _) H).
    trivial.
  + intro H.
    right.
    refine (conj H _).
    case_eq (f n =? x).
    - intro G; contradiction (proj1 (Nat.eqb_eq _ _) G).
    - trivial.
Qed.


Lemma infvalley_if_bounded_by_0: forall f,
  (forall x, f x <= 0) -> exists x, infvalley f x.
Proof.
  intros f B0.
  refine (ex_intro _ 0 _).
  unfold infvalley.
  intros y _.
  transitivity 0.
  - exact (proj1 (Nat.le_0_r _) (B0 y)).
  - symmetry.
    exact (proj1 (Nat.le_0_r _) (B0 0)).
Qed.

Lemma LPO_infvalley_aux:
  LPO -> forall m f, decr f ->
  (forall x, f x <= m) ->
  exists x, infvalley f x.
Proof.
  intro LPO.
  induction m.
  -- intros f D.
     exact (infvalley_if_bounded_by_0 f).
  -- intros f D BSm.
     destruct (f_at_level f (S m)) as [g pg].
     case (LPO g).
     + intro T.
       destruct T as [x px].
       case (pg x).
       - intro H.
         rewrite px in H.
         destruct H.
         discriminate.
       - intro H.
         destruct H as [G _].
         pose (q := Arith.leq_and_not' _ _ (BSm x) G).
         destruct (translate f x) as [f' tr].
         pose (D' := decr_translation f f' x D tr).
         pose (f'Bm := decr_translation_estimate f f' x m D tr q).
         destruct (IHm f' D' f'Bm) as [n pn].
         refine (ex_intro _ (n + x) _).
         intros y I.
         rewrite (tr n).
         rewrite <- (pn (y - x) (Arith.le_sub _ _ _ I)).
         rewrite <- (tr (y - x)).
         apply f_equal_nat.
         exact (Arith.le_sub_ident _ _ _ I).
     + intros F.
       refine (ex_intro _ 0 _).
       unfold infvalley.
       intros y _.
       transitivity (S m).
       - case (pg y).
         * apply (proj1).
         * intro H.
           pose (q := F y).
           rewrite (proj2 H) in q.
           discriminate.
       - symmetry.
         case (pg 0).
         * apply (proj1).
         * intro H.
           pose (q := F 0).
           rewrite (proj2 H) in q.
           discriminate.
Qed.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Proof.
  intros LPO f D.
  assert (forall y, f y <= f 0) as B.
  - intro y.
    exact (decr_estimate f D 0 y (le_0_n _)).
  - exact (LPO_infvalley_aux LPO (f 0) f D B).
Qed.
