Require Import PeanoNat.

Definition LPO :=
  forall f : nat -> bool,
  (exists x, f x = true) \/ (forall x, f x = false).

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.
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

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Proof.
Admitted.

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

(* TODO: extract and make a small common lib *)
Lemma leq_and_not: forall x y, x <= S y -> x = S y \/ x <= y.
Proof.
  intro x.
  case x.
  + right.
    exact (le_0_n _).
  + intros n y H.
    case (le_S_n _ _ H).
    - left.
      reflexivity.
    - right.
      apply le_n_S.
      assumption.
Qed.

Lemma leq_and_not': forall x y, x <= S y -> x <> S y -> x <= y.
Proof.
  intros x y H.
  case (leq_and_not _ _ H).
  - contradiction.
  - intros.
    assumption.
Qed.

Theorem decr_estimate: forall f, decr f -> forall x y, x <= y -> f y <= f x.
Proof.
  intros f D x.
  induction y.
  + intro.
    rewrite (proj1 (Nat.le_0_r _) H).
    apply le_n.
  + intro.
    case (Nat.eq_dec x (S y)).
    - intro.
      rewrite e.
      apply le_n.
    - intro.
      pose (p := IHy (leq_and_not' _ _ H n)).
      pose (q := D y).
      Nat.order.
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

Definition translation(f g:nat -> nat)(n: nat) := forall x, f (x + n) = g x.

Lemma translate: forall f n, exists g, translation f g n.
Admitted.

Lemma arith_lemma_1: forall n x y, n + x <= y -> n <= y - x.
Proof.
  intros n x y H.
  assert (x <= y).
  - pose (p := Nat.add_le_mono 0 n x x (le_0_n _) (le_n _)).
    Nat.order.
  - assert (y = y - x + x) as H1.
    + symmetry.
      exact (Nat.sub_add x y H0).
    + rewrite H1 in H.
      rewrite (Nat.add_comm n x) in H.
      rewrite (Nat.add_comm (y - x) x) in H.
      exact (proj2 (Nat.add_le_mono_l n (y-x) x) H).
Qed.

Lemma arith_lemma_2: forall n x y, n + x <= y -> y = y - x + x.
Proof.
  intros n x y H.
  assert (x <= y) as H0.
  - pose (p := Nat.add_le_mono 0 n x x (le_0_n _) (le_n _)).
    Nat.order.
  - symmetry.
    exact (Nat.sub_add x y H0).
Qed.

Lemma decr_translation: forall f g n, decr f -> translation f g n -> decr g.
Admitted.

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
         pose (q := leq_and_not' _ _ (BSm x) G).
         destruct (translate f x) as [f' tr].
         pose (D' := decr_translation f f' x D tr).
         assert (forall y, f' y <= m) as f'Bm.
         ++ intro y.
            rewrite <- (tr y).
            pose (s := decr_estimate f D x (x+y) (Nat.le_add_r x y)).
            rewrite (Nat.add_comm y x).
            Nat.order.
         ++ destruct (IHm f' D' f'Bm) as [n pn].
            refine (ex_intro _ (n + x) _).
            intros y I.
            rewrite (tr n).
            rewrite <- (pn (y - x) (arith_lemma_1 _ _ _ I)).
            rewrite <- (tr (y - x)).
            apply f_equal_nat.
            exact (arith_lemma_2 _ _ _ I).
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
