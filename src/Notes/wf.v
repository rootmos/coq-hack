Require Import Hack.CMP.Fun.

Definition subst X0 X := {f: X0 -> X | inj f}.

(* from Wikipedia: https://en.wikipedia.org/wiki/Well-founded_relation *)
Definition wiki_wf {X} (R: X -> X -> Prop) :=
  forall S, forall i: subst S X, S ->
  exists m: S, forall s: S,
  ~ (R (proj1_sig i s) (proj1_sig i m)).

Lemma l0 {X} {R: X -> X -> Prop}: forall x, R x x -> ~ well_founded R.
Proof.
  intros x px H.
  pose (H x).
  induction a.
  now pose (H1 x px px).
Qed.

Lemma l0' {X} {R: X -> X -> Prop}: well_founded R -> forall x, ~ R x x.
Proof.
  intros wf x.
  contradict wf.
  exact (l0 x wf).
Qed.

Lemma singleton {X}: forall x: X,
  {s: subst unit X | proj1_sig s tt = x}.
Proof.
  intro x.
  pose (i := fun u: unit => x).
  assert (inj i) as ii. { intros u0 u1 H. now destruct u0, u1. }
  now exists (exist _ i ii).
Qed.

Lemma l1 {X} {R: X -> X -> Prop}: (exists x, R x x) -> ~ wiki_wf R.
Proof.
  intros [x px] H.
  unfold wiki_wf in H.
  destruct (singleton x) as [s G].
  destruct (H unit s tt).
  pose (H0 tt).
  destruct s.
  destruct x0.
  now rewrite G in n.
Qed.

Lemma well_founded_subset {X X0} {R: X -> X -> Prop}:
  well_founded R -> forall s: subst X0 X,
  {R0: X0 -> X0 -> Prop & well_founded R0 &
    forall x y, R (proj1_sig s x) (proj1_sig s y) = R0 x y}.
Proof.
  intros wf [s si].
  pose (R0 := fun x y => R (s x) (s y)).
  exists R0.
  + intro a0.
    pose (a := s a0). assert (a = s a0) by reflexivity.
    generalize a, a0, H.
    apply (well_founded_induction_type wf
      (fun x => forall x0, x = s x0 -> Acc R0 x0)).
    intros x G x0 eq.
    apply Acc_intro. intros y r.
    pose (G (s y)).
    rewrite eq in a1.
    unfold R0 in r.
    now apply (a1 r y).
  + easy.
Qed.

Require Import Classical.

Theorem t0 {X} {R: X -> X -> Prop}:
  well_founded R -> wiki_wf R.
Proof.
  intros H S s s0.
  destruct (well_founded_subset H s) as [R0 pR0].
  destruct s as [i pi].
  apply (not_all_not_ex _ (fun m => forall s0, ~ R (i s0) (i m))).
  intro H0.
  assert (forall s, exists y, R (i y) (i s)).
  {
    intro x.
    destruct (not_all_ex_not _ _ (H0 x)) as [y py].
    apply NNPP in py.
    now exists y.
  }
  pose (pR0 s0) as a.
  induction a.
  destruct (H1 x).
  rewrite e in H4.
  exact (H3 _ H4).
Qed.
