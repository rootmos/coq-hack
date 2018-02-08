Require Import Hack.CMP.Fun.
Require Coq.Vectors.Fin.
Require Decidable.
Require Import Classical.
Require Import Omega.

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


Lemma k {X} {R: X -> X -> Prop} {a}:
  ~ Acc R a -> exists b: X, R b a /\ ~ Acc R b.
Proof.
  apply (Decidable.contrapositive _ _ (classic _)).
  intros H n. contradict n.
  apply Acc_intro.
  intros.
  case (not_and_or _ _ (not_ex_all_not _ _ H y)).
  + now intro.
  + apply NNPP.
Qed.

Definition Q {X} (R: X -> X -> Prop) (x y: {x | ~ Acc R x}) := R (proj1_sig y) (proj1_sig x).

Lemma kp_aux {X} {R: X -> X -> Prop}:
  forall x: {x | ~ Acc R x}, exists y: {x | ~ Acc R x}, Q R x y.
Proof.
  intros [x px].
  destruct (k px) as [y [py0 py1]].
  now exists (exist (fun a => ~ Acc R a) y py1).
Qed.

Require Hack.Notes.Process.

Lemma kp {X} {R: X -> X -> Prop} {a}:
  ~ Acc R a -> exists f: nat -> X, forall n, R (f (S n)) (f n).
Proof.
  intro na.
  assert ({x | ~ Acc R x}) as A by now exists a.
  destruct (Process.process' (R:=Q R) kp_aux A) as [f pf].
  exists (fun n => proj1_sig (f n)).
  intro n.
  now pose (pf n).
Qed.

Definition cyclic {I X} (R: X -> X -> Prop) (i: I -> X) :=
  forall t, exists s, R (i s) (i t).

Definition finitely_cyclic {X} (R: X -> X -> Prop) (n: nat) :=
  {i: Fin.t (S n) -> X | cyclic R i}.

Lemma Fin1 (u v: Fin.t 1): u = v.
Proof.
  apply Fin.to_nat_inj.
  destruct (Fin.to_nat u), (Fin.to_nat v).
  compute.
  omega.
Qed.

Inductive Collapse {n} (x: Fin.t (S (S n))): Set :=
  Collapse_intro:
  forall (f: Fin.t (S (S n)) -> Fin.t (S n)) (g: Fin.t (S n) -> Fin.t (S (S n))),
  (forall z, z <> x -> g (f z) = z) -> Collapse x.

Definition fin_cut (n: nat) (t: Fin.t (S (S n))): Fin.t (S n) :=
  match t in Fin.t (S (S m)) return Fin.t (S m) with
  | @Fin.F1 (S _) => Fin.F1
  | @Fin.FS (S _) s => s
  end.

Definition fin_cut' (n: nat) (t: Fin.t (S n)): Fin.t (S (S n)) :=
  match t in Fin.t (S m) return Fin.t (S (S m)) with
  | _ => Fin.FS t
  end.

Definition collapse' (n: nat): Collapse (@Fin.F1 (S n)).
Proof.
  refine (Collapse_intro _  (fin_cut n) (fin_cut' n) _).
  induction z using Fin.caseS'; try auto; contradiction.
Qed.

Lemma collapse {n} (x: Fin.t (S (S n))): Collapse x.
Proof.
  induction x using Fin.caseS'.
  + apply collapse'.
  + pose (s := fun (t: Fin.t (S (S n))) =>
      if Fin.eqb (@Fin.F1 (S n)) t then Fin.FS x else
      if Fin.eqb (Fin.FS x) t then @Fin.F1 (S n) else t).
    destruct (collapse' n) as [f g e].
    refine (Collapse_intro _ (fun t => f (s t)) (fun t => s (g t)) _).
    intros z ne. unfold s. simpl.
    induction z using Fin.caseS'.
    - rewrite e.
      -- now rewrite Nat.eqb_refl, (proj2 (Fin.eqb_eq _ x x) eq_refl).
      -- rewrite Nat.eqb_refl. now apply not_eq_sym.
    - assert (Fin.eqb x z = false).
      {
        apply Bool.not_true_is_false.
        intro eq.
        apply Fin.eqb_eq in eq. apply ne, Fin.FS_inj.
        now rewrite eq.
      }
      rewrite H. rewrite e; [now rewrite H| discriminate].
Qed.

Lemma j' {X} {R: X -> X -> Prop} {n}:
  finitely_cyclic R n -> ~ wiki_wf R.
Proof.
  induction n; intros [i pi] wf.
  + assert (t: Fin.t 1) by constructor.
    destruct (pi t).
    rewrite (Fin1 x t) in H.
    now apply (l1 (ex_intro _ _ H)).
  + case (classic (inj i)).
    - intro ii.
      destruct (wf _ (exist _ i ii) Fin.F1) as [s ps].
      destruct (pi s) as [t tp].
      now pose (ps t).
    - intro ni.
      apply not_all_ex_not in ni.
      destruct ni as [x px].
      apply not_all_ex_not in px.
      destruct px as [y p].
      contradict p.
      intro H.
      case (Fin.eq_dec x y); try apply id.
      intro ne.
      exfalso.
      destruct (collapse x) as [r ri p0].
      assert (finitely_cyclic R n).
      {
        exists (fun z => i (ri z)).
        intro t.
        destruct (pi (ri t)) as [z pz].
        case (Fin.eq_dec z x).
        -- intro e.
           exists (r y).
           rewrite e, H in pz.
           apply not_eq_sym in ne.
           now rewrite p0.
        -- intro. exists (r z). now rewrite p0.
      }
      now apply IHn.
Qed.

Lemma construct_cyclic {X} {R: X -> X -> Prop} {f: nat -> X}:
  (forall n, R (f (S n)) (f n)) ->
  forall n m: nat, n < m -> f n = f m ->
  finitely_cyclic R m.
Proof.
  intros pf n m lt eq.
  exists (fun t => f (proj1_sig (Fin.to_nat t))).
  intro t.
  destruct (Fin.to_nat t) as [x px].
  case (Nat.eq_dec x m).
  - intro xm.
    assert (S n < S m) as lt' by omega.
    exists (Fin.of_nat_lt lt').
    rewrite Fin.to_nat_of_nat.
    compute.
    rewrite xm, <- eq.
    apply pf.
  - intro ne.
    assert (S x < S m) as lt' by omega.
    exists (Fin.of_nat_lt lt').
    rewrite Fin.to_nat_of_nat.
    apply pf.
Qed.

Lemma l {X} {R: X -> X -> Prop} {a}:
  wiki_wf R -> ~ Acc R a ->
  exists f: nat -> X,
  (forall n, R (f (S n)) (f n)) /\ inj f.
Proof.
  intros wf na.
  destruct (kp na) as [f pf].
  exists f.
  split; try assumption.
  intros n m H.
  case (Nat.compare_spec n m); try easy; intro lt; [|symmetry in H];
      exfalso; now apply (j' (construct_cyclic pf _ _ lt H)).
Qed.

Theorem t1 {X} {R: X -> X -> Prop}:
  wiki_wf R -> well_founded R.
Proof.
  intro wf.
  case (classic (well_founded R)).
  + apply id.
  + intro H.
    apply not_all_ex_not in H.
    destruct H as [a pa].
    destruct (l wf pa) as [i [pi ii]].
    destruct (wf _ (exist _ i ii) 0) as [m pm].
    pose (pm (S m)).
    pose (pi m).
    contradiction.
Qed.
