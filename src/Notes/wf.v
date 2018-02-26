(* Proof of equivalence between two definitions of a well-founded relation:
 *   - Coq's (https://coq.inria.fr/library/Coq.Init.Wf.html) and
 *   - Wikipedia's (https://en.wikipedia.org/wiki/Well-founded_relation)
 * using classical logic. *)

Require Import Hack.CMP.Fun.
Require Hack.Notes.Process.
Require Coq.Vectors.Fin.
Require Import Classical.
Require Import Omega.

Definition subst X0 X := {f: X0 -> X | inj f}.

(* From Wikipedia: https://en.wikipedia.org/wiki/Well-founded_relation
   My intuition: (non-empty) paths of related elements eventually end *)
Definition wiki_wf {X} (R: X -> X -> Prop) :=
  forall S, forall i: subst S X, S ->
  exists m: S, forall s: S,
  ~ (R (proj1_sig i s) (proj1_sig i m)).

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
    now apply (a1 r y).
  + easy.
Qed.

Theorem coq_wf_imp_wiki_wf {X} {R: X -> X -> Prop}:
  well_founded R -> wiki_wf R.
Proof.
  intros H S s s0.
  destruct (well_founded_subset H s) as [R0 pR0].
  destruct s as [i pi].
  apply not_all_not_ex.
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

(* Given a point that's not accessible, we can point out
 * a related point that's also not accessible *)
Lemma next_non_acc {X} {R: X -> X -> Prop} {a}:
  ~ Acc R a -> exists b: X, R b a /\ ~ Acc R b.
Proof.
  intro n. apply Peirce. intro H. contradict n.
  apply Acc_intro. intros.
  destruct (not_and_or _ _ (not_ex_all_not _ _ H y));
    [contradiction|now apply NNPP].
Qed.

Lemma lift_process_into_sig {X} {R: X -> X -> Prop} (x: {x | ~ Acc R x}):
  exists y: {x | ~ Acc R x}, R (proj1_sig y) (proj1_sig x).
Proof.
  destruct x as [x px].
  destruct (next_non_acc px) as [y [py0 py1]].
  now exists (exist _ y py1).
Qed.

(* Using the above lemmas we can create a sequence of related points
 * starting from a non-accessible point.
 *
 * NB. This lemma relies upon https://coq.inria.fr/library/Coq.Logic.ClassicalChoice.html#choice
 * via Process.process' in order to construct its sequence. *)
Lemma construct_process {X} {R: X -> X -> Prop} {a}:
  ~ Acc R a -> exists f: nat -> X, forall n, R (f (S n)) (f n).
Proof.
  intro na.
  assert ({x | ~ Acc R x}) as A by now exists a.
  destruct (Process.process'
    (R := fun x y => R (proj1_sig y) (proj1_sig x))
    lift_process_into_sig A) as [f pf].
  exists (fun n => proj1_sig (f n)).
  apply pf.
Qed.

(* Given a path in X, let's call it cyclic if all points on the path have a
 * point related to it by R. *)
Definition cyclic {I X} (R: X -> X -> Prop) (i: I -> X) :=
  forall t, exists s, R (i s) (i t).

Definition finitely_cyclic {X} (R: X -> X -> Prop) (n: nat) :=
  {i: Fin.t (S n) -> X | cyclic R i}.

(* remove an element from a Fin.t set *)
Inductive Collapse {n} (x: Fin.t (S (S n))): Set :=
  Collapse_intro:
  forall (f: Fin.t (S (S n)) -> Fin.t (S n)) (g: Fin.t (S n) -> Fin.t (S (S n))),
  (forall z, z <> x -> g (f z) = z) -> Collapse x.

Lemma collapse' (n: nat): Collapse (@Fin.F1 (S n)).
Proof.
  refine (Collapse_intro _
    (fun t => match t with @Fin.F1 (S _) => Fin.F1 | @Fin.FS (S _) s => s end)
    Fin.FS _).
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
    - rewrite e; rewrite Nat.eqb_refl.
      -- now rewrite (proj2 (Fin.eqb_eq _ x x) eq_refl).
      -- now apply not_eq_sym.
    - assert (Fin.eqb x z = false).
      {
        apply Bool.not_true_is_false.
        rewrite Fin.eqb_eq.
        contradict ne.
        now rewrite ne.
      }
      rewrite H. rewrite e; [now rewrite H| discriminate].
Qed.

Lemma Fin1 (u v: Fin.t 1): u = v.
Proof.
  induction u using Fin.caseS';
  induction v using Fin.caseS';
  try reflexivity; now apply Fin.case0.
Qed.

Lemma singleton {X} (x: X): {s: subst unit X | proj1_sig s tt = x}.
Proof.
  pose (i := fun u: unit => x).
  assert (inj i) as ii by (intros u0 u1 H; now destruct u0, u1).
  now exists (exist _ i ii).
Qed.

(* A singleton cycle, ie a point related to itself, contradicts the Wikipedia
 * definition of a well-founded relation. *)
Lemma singleton_cycle_imp_not_wiki_wf {X} {R: X -> X -> Prop} {x}:
  R x x -> ~ wiki_wf R.
Proof.
  intros px H.
  destruct (singleton x) as [s G].
  destruct (H unit s tt) as [y p].
  apply (p tt).
  case y.
  now rewrite G.
Qed.

(* Furthermore, having a finitely cyclic path also contradicts the definition
 * of a well-founded relation. The proof uses the above singleton-lemma as
 * a base case and then inductively removes a point and selects a smaller
 * finitely cyclic subpath. *)
Lemma finitely_cyclic_not_wiki_wf {X} {R: X -> X -> Prop} {n}:
  finitely_cyclic R n -> ~ wiki_wf R.
Proof.
  induction n; intros [i pi] wf.
  + assert (t: Fin.t 1) by constructor.
    destruct (pi t).
    rewrite (Fin1 x t) in H.
    now apply (singleton_cycle_imp_not_wiki_wf H).
  + case (classic (inj i)).
    - intro ii.
      destruct (wf _ (exist _ i ii) Fin.F1) as [s ps].
      destruct (pi s) as [t tp].
      now pose (ps t).
    - intro ni.
      apply not_all_ex_not in ni. destruct ni as [x px].
      apply not_all_ex_not in px. destruct px as [y p].
      contradict p.
      intro H.
      case (Fin.eq_dec x y); try apply id.
      intro ne.
      exfalso.
      destruct (collapse x) as [r ri p0].
      apply IHn; try assumption.
      exists (fun z => i (ri z)).
      intro t.
      destruct (pi (ri t)) as [z pz].
      case (Fin.eq_dec z x); intro e; [exists (r y)|exists (r z)];
          rewrite p0; try assumption.
      -- now rewrite <- H, <- e.
      -- now apply not_eq_sym in ne.
Qed.

(* A small lemma constructing the proof of a finite cyclic path given
 * a sequence of related elements and a repetition in the sequence (ie it
 * associates the repeated values and walks along the sequence). *)
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

(* If we're given the facts that a relation supposedly well-founded over a set
* and a point that is not accessible, then we can construct an infinite
* sequence of related points without repetitions. *)
Lemma construct_infinitely_related_subset {X} {R: X -> X -> Prop} {a}:
  wiki_wf R -> ~ Acc R a ->
  exists f: nat -> X,
  (forall n, R (f (S n)) (f n)) /\ inj f.
Proof.
  intros wf na.
  destruct (construct_process na) as [f pf].
  exists f.
  split; try assumption.
  intros n m H.
  case (Nat.compare_spec n m); try easy; intro lt; [|symmetry in H]; exfalso;
      now apply (finitely_cyclic_not_wiki_wf (construct_cyclic pf _ _ lt H)).
Qed.

(* To prove the direction that Wikipedias definition implies Coq's definition
* of a well-founded relation, we employ reductio ad absurdum and the above
* lemma to derive a direct contradiction against Wikipedia's definition. *)
Theorem wiki_wf_imp_coq_wf {X} {R: X -> X -> Prop}:
  wiki_wf R -> well_founded R.
Proof.
  intro wf.
  apply Peirce.
  intro H.
  destruct (not_all_ex_not _ _ H) as [a pa].
  destruct (construct_infinitely_related_subset wf pa) as [i [pi ii]].
  destruct (wf _ (exist _ i ii) 0) as [m pm].
  pose (pm (S m)). contradiction (pi m).
Qed.
