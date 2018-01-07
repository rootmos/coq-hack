Require Import Hack.CMP.Fun.
Require Import Hack.CMP.Fin.
Require Import Basics.
Open Scope program_scope.

Lemma shuffle {n}: forall x: Fin (S n),
  {s: Fin (S n) -> Fin (S n) & bij s & s x = inl tt}.
Proof.
  induction n.
  - intro x.
    exists id. split.
    + intros u u' H. compute in H. assumption.
    + intro v. exists v. compute. reflexivity.
    + case x; intro u; case u; reflexivity.
  - intro x. case_eq x.
    + intros u H. dependent inversion u.
      exists id. split.
      ++ intros v v' G. compute in G. assumption.
      ++ intro v. exists v. compute. reflexivity.
      ++ compute. reflexivity.
    + intros f H.
      destruct (IHn f) as [t [ti ts] qt].
      pose (flip := fun (y: Fin (S (S n))) => match y with
        | inl _ => inr (inl tt)
        | inr (inl _) => inl tt
        | inr (inr z) => inr (inr z)
      end).
      assert (bij flip) as flip_bij.
      {
        split.
        + intros u u' G.
          case u, u' in *.
          ++ case u, u0 in *. reflexivity.
          ++ case f0 in *; compute in G; discriminate G.
          ++ case f0 in *; compute in G; discriminate G.
          ++ case f0, f1 in *; compute in G; try discriminate G.
             +++ case u, u0. reflexivity.
             +++ assumption.
        + intro y. case y in *.
          ++ exists (inr (inl tt)). compute. case u. reflexivity.
          ++ case s.
             +++ intro u. exists (inl tt). compute. case u. reflexivity.
             +++ intro f0. exists (inr (inr f0)). compute. reflexivity.
      }
      pose (extend := fun (y: Fin (S (S n))) => match y with
        | inl _ => inl tt
        | inr z => inr (t z)
      end).
      assert (bij extend) as extend_bij.
      {
        split.
        + intros u u' G.
          case u, u' in *; compute in G; try discriminate G.
          ++ case u, u0. reflexivity.
          ++ apply (fin_inr_inj (t f0) (t f1)), ti in G.
             rewrite G. reflexivity.
        + intro y. case y.
          ++ intro u. exists (inl tt). compute. case u. reflexivity.
          ++ intro f0. destruct (ts f0) as [x0 x0p]. exists (inr x0).
             compute. rewrite x0p. reflexivity.
      }
      exists (flip ∘ extend).
      ++ apply compose_bij; assumption.
      ++ compute. rewrite qt. reflexivity.
Qed.

Lemma shave {n m}:
  forall f: Fin (S n) -> Fin (S m),
  inj f ->
  f (inl tt) = inl tt -> {g | forall x, (inr ∘ g) x = (f ∘ inr) x}.
Proof.
  intros f I H.
  assert (forall x, {y | f (inr x) = inr y}) as F.
  {
    intro x.
    case (fin_dec (f (inr x)) (inl tt)).
    + intro G.
      compute in G, H.
      rewrite <- G in H.
      discriminate (I _ _ H).
    + intro G.
      case_eq (f (inr x)).
      - intros u U0. case u in U0. contradiction.
      - intros f0 F0. exists f0. reflexivity.
  }
  exists (fun x => proj1_sig (F x)).
  intro x.
  compute.
  pose (F x).
  replace (F x) with s by reflexivity.
  destruct s.
  symmetry. assumption.
Qed.

Theorem inj_to_surj {n}: forall f: Fin n -> Fin n, inj f -> surj f.
Proof.
  intros f fi y.
  induction n.
  - case y.
  - destruct (shuffle (f (inl tt))) as [s [si ss] ps].
    destruct (shave (s ∘ f) (compose_inj _ _ _ _ _ fi si) ps) as [g pg].
    fold Fin in *.
    assert (inj g) as gi.
    {
      intros x x' H.
      unfold compose in *.
      pose (gx := pg x).
      rewrite H, (pg x') in gx.
      apply si, fi, fin_inr_inj in gx.
      symmetry. assumption.
    }
    case_eq (s y).
    + intros u H. exists (inl u). case u in *.
      rewrite <- ps in H.
      apply si. symmetry. assumption.
    + intros x' H.
      destruct ((IHn g gi) x') as [x px].
      exists (inr x).
      rewrite <- px in H.
      unfold compose in pg.
      rewrite (pg x) in H.
      apply si in H. symmetry. assumption.
Qed.

Theorem surj_to_inj {n}: forall f : Fin n -> Fin n, surj f -> inj f.
Proof.
  intros f fs.
  pose (g := fun y => projT1 (fs y)).
  assert (inj g) as gi.
  {
    intros y y' G. unfold g in G.
    destruct (fs y), (fs y').
    compute in G. rewrite G in e.
    transitivity (f x0); [symmetry|]; assumption.
  }
  pose (inj_to_surj g gi) as gs.
  assert (forall y, f (g y) = y) as H.
  { intro y. unfold g. destruct (fs y). compute. assumption.  }
  intros x x' G.
  destruct (gs x) as [y py]. rewrite <- py, (H y) in G.
  destruct (gs x') as [y' py']. rewrite <- py', (H y') in G.
  transitivity (g y'); [rewrite G in py; symmetry|]; assumption.
Qed.
