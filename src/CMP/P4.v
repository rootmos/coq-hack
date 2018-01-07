Require Import Hack.CMP.Fun.
Require Import Hack.CMP.Fin.
Require Import Basics.
Open Scope program_scope.

Definition flip {n} := fun (y: Fin (S (S n))) => match y with
| inl _ => inr (inl tt)
| inr (inl _) => inl tt
| inr (inr z) => inr (inr z)
end.

Lemma flip_bij {n}: bij (flip (n:=n)).
Proof.
  split.
  + intros u u' G.
    case u, u' in *; try (case f in *; discriminate G).
      ++ case u, u0 in *. reflexivity.
      ++ case f, f0 in *; try discriminate G; [case u, u0|]; auto.
  + intro y. case y in *.
    ++ case u. exists (inr (inl tt)). reflexivity.
    ++ case s.
       +++ intro u. case u. exists (inl tt). reflexivity.
       +++ intro f0. exists (inr (inr f0)). reflexivity.
Qed.

Definition extend {n} (t: Fin n -> Fin n) :=
  fun (y: Fin (S n)) => match y with
| inl _ => inl tt
| inr z => inr (t z)
end.

Lemma extend_inj {n} {t: Fin n -> Fin n}:
  inj t -> inj (extend t).
Proof.
  intro ti.
  intros u u' G.
  case u, u' in *; try discriminate G.
  + case u, u0. reflexivity.
  + apply fin_inr_inj, ti in G. rewrite G. reflexivity.
Qed.

Lemma extend_surj {n} {t: Fin n -> Fin n}:
  surj t -> surj (extend t).
Proof.
  intros ts y. case y.
  + intro u. exists (inl tt). case u. reflexivity.
  + intro f0. destruct (ts f0) as [x0 x0p]. exists (inr x0).
    compute. rewrite x0p. reflexivity.
Qed.

Lemma extend_bij {n} {t: Fin n -> Fin n}:
  bij t -> bij (extend t).
Proof.
  intros [ti ts].
  constructor 1; [apply extend_inj| apply extend_surj]; assumption.
Qed.

Lemma shuffle {n}: forall x: Fin (S n),
  {s: Fin (S n) -> Fin (S n) & bij s & s x = inl tt}.
Proof.
  induction n.
  - intro x.
    exists id. all: cycle 1. {case x; intro u; case u; reflexivity. }
    split; [intros u u' H | intro v; exists v]; trivial.
  - intro x. case_eq x.
    + intros u H. dependent inversion u.
      exists id. all: cycle 1. trivial.
      split; [intros v v' G| intro v; exists v]; trivial.
    + intros f H.
      destruct (IHn f) as [t tb qt].
      pose (flip_bij (n:=n)).
      pose (extend_bij tb).
      exists (flip ∘ (extend t));
        [apply compose_bij| compute; rewrite qt]; trivial.
Qed.

Lemma shave {n m}:
  forall f: Fin (S n) -> Fin (S m),
  inj f -> f (inl tt) = inl tt ->
  {g | forall x, (inr ∘ g) x = (f ∘ inr) x & inj g }.
Proof.
  intros f I H.
  assert (forall x, {y | f (inr x) = inr y}) as F.
  {
    intro x.
    case (fin_dec (f (inr x)) (inl tt)).
    + intro G. rewrite <- G in H.
      discriminate (I _ _ H).
    + intro G.
      case_eq (f (inr x)).
      - intros u U0. case u in U0. contradiction.
      - intros f0 _. exists f0. reflexivity.
  }
  pose (g := fun x => proj1_sig (F x)).
  assert (forall x, inr (g x) = f (inr x)) as pg.
  {
    intro x.
    compute.
    pose (s := F x). replace (F x) with s by reflexivity.
    destruct s. symmetry. assumption.
  }
  exists g; [assumption|].
  intros x x' G.
  apply fin_inr_inj, I.
  fold Fin in pg.
  rewrite <- (pg x), <- (pg x'), G.
  reflexivity.
Qed.

Theorem inj_to_surj {n}: forall f: Fin n -> Fin n, inj f -> surj f.
Proof.
  intros f fi y.
  induction n.
  - case y.
  - destruct (shuffle (f (inl tt))) as [s [si ss] ps].
    destruct (shave (s ∘ f) (compose_inj _ _ _ _ _ fi si) ps) as [g pg gi].
    fold Fin in *.
    case_eq (s y).
    + intros u H. exists (inl u). case u in *.
      rewrite <- ps in H.
      apply si. symmetry. assumption.
    + intros x' H.
      destruct ((IHn g gi) x') as [x px].
      exists (inr x).
      unfold compose in pg.
      rewrite <- px, (pg x) in H.
      apply si. symmetry. assumption.
Qed.

Theorem surj_to_inj {n}: forall f : Fin n -> Fin n, surj f -> inj f.
Proof.
  intros f fs.
  intros x x' G.
  destruct (right_inv fs) as [g H gi].
  pose (inj_to_surj g gi) as gs.
  destruct (gs x) as [y py]. rewrite <- py, (H y) in G.
  destruct (gs x') as [y' py']. rewrite <- py', (H y') in G.
  transitivity (g y'); [rewrite G in py; symmetry|]; assumption.
Qed.
