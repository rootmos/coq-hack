Require Import Hack.CMP.Fun.
Require Import PeanoNat.
Require Import Basics.
Require Import List.
Open Scope program_scope.

Fixpoint Fin(n : nat): Set :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Record Image {X Y} (f: X->Y) fX := mkImage {
  f' : X -> fX;
  f'_surj : surj f';
  emb : fX -> Y;
  emb_inj : inj emb;
  comp: forall x, (compose emb f') x = f x;
}.

Lemma vacuous_f: forall Y, Empty_set -> Y.
Proof.
  intros Y a. case a.
Qed.

Lemma vacuous_f_inj {Y}: forall f: Empty_set -> Y, inj f.
Proof.
  intros f x. case x.
Qed.

Lemma vacuous_f_surj {X}: forall f: X -> Empty_set, surj f.
Proof.
  intros f y. case y.
Qed.

Lemma image_dec' {Y n}:
  forall f: Fin n -> Y,
  forall y, (forall x, {f x = y} + {f x <> y}) ->
  {x | f x = y} + {forall x, f x <> y}.
Proof.
  intros f.
  induction n.
  - right. destruct x.
  - intros y D.
    case (IHn (compose f inr) y (fun x => D (inr x))).
    + intros [x px]. left. exists (inr x). assumption.
    + intro H.
      case (D (inl tt)).
      ++ intro. left. exists (inl tt). assumption.
      ++ right. destruct x; [case u; assumption | apply H].
Qed.

Lemma image_dec {Y n}:
  (forall y y': Y, {y = y'} + {y <> y'}) ->
  forall f: Fin n -> Y,
  forall y, {x | f x = y} + {forall x, f x <> y}.
Proof.
  intros D f y. exact (image_dec' f y (fun x => D (f x) y)).
Qed.

Definition collision {X Y} (f: X -> Y) :=
  {p: X*X & f (fst p) = f (snd p) & (fst p) <> (snd p)}.

Lemma collision_inr {n Y} {f: Fin (S n) -> Y}:
  collision (compose f (inr: Fin n -> Fin (S n))) -> collision f.
Proof.
  intros [(x, x') P Q].
  exists (inr x, inr x').
  + simpl.
    unfold compose in P.
    simpl in P.
    exact P.
  + simpl. simpl in P.
    contradict Q.
    injection Q.
    intro. assumption.
Qed.

Lemma f_fin_dom_fin_codom {Y n}:
  forall f: Fin n -> Y,
  (forall x x', {f x = f x'} + {f x <> f x'}) ->
  {p: nat * (list (collision f))
    & Image f (Fin (fst p))
    & (fst p) + (length (snd p)) = n }.
Proof.
  intros f D.
  induction n.
  - exists (0, nil). all: swap 1 2. { reflexivity. }
    pose (f' := vacuous_f Empty_set).
    pose (f'_surj := vacuous_f_surj f').
    pose (emb := vacuous_f Y).
    pose (emb_inj := vacuous_f_inj emb).
    refine (mkImage _ _ f Empty_set f' f'_surj emb emb_inj _). { intro x. case x. }
  - pose (D_r := fun x x' => D (inr x) (inr x')).
    destruct (IHn (compose f inr) D_r) as [(m, col) [f' f's e ei c] l].
    pose (y := f (inl tt)).
    assert(forall x, {e x = y} + {e x <> y}) as D'.
    {
      intro x.
      destruct (f's x) as [v pv].
      rewrite <- pv.
      unfold compose in c.
      rewrite (c v).
      replace y with (f (inl tt)) by trivial.
      apply D.
    }
    fold Fin in *.
    case (image_dec' e y D').
    -- intros [x fsn'_p].
       destruct (f's x) as [x0 x0p].
       assert (C: collision f).
       {
         exists (inl tt, inr x0).
         + unfold compose in c.
           pose (c x0).
           simpl.
           rewrite <- (c x0).
           replace (f (inl tt)) with y by reflexivity.
           rewrite x0p.
           symmetry.
           assumption.
         + discriminate.
       }
       exists (m, cons C (List.map collision_inr col)). all: swap 1 2.
       {
         simpl. simpl in l.
         rewrite List.map_length.
         rewrite Nat.add_succ_r.
         apply eq_S.
         assumption.
       }
       pose (f'_e := fun (n: Fin (S n)) => match n with inl _ => x | inr m => f' m end).
       assert (surj f'_e) as f'_es.
       { intro y'. destruct (f's y') as [x' px]. exists (inr x'). assumption. }
       assert (forall x, compose e f'_e x = f x) as c_e.
       {
         intro x'. case x'.
         + intro. compute.
           rewrite fsn'_p.
           replace u with tt; [ reflexivity | case u; reflexivity ].
         + apply c.
       }
       exact (mkImage _ _ f _ f'_e f'_es e ei c_e).
    -- intro H.
       exists (S m, List.map collision_inr col). all: swap 1 2.
       { simpl. rewrite List.map_length. simpl in l. rewrite l. reflexivity. }
       pose (f'' := fun (x: Fin (S n)) =>
         match x with
         | inl _ => inl tt
         | inr m => inr (f' m)
       end).
       pose (e' := fun (x: Fin (S m)) =>
         match x with
         | inl _ => f (inl tt)
         | inr m => e m
       end).
       assert (surj f'') as f''_s.
       {
         intro y'. case y'.
         + destruct u. exists (inl tt). reflexivity.
         + intro v.
           destruct (f's v) as [v' pv'].
           exists (inr v'). compute. rewrite pv'. reflexivity.
       }
       assert (inj e') as e'_i.
       {
         intros x x'. case x, x'.
         + intros. case u, u0. reflexivity.
         + intros. contradiction (H f0). symmetry. assumption.
         + intros. contradiction (H f0).
         + intros G. rewrite (ei _ _ G). reflexivity.
       }
       assert (forall x, compose e' f'' x = f x) as c'.
       { destruct x; [case u | apply c]; reflexivity. }
       exact (mkImage _ _ f (Fin (S m)) f'' f''_s e' e'_i c').
Qed.

Lemma f_inj_dec {X Y}: forall f: X -> Y,
  (forall x x': X, {x = x'} + {x <> x'}) -> inj f ->
  (forall x x', {f x = f x'} + {f x <> f x'}).
Proof.
  intros f D i x x'.
  case (D x x').
  + destruct 1. left. reflexivity.
  + intro n. right. intro. apply n, i. assumption.
Qed.

Lemma fin_dec {n}: forall x x': Fin n, {x = x'} + {x <> x'}.
Proof.
  induction n.
  - intro x. case x.
  - intros x x'.
    dependent inversion x.
    -- dependent inversion x'.
       + left. case u, u0. reflexivity.
       + right. discriminate.
    -- dependent inversion x'.
       + right. discriminate.
       + case (IHn f f0).
         ++ intro e. left. rewrite e. reflexivity.
         ++ intro n0. right. injection. assumption.
Qed.

Lemma f_inj_fin_dom_fin_codom {Y n}: forall f: Fin n -> Y, inj f -> Image f (Fin n).
Proof.
  intros f I.
  destruct (f_fin_dom_fin_codom f (f_inj_dec f fin_dec I)) as [(m, col) i p].
  inversion i as [f' f's e ei c].
  simpl in p.
  case_eq col.
  - intro cn.
    rewrite cn in p.
    simpl in p.
    rewrite Nat.add_0_r in p.
    simpl in i.
    rewrite p in i.
    exact i.
  - intros.
    assert (inj f') as f'i.
    {
      intros x x' G.
      unfold inj in I.
      pose ((f_equal e) (f' x) (f' x')) as F.
      unfold compose in c.
      rewrite c, c in F.
      exact (I _ _ (F G)).
    }
    inversion c0 as [(x, x') P Q].
    simpl in P, Q.
    rewrite <- (c x), <- (c x') in P.
    unfold compose in P.
    contradiction (f'i _ _ (ei (f' x) (f' x') P)).
Qed.

Lemma shuffle {n}: forall x: Fin (S n),
  {s: Fin (S n) -> Fin (S n) & bij s & s x = inl tt}.
Admitted.

Lemma shave {n m}:
  forall f: Fin (S n) -> Fin (S m),
  f (inl tt) = inl tt -> {g | forall x, (inr ∘ g) x = (f ∘ inr) x}.
Admitted.

Lemma inr_inj {n}: inj (inr: Fin n -> Fin (S n)).
Proof.
  intros x x' H. injection H. intro. assumption.
Qed.

Theorem inj_to_surj {n}: forall f: Fin n -> Fin n, inj f -> surj f.
Proof.
  intros f I y.
  induction n.
  - case y.
  - destruct (shuffle (f (inl tt))) as [s [si ss] ps].
    destruct (shave (s ∘ f) ps) as [g pg].
    fold Fin in *.
    assert (inj g) as gi.
    {
      intros x x' H.
      unfold compose in *.
      pose (pg x) as gx.
      pose (pg x') as gx'.
      rewrite H, gx' in gx.
      apply si in gx.
      apply I in gx.
      apply inr_inj in gx.
      symmetry. assumption.
    }
    case_eq (s y).
    + intros u H. exists (inl u). case u in *.
      rewrite <- ps in H.
      apply si.
      symmetry. assumption.
    + intros x' H.
      destruct ((IHn g gi) x') as [x px].
      exists (inr x).
      rewrite <- px in H.
      unfold compose in pg.
      rewrite (pg x) in H.
      apply si in H.
      symmetry. assumption.
Qed.

Lemma f_fin_codom_eq_surj {X n}: forall f: X -> Fin n, Image f (Fin n) -> surj f.
Proof.
  intros f [f' f's e ei c] y.
  case (image_dec fin_dec e y).
  - intros [x' p'].
    destruct (f's x') as [x p].
    exists x.
    unfold compose in c.
    rewrite <- (c x).
    rewrite p.
    assumption.
  - intro.
    pose (inj_to_surj e ei) as es.
    destruct ((compose_surj _ _ _ _ _ f's es) y) as [x px].
    exists x.
    rewrite <- (c x).
    assumption.
Qed.

Theorem inj_to_surj_alt_proof {n}: forall f: Fin n -> Fin n, inj f -> surj f.
Proof.
  intros f inj.
  exact (f_fin_codom_eq_surj _ (f_inj_fin_dom_fin_codom f inj)).
Qed.

Lemma f_fin_surj_codom {X n}: forall f: X -> Fin n, surj f -> Image f (Fin n).
Admitted.

Lemma f_fin_surj_dom_eq {Y n}: forall f: Fin n -> Y, Image f (Fin n) -> inj f.
Admitted.

Theorem surj_to_inj {n}: forall f : Fin n -> Fin n, surj f -> inj f.
Proof.
  intros f surj.
  exact (f_fin_surj_dom_eq _ (f_fin_surj_codom f surj)).
Qed.

Lemma f_bij_fin {n m}: forall f: Fin n -> Fin m, bij f -> n = m.
Admitted.

Lemma f_bij_fin' {n}: forall f: Fin n -> Fin n, bij f.
Admitted.
