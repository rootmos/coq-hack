Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.

Definition ded_fin(X : Set) := forall f : X -> X, inj f -> surj f.

Section df_inh_cancel_sgroups.
  Variable X : Set.
  Variable x0 : X.
  Variable m : X -> X -> X.

  Infix "*" := m.

  Hypothesis X_df : ded_fin X.
  Hypothesis assoc : forall x y z, x * (y * z) = (x * y) * z.
  Hypothesis l_cancel : forall x y z, x * y = x * z -> y = z.
  Hypothesis r_cancel : forall x y z, y * x = z * x -> y = z.

  Definition a_X (a: X) (x: X): X := a * x.
  Definition X_a (a: X) (x: X): X := x * a.

  Lemma X_a_inj: forall a, inj (X_a a).
  Proof.
    intros a x x'. compute. exact (r_cancel _ _ _).
  Qed.

  Lemma a_X_inj: forall a, inj (a_X a).
  Proof.
    intros a x x'. compute. exact (l_cancel _ _ _).
  Qed.

  Lemma factorize_r: forall x y, exists! z, x = z * y.
  Proof.
    intros x y.
    pose (p := X_df _ (X_a_inj y) x).
    inversion p as [z H].
    refine (ex_intro _ z _).
    split.
    - symmetry. assumption.
    - intro x'. rewrite <- H. exact (r_cancel _ _ _).
  Qed.

  Lemma factorize_l: forall x y, exists! z, x = y * z.
  Proof.
    intros x y.
    pose (p := X_df _ (a_X_inj y) x).
    inversion p as [z H].
    refine (ex_intro _ z _).
    split.
    - symmetry. assumption.
    - intro x'. rewrite <- H. exact (l_cancel _ _ _).
  Qed.

  (* weak identity element (ie identity element for x) *)
  Definition we (x: X) := exists! e, (x = e * x) /\ (x = x * e).

  Lemma find_we: forall x, we x.
  Proof.
    intro x.
    destruct (factorize_r x x) as [el P]. destruct P as [pel uel].
    assert (el = el * el) as elel.
    - destruct (factorize_r el el) as [z P]. destruct P as [pz uz].
      assert (el * x = z * (el * x)) as H.
      -- rewrite assoc.
         rewrite <- pz.
         trivial.
      -- rewrite <- pel in H.
         rewrite <- (uel z H) in pz.
         assumption.
    - destruct (factorize_l x x) as [er P]. destruct P as [per uer].
      assert (el = er) as eler.
      -- destruct (factorize_l el er) as [z P]. destruct P as [pz uz].
         assert (x * el = (x * er) * z) as H.
         +++ rewrite <- assoc.
             rewrite <- pz.
             trivial.
         +++ rewrite <- per in H.
             rewrite <- (l_cancel _ _ _ H) in pz.
             symmetry in elel.
             exact (r_cancel _ _ _ (eq_trans elel pz)).
      -- refine (ex_intro _ er _).
         split.
         +++ rewrite eler in pel. exact (conj pel per).
         +++ intros f H. destruct H as [fl fr].
             assert (x * er = x * f) as G.
             + transitivity x. ++ symmetry. assumption. ++ assumption.
             + exact (l_cancel _ _ _ G).
  Qed.

  (* the identity *)
  Definition e : X.
  Admitted.

  Theorem l_id : forall x, e * x = x.
  Admitted.

  Theorem r_id : forall x, x * e = x.
  Admitted.

  (* the inverse operation *)
  Definition inv : X -> X.
  Admitted.

  Theorem l_inv : forall x, (inv x) * x = e.
  Admitted.

  Theorem r_inv : forall x, x * (inv x) = e.
  Admitted.

End df_inh_cancel_sgroups.
