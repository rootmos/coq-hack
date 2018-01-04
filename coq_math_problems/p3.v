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

  Definition urf (x y z: X) := unique (fun z' => x = z' * y) z.
  Definition ulf (x y z: X) := unique (fun z' => x = y * z') z.

  Lemma factorize_r: forall x y, {z | urf x y z }.
  Proof.
    intros x y.
    pose (p := X_df _ (X_a_inj y) x).
    inversion p as [z H].
    exists z.
    split.
    - symmetry. assumption.
    - intro x'. rewrite <- H. exact (r_cancel _ _ _).
  Qed.

  Lemma factorize_l: forall x y, {z | ulf x y z}.
  Proof.
    intros x y.
    pose (p := X_df _ (a_X_inj y) x).
    inversion p as [z H].
    exists z.
    split.
    - symmetry. assumption.
    - intro x'. rewrite <- H. exact (l_cancel _ _ _).
  Qed.

  Lemma uf_diag: forall x z, urf x x z -> z = z * z.
  Proof.
    intros x el urf.
    inversion urf as [pel uel].
    pose (p := factorize_r el el). inversion p as [z [pz uz]].
    assert (el * x = z * (el * x)) as H.
    -- rewrite assoc.
       rewrite <- pz.
       trivial.
    -- rewrite <- pel in H.
       rewrite <- (uel z H) in pz.
       assumption.
  Qed.

  (* weak identity element (ie identity element for x) *)
  Definition we (e x: X) := unique (fun e' => (x = e' * x) /\ (x = x * e')) e.

  Lemma find_we: forall x, {e | we e x}.
    intro x.
    pose (p := factorize_r x x).
    inversion p as [el P]. inversion P as [pel uel].
    pose (elel := uf_diag _ _ P).
    pose (q := factorize_l x x). inversion q as [er [per uer]].
    assert (el = er) as eler.
    -- pose (r := factorize_l el er). inversion r as [z [pz uz]].
       assert (x * el = (x * er) * z) as H.
       +++ rewrite <- assoc.
           rewrite <- pz.
           trivial.
       +++ rewrite <- per in H.
           rewrite <- (l_cancel _ _ _ H) in pz.
           symmetry in elel.
           exact (r_cancel _ _ _ (eq_trans elel pz)).
    -- exists er.
       split.
       +++ rewrite eler in pel. exact (conj pel per).
       +++ intros f H. destruct H as [fl fr].
           assert (x * er = x * f) as G.
           + transitivity x. ++ symmetry. assumption. ++ assumption.
           + exact (l_cancel _ _ _ G).
  Qed.

  Lemma we_are_identical: forall x y e, we e x -> we e y.
  Proof.
    intros x y we_x. intro fwx. inversion fwx as [[lx rx] ux].
    pose (fwy := find_we y). inversion fwy as [we_y [[ly ry] uy]].
    pose (p := factorize_l y we_x). inversion p as [z [zp _]]. clear p.
    assert (we_x = we_x * we_x) as we_x_we_x.
    - rewrite lx in lx. rewrite assoc in lx. exact (r_cancel _ _ _ lx).
    - assert (we_x * y = (we_x * we_x) * z) as H.
      -- rewrite <- assoc. rewrite <- zp. trivial.
      -- rewrite <- we_x_we_x in H.
         rewrite <- (l_cancel _ _ _ H) in zp.
         symmetry in ly.
         pose (p := r_cancel _ _ _ (eq_trans ly zp)). (* we_y = we_x *)
         split.
         + split.
           ++ assumption.
           ++ rewrite p in ry. assumption.
         + rewrite p in uy. assumption.
  Qed.

  (* the identity *)
  Definition e: X := proj1_sig (find_we x0).

  Theorem l_id: forall x, e * x = x.
  Proof.
    intro x.
    unfold e.
    pose (p := find_we x0).
    replace (find_we x0) with p.
    - dependent inversion p as [e P].
      compute.
      destruct (we_are_identical _ x _ P) as [[l _] _].
      symmetry.
      assumption.
    - trivial.
  Qed.

  Theorem r_id : forall x, x * e = x.
  Proof.
    intro x.
    unfold e.
    pose (p := find_we x0).
    replace (find_we x0) with p.
    - dependent inversion p as [e P].
      compute.
      destruct (we_are_identical _ x _ P) as [[_ r] _].
      symmetry.
      assumption.
    - trivial.
  Qed.

  (* the inverse operation *)
  Definition inv : X -> X.
  Admitted.

  Theorem l_inv : forall x, (inv x) * x = e.
  Admitted.

  Theorem r_inv : forall x, x * (inv x) = e.
  Admitted.

End df_inh_cancel_sgroups.
