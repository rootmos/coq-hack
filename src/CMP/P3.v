(* https://coq-math-problems.github.io/Problem3/ *)

Require Import Hack.CMP.Fun.

(* The proof notices that the cancellation properties makes the
   two left/right group actions a_X and X_a injective, which in
   turn implies that any x,y in X has a unique left/right
   factorization.

   This is used to find a "weak" identity element, defined here
   as a unique identity element for each x, ie:
   we(x) * x = x * we(x) = x. Then it's shown that we(x)=we(y) for
   any x, y, letting us define e := we(x0).

   The inverse is found by using the unique factorization with
   respect to the identity element.
*)

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
    intros a x x'. apply r_cancel.
  Qed.

  Lemma a_X_inj: forall a, inj (a_X a).
  Proof.
    intros a x x'. apply l_cancel.
  Qed.

  Definition urf (x y z: X) := unique (fun z' => x = z' * y) z.
  Definition ulf (x y z: X) := unique (fun z' => x = y * z') z.

  Lemma factorize_r: forall x y, {z | urf x y z }.
  Proof.
    intros x y.
    destruct (X_df _ (X_a_inj y) x) as [z H].
    exists z.
    rewrite <- H.
    split; [ reflexivity | apply r_cancel ].
  Qed.

  Lemma factorize_l: forall x y, {z | ulf x y z}.
  Proof.
    intros x y.
    destruct (X_df _ (a_X_inj y) x) as [z H].
    exists z.
    rewrite <- H.
    split; [ reflexivity | apply l_cancel ].
  Qed.

  Lemma uf_diag: forall x z, urf x x z -> z = z * z.
  Proof.
    intros x el [pel uel].
    destruct (factorize_r el el) as [z [pz _]].
    assert (el * x = z * (el * x)) as H.
    { rewrite assoc, <- pz. reflexivity. }
    rewrite <- pel in H.
    rewrite <- (uel z H) in pz.
    assumption.
  Qed.

  (* weak identity element (ie identity element for x) *)
  Definition we (e x: X) := unique (fun e' => (x = e' * x) /\ (x = x * e')) e.

  Lemma find_we: forall x, {e | we e x}.
    intro x.
    pose (p := factorize_r x x).
    inversion_clear p as [el P]. inversion P as [pel _].
    destruct (factorize_l x x) as [er [per uer]].
    assert (el = er) as eler.
    {
      destruct (factorize_l el er) as [z [pz _]].
      assert (x * el = (x * er) * z) as H.
      { rewrite <- assoc, <- pz. reflexivity. }
      rewrite <- per in H.
      rewrite <- (l_cancel _ _ _ H) in pz.
      apply r_cancel with (1 := eq_trans (eq_sym (uf_diag _ _ P)) pz).
    }
    exists er.
    split.
    - rewrite eler in pel. exact (conj pel per).
    - intros f [fl fr]. apply uer. assumption.
  Qed.

  Lemma we_are_identical: forall x y e, we e x -> we e y.
  Proof.
    intros x y we_x [[lx rx] ux].
    destruct (find_we y) as [we_y [[ly ry] uy]].
    destruct (factorize_l y we_x) as [z [zp _]].
    assert (we_x = we_x * we_x) as we_x_we_x.
    { rewrite lx, assoc in lx. exact (r_cancel _ _ _ lx). }
    assert (we_x * y = (we_x * we_x) * z) as H.
    { rewrite <- assoc, <- zp. reflexivity. }
    rewrite <- we_x_we_x in H.
    rewrite <- (l_cancel _ _ _ H) in zp.
    rewrite (r_cancel _ _ _ (eq_trans (eq_sym ly) zp)) in ry, uy.
    split; try split; assumption.
  Qed.

  (* the identity *)
  Definition e: X := proj1_sig (find_we x0).

  Theorem l_id: forall x, x = e * x.
  Proof.
    intro x.
    unfold e.
    pose (p := find_we x0).
    replace (find_we x0) with p by reflexivity.
    dependent inversion_clear p as [e P].
    exact (proj1 (proj1 (we_are_identical _ x _ P))).
  Qed.

  Theorem r_id : forall x, x = x * e.
  Proof.
    intro x.
    unfold e.
    pose (p := find_we x0).
    replace (find_we x0) with p by reflexivity.
    dependent inversion_clear p as [e P].
    exact (proj2 (proj1 (we_are_identical _ x _ P))).
  Qed.

  (* the inverse operation *)
  Definition inv (x: X): X := proj1_sig (factorize_l e x).

  Theorem r_inv : forall x, e = x * (inv x).
  Proof.
    intro x.
    unfold inv.
    pose (p := factorize_l e x).
    replace (factorize_l e x) with p by reflexivity.
    dependent inversion_clear p as [i P].
    exact (proj1 P).
  Qed.

  Theorem l_inv : forall x, e = (inv x) * x.
  Proof.
    intro x.
    assert (x * e = x * inv x * x).
    { rewrite <- r_inv, <- r_id, <- l_id. reflexivity. }
    rewrite <- assoc in H.
    apply l_cancel with (1 := H).
  Qed.

End df_inh_cancel_sgroups.
