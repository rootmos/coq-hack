Require Import Hack.CMP.Fun.

Fixpoint Fin(n : nat): Set :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

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

Lemma fin_inr_inj {n}: inj (inr: Fin n -> Fin (S n)).
Proof.
  intros x x' H. injection H. intro. assumption.
Qed.
