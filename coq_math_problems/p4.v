Require Import Fun.

Fixpoint Fin(n : nat) : Set :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Require Import Basics.

Record Image {X Y} (f: X->Y) fX := mkImage {
  f' : X -> fX;
  f'_surj := surj f';
  emb : fX -> Y;
  emb_inj := inj emb;
  comp: forall x, (compose emb f') x = f x;
}.

Lemma f_fin_dom_fin_codom {Y n}: forall f: Fin n -> Y,
  {m: nat & Image f (Fin m) & m <= n }.
Admitted.

Lemma f_inj_fin_dom_fin_codom {Y n}: forall f: Fin n -> Y, inj f -> Image f (Fin n).
Admitted.

Lemma f_fin_codom_eq_surj {X n}: forall f: X -> Fin n, Image f (Fin n) -> surj f.
Admitted.

Theorem inj_to_surj {n}: forall f: Fin n -> Fin n, inj f -> surj f.
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
