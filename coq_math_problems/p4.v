Require Import Fun.

Fixpoint Fin(n : nat) : Set :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Require Import Basics.

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

Lemma emb_dec {Y n}: forall e: Fin n -> Y, forall y, {x | e x = y} + (forall x, e x <> y).
Admitted.

Require Import PeanoNat.

Lemma f_fin_dom_fin_codom {Y n}: forall f: Fin n -> Y,
  {m: nat & Image f (Fin m) & m <= n }.
Proof.
  induction n.
  - intro f.
    exists 0. all: swap 1 2. { apply le_n. }
    pose (f' := vacuous_f Empty_set).
    pose (f'_surj := vacuous_f_surj f').
    pose (emb := vacuous_f Y).
    pose (emb_inj := vacuous_f_inj emb).
    refine (mkImage _ _ f Empty_set f' f'_surj emb emb_inj _). { intro x. case x. }
  - intro f.
    destruct (IHn (compose f inr)) as [m [f' f's e ei c] l].
    case (emb_dec e (f (inl tt))).
    -- intros [y fsn'_p].
       exists m. all: swap 1 2. { apply le_S. assumption. }
       pose (f'_e := fun (n: Fin (S n)) => match n with inl _ => y | inr m => f' m end).
       assert (surj f'_e) as f'_es.
       { intro y'. destruct (f's y') as [x px]. exists (inr x). assumption. }
       assert (forall x, compose e f'_e x = f x) as c_e.
       {
         intro x. case x.
         + intro. compute.
           rewrite fsn'_p.
           replace u with tt; [ reflexivity | case u; reflexivity ].
         + apply c.
       }
       exact (mkImage _ _ f _ f'_e f'_es e ei c_e).
    -- intro H.
       exists (S m). all: swap 1 2. { exact (proj1 (Nat.succ_le_mono _ _) l). }
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
         intro y. case y.
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
