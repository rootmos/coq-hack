(* Simply typed lambda calculus (following TaPL) *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Import PeanoNat.

Inductive type :=
| Ty_bool : type
| Ty_fun : type -> type -> type.

Inductive term :=
| T_true : term
| T_false : term
| T_var : nat -> term
| T_abs : type -> term -> term
| T_app : term -> term -> term.

Inductive value :=
| V_abs : type -> term -> value.

Definition ctx := list type.

Inductive typing: ctx -> term -> type -> Set :=
| Typ_true : forall {ctx}, typing ctx T_true Ty_bool
| Typ_false : forall {ctx}, typing ctx T_false Ty_bool
| Typ_var : forall {n T ctx},
    nth_error ctx n = Some T -> typing ctx (T_var n) T
| Typ_abs : forall {T1 T2 ctx t2},
    typing (T1 :: ctx) t2 T2 ->
    typing ctx (T_abs T1 t2) (Ty_fun T1 T2)
| Typ_app : forall T1 {T2 t1 t2 ctx},
    typing ctx t1 (Ty_fun T1 T2) ->
    typing ctx t2 T1 ->
    typing ctx (T_app t1 t2) T2.

Lemma example: typing [] (T_app (T_abs Ty_bool (T_var 0)) T_true) Ty_bool.
Proof.
  apply (Typ_app Ty_bool).
  + now apply Typ_abs, Typ_var.
  + apply Typ_true.
Qed.

Lemma exercise_9_2_3_a:
  {c: ctx & typing c (T_app (T_app (T_var 0) (T_var 1)) (T_var 2)) Ty_bool}.
Proof.
  pose (Tf := Ty_fun Ty_bool (Ty_fun Ty_bool Ty_bool)).
  exists (Tf :: Ty_bool :: Ty_bool :: []).
  apply (Typ_app Ty_bool); [apply (Typ_app Ty_bool)|]; now apply Typ_var.
Qed.

Lemma exercise_9_2_3_b {c}:
  typing c (T_app (T_app (T_var 0) (T_var 1)) (T_var 2)) Ty_bool ->
  exists c' T S,
  c = Ty_fun T (Ty_fun S Ty_bool) :: T :: S :: c'.
Proof.
  intros typ.
  repeat (destruct c; [inversion typ; inversion H4; discriminate|]).
  exists c, t0, t1.
  inversion typ.
  inversion H2.
  inversion H4.
  inversion H8.
  inversion H10.
  inversion H21.
  inversion H13.
  inversion H17.
  reflexivity.
Qed.

Lemma exercise_9_3_2:
  ~ inhabited {c: ctx & {T: type & typing c (T_app (T_var 0) (T_var 0)) T}}.
Proof.
  unfold not.
  intros [[c [T typ]]].
  destruct c; inversion typ; inversion H4; subst.
  + discriminate.
  + inversion H7. rewrite <- H0 in *.
    inversion H2. subst. inversion H3.
    clear H7. clear H2. clear typ. clear H3. clear H4. clear c.
    induction T1.
    - discriminate.
    - inversion H0.
      rewrite H2 in H1.
      exact (IHT1_1 H1).
Qed.

Theorem uniqueness_of_types {c t T T'}: typing c t T -> typing c t T' -> T = T'.
Proof.
  revert c T T'.
  induction t; intros c T T' p1 p2; inversion p1; inversion p2; subst;
    try reflexivity.
  - enough (Some T = Some T') by now inversion H.
    now transitivity (nth_error c n).
  - now rewrite (IHt _ _ _ H3 H8).
  - rewrite (IHt2 _ _ _ H4 H10) in H2.
    pose (IHt1 _ _ _ H2 H8).
    now inversion e.
Qed.

Definition is_value (t: term) :=
  match t with T_abs _ _ | T_true | T_false => true | _ => false end.


Fixpoint shift' (c: nat) (d: nat) (t: term) :=
  match t with
  | T_var k => if k <? c then t else T_var (k + d)
  | T_abs T t => T_abs T (shift' (S c) d t)
  | T_app t1 t2 => T_app (shift' c d t1) (shift' c d t2)
  | _ => t
  end.

Fixpoint unshift' (c: nat) (d: nat) (t: term) :=
  match t with
  | T_var k => if k <? c then t else T_var (k - d)
  | T_abs T t => T_abs T (unshift' (S c) d t)
  | T_app t1 t2 => T_app (unshift' c d t1) (unshift' c d t2)
  | _ => t
  end.

Definition shift := shift' 0.
Definition unshift := unshift' 0.

Fixpoint subst (j: nat) (t: term) (s: term) :=
  match t with
  | T_var k => if k =? j then s else t
  | T_abs T t1 => T_abs T (subst (S j) t1 (shift 1 s))
  | T_app t1 t2 => T_app (subst j t1 s) (subst j t2 s)
  | _ => t
  end.

Lemma unshift_shift t: forall c d,  unshift' c d (shift' c d t) = t.
Proof.
  induction t; auto; simpl; intros c d.
  - unfold unshift'.
    case_eq (n <? c).
    + intros ltb. now rewrite ltb.
    + intros ltb. apply Nat.ltb_nlt in ltb.
      assert (~ n + d < c) by omega.
      apply Nat.ltb_nlt in H.
      rewrite H.
      now rewrite Nat.add_sub.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Inductive eval: term -> term -> Set :=
| E_app1: forall {t t' s}, eval t t' ->
    eval (T_app t s) (T_app t' s)
| E_app2: forall {v t t'}, is_value v = true ->
    eval t t' -> eval (T_app v t) (T_app v t')
| E_app_abs: forall T t {v}, is_value v = true ->
    eval (T_app (T_abs T t) v) (unshift 1 (subst 0 t (shift 1 v))).

Theorem progress {t T}:
  typing [] t T -> (is_value t = true) + {t': term & eval t t'}.
Proof.
  pose (c := @nil type). assert (c = []) by reflexivity. rewrite <- H.
  induction 1; try now left. rewrite H in e; try (destruct n; discriminate).
  right. inversion H0_; subst; try (destruct n; discriminate).
  - case_eq (is_value t2). intros.
    + exists (unshift 1 (subst 0 t0 (shift 1 t2))). now apply E_app_abs.
    + case (IHtyping2 (eq_refl _)).
      ++ intros. now rewrite e in H.
      ++ intros [t' p]. exists (T_app (T_abs T1 t0) t'). now apply E_app2.
  - case (IHtyping1 (eq_refl _)); [discriminate|].
    intros [a p]. exists (T_app a t2). now apply E_app1.
Qed.

Lemma shift'_add a b n {t}: shift' n a (shift' n b t) = shift' n (a + b) t.
Proof.
  revert n.
  induction t; intro; simpl; try reflexivity.
  - case_eq (n <? n0); intros; simpl.
    + now rewrite H.
    + apply Nat.ltb_nlt in H.
      assert (~ n + b < n0) by omega.
      apply Nat.ltb_nlt in H0.
      rewrite H0.
      f_equal.
      omega.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma shift'_0 n t: shift' n 0 t = t.
Proof.
  revert n.
  induction t; intros n0; try easy; simpl.
  + rewrite Nat.add_0_r. case (n <? n0); reflexivity.
  + f_equal. apply IHt.
  + f_equal; [apply IHt1 | apply IHt2].
Qed.

Lemma typing_permutation_shift {c d d' c' t T}:
  length d = length d' ->
  typing (c ++ d ++ c') (shift' (length c) (length d) t) T ->
  typing (c ++ d' ++ c') (shift' (length c) (length d') t) T.
Proof.
  revert c c' d d' T.
  induction t; intros c c' d d' T P; simpl.
  + inversion_clear 1. apply Typ_true.
  + inversion_clear 1. apply Typ_false.
  + case_eq (n <? length c).
    - intros lt. inversion_clear 1. apply Typ_var. rewrite <- H0.
      apply Nat.ltb_lt in lt.
      now rewrite (nth_error_app1 c (d ++ c') lt),
        (nth_error_app1 c (d' ++ c') lt).
    - intros nlt. inversion_clear 1. apply Typ_var. rewrite <- H0.
      apply Nat.ltb_ge in nlt.
      assert (length (c ++ d) <= n + length d) by (rewrite app_length; omega).
      pose (nth_error_app2 (c ++ d) c' H).
      assert (length (c ++ d') <= n + length d') by (rewrite app_length; omega).
      pose (nth_error_app2 (c ++ d') c' H1).
      rewrite <- app_assoc in e0, e.
      rewrite e, e0.
      f_equal.
      repeat rewrite app_length.
      now rewrite P.
  + inversion_clear 1.
    now apply Typ_abs, (IHt (t :: c) _ _ _ _ P).
  + inversion_clear 1.
    apply (Typ_app T1);
      [apply (IHt1 _ _ _ _ _ P)| apply (IHt2 _ _ _ _ _ P)];
      assumption.
Qed.

Fixpoint absent (j: nat) (t: term) :=
  match t with
  | T_var i => i <> j
  | T_abs _ t1 => absent (S j) t1
  | T_app t1 t2 => absent j t1 /\ absent j t2
  | _ => True
  end.

Lemma shift_absent {j i n} t: j <= n < j + i -> absent n (shift' j i t).
Proof.
  revert j i n.
  induction t; intros; try easy; simpl.
  - case_eq (n <? j); intros;
      [apply Nat.ltb_lt in H0 | apply Nat.ltb_ge in H0]; simpl; omega.
  - apply IHt. omega.
  - split; [apply IHt1|apply IHt2]; assumption.
Qed.

Lemma shift_absent_le {j n} i t: absent n t -> n < j -> absent n (shift' j i t).
Proof.
  revert j n i.
  induction t; intros; try easy; simpl.
  - case_eq (n <? j); intros; simpl; try assumption.
    rewrite Nat.ltb_ge in H1. omega.
  - apply IHt. now simpl in H. omega.
  - destruct H. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma shift_absent_ge {j n} i t: absent n t -> j <= n -> absent (n + i) (shift' j i t).
Proof.
  revert j n i.
  induction t; intros; try easy; simpl.
  - case_eq (n <? j); intros; simpl.
    + rewrite Nat.ltb_lt in H1. omega.
    + case (Nat.eq_dec n n0).
      ++ intros. rewrite e in H. now destruct H.
      ++ intros. omega.
  - assert (S (n + i) = S n + i) by auto.
    rewrite H1. apply IHt. now simpl in H. omega.
  - destruct H. split; [apply IHt1 | apply IHt2]; assumption.
Qed.

Lemma shift_comm {i j k l} t: i + j <= k ->
  shift' i j (shift' k l t) = shift' (k + j) l (shift' i j t).
Proof.
  revert i j k l.
  induction t; try easy; intros; simpl.
  - case_eq (n <? i); intros; simpl.
    + pose H0. apply Nat.ltb_lt in e.
      assert (n <? k = true) by (apply Nat.ltb_lt; omega).
      assert (n <? k + j = true) by (apply Nat.ltb_lt; omega).
      rewrite H1, H2. simpl. now rewrite H0.
    + intros. pose H0. apply Nat.ltb_ge in e.
      case_eq (n <? k).
      ++ intros. simpl. rewrite H0. apply Nat.ltb_lt in H1.
         enough (n + j <? k + j = true) by now rewrite H2.
         apply Nat.ltb_lt. omega.
      ++ intros. simpl. apply Nat.ltb_ge in H1.
         assert (n + j <? k + j = false) by (apply Nat.ltb_ge; omega).
         assert (n + l <? i = false) by (apply Nat.ltb_ge; omega).
         rewrite H2, H3. f_equal. omega.
  - f_equal. apply IHt. omega.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
Qed.

Lemma subst_absent_eq {t s n}: absent n s -> absent n t -> subst n t s = t.
Proof.
  revert n s.
  induction t; intros; try easy; simpl.
  - case_eq (n =? n0); intros; [|reflexivity].
    rewrite Nat.eqb_eq in H1. rewrite H1 in H0. now destruct H0.
  - f_equal.
    simpl in H0.
    apply IHt; [|assumption].
    rewrite <- Nat.add_1_r.
    apply shift_absent_ge; [assumption|apply Nat.le_0_l].
  - f_equal; destruct H0; [apply IHt1|apply IHt2]; assumption.
Qed.

Lemma absent_succ {n s}: absent n s -> absent (S n) (shift 1 s).
Admitted.

Lemma subst_absent {t s n}: absent n s -> absent n (subst n t s).
Proof.
  revert n s .
  induction t; intros; try easy; simpl.
  - case_eq (n =? n0). intro. assumption.
    intro. now rewrite Nat.eqb_neq in H0.
  - now apply IHt, absent_succ.
  - split; [apply IHt1|apply IHt2]; assumption.
Qed.

Lemma absent_unshift_typing {t c c' T}: absent (length c) t -> forall S,
  typing (c ++ S :: c') t T -> typing (c ++ c') (unshift' (length c) 1 t) T.
Proof.
  revert c c' T.
  induction t; intros; inversion_clear H0; simpl.
  - apply Typ_true.
  - apply Typ_false.
  - case_eq (n <? length c); intro; apply Typ_var; rewrite <- H1.
    + apply Nat.leb_le in H0.
      rewrite (nth_error_app1 c c' H0).
      now rewrite (nth_error_app1 c (S :: c') H0).
    + apply Nat.leb_gt in H0.
      unfold lt in H0. apply le_S_n in H0.
      case (Nat.eq_dec (length c) n); intros.
      ++ rewrite e in H. now destruct H.
      ++ destruct n; [now apply Nat.le_0_r in H0|].
         rewrite Nat.sub_1_r, <- pred_Sn.
         assert (S :: c' = [S] ++ c') by auto.
         rewrite H2, app_assoc,
           (nth_error_app2 (c ++ [S]) c'); rewrite app_length.
         +++ rewrite Nat.add_1_r, nth_error_app2. f_equal. omega.
         +++ simpl. omega.
  - apply Typ_abs. simpl in H. exact (IHt (t::c) c' T2 H S H1).
  - destruct H. apply (Typ_app T1);
      [apply (IHt1 c c' _ H S) | apply (IHt2 c c' _ H0 S)];
      assumption.
Qed.

Lemma absent_unshift_typing' {t c c' T}: absent (length c) t ->
  typing (c ++ c') (unshift' (length c) 1 t) T ->
  forall S, typing (c ++ S :: c') t T.
Proof.
  revert c c' T.
  induction t; intros.
  - inversion_clear H0. apply Typ_true.
  - inversion_clear H0. apply Typ_false.
  - apply Typ_var. simpl in H0.
    case_eq (n <? length c); intros; rewrite H1 in H0.
    + inversion_clear H0. rewrite <- H2.
      apply Nat.leb_le in H1.
      rewrite (nth_error_app1 c (S :: c') H1).
      now rewrite (nth_error_app1 c c' H1).
    + inversion_clear H0. rewrite <- H2.
      apply Nat.ltb_ge in H1.
      destruct n.
      ++ apply Nat.le_0_r in H1. rewrite H1 in H. now destruct H.
      ++ rewrite Nat.sub_1_r.
         rewrite <- pred_Sn.
         admit.
  - inversion_clear H0.
    apply Typ_abs.
    simpl in H.
    apply (IHt (t :: c) c' T2 H H1).
  - inversion_clear H0.
    destruct H. apply (Typ_app T1); [apply IHt1|apply IHt2]; assumption.
Admitted.

Lemma preservation_under_substitution' {c c' s S t T}:
  typing (c ++ S :: c') t T -> typing (c ++ c') s S ->
  typing (c ++ c')
    (unshift' (length c) 1 (subst (length c) t (shift' (length c) 1 s))) T.
Proof.
  revert c c' s S T.
  induction t; intros c c' s S T; inversion_clear 1; intros st; simpl.
  - apply Typ_true.
  - apply Typ_false.
  - admit.
  - apply Typ_abs.
    unfold shift.
    case (Nat.eq_dec (length c) 0).
    + intros eq. apply length_zero_iff_nil in eq. subst. simpl.
      admit.
    + intros neq.
      rewrite shift_comm.
      assert (Datatypes.S (length c) = length (t :: c)) by auto.
      rewrite H.
      assert (t :: c ++ c' = (t :: c) ++ c') by auto.
      assert (length c + 1 = length (t :: c)) by apply Nat.add_1_r.
      rewrite H1, H2.
      apply (IHt (t :: c) c' (shift' 0 1 s) S T2).
      ++ assumption.
      ++ rewrite <- (unshift_shift s 0 1) in st.
         pose (@absent_unshift_typing' (shift' 0 1 s) [] (c ++ c') S).
         simpl in t1.
         refine (t1 _ st t).
         apply shift_absent.
         auto.
      ++ omega.
  - apply (Typ_app T1);
      [apply (IHt1 _ _ _ S)|apply (IHt2 _ _ _ S)]; assumption.
Admitted.

Lemma preservation_under_substitution {c s S t T}:
  typing (S :: c) t T -> typing c s S ->
  typing c (unshift 1 (subst 0 t (shift 1 s))) T.
Proof.
  apply (@preservation_under_substitution' []).
Qed.

Theorem preservation {c t t' T}:
  typing c t T -> eval t t' -> typing c t' T.
Proof.
  intros typ e.
  revert T typ.
  induction e.
  - intros T typ. inversion typ. subst.
    apply (Typ_app T1); [apply (IHe _ H2) | assumption].
  - intros T typ. inversion typ. subst.
    apply (Typ_app T1); [now pose (IHe _ H4) | now apply IHe].
  - intros T0 typ.
    inversion_clear typ. inversion_clear H. inversion_clear H1.
    + apply Typ_true.
    + apply Typ_false.
    + destruct n.
      ++ inversion H. rewrite <- H2. unfold subst. simpl.
         unfold unshift, shift.
         now rewrite unshift_shift.
      ++ apply Typ_var.
         rewrite <- H. simpl. now rewrite Nat.sub_0_r.
    + refine (preservation_under_substitution _ H0).
      now apply Typ_abs.
    + refine (preservation_under_substitution _ H0).
      apply (Typ_app T2); assumption.
Qed.
