(* Simply typed lambda calculus (following TaPL) *)

Require Import List.
Import ListNotations.

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

Inductive typing: ctx -> term -> type -> Type :=
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
