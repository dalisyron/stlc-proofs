(*
    (STLC.v)

    This file contains my solutions to Q4, Q5, Q6.

    They are available under:
        - Theorem question4
        - Theorem question5_weakening
        - Theorem question6

    The code uses the `Maps.v` file from Software Foundations to 
    model partial maps (functions). In order to build this project,
    you need to compile `Maps.v` file first.

    - In your terminal, run:
        ```
        coqc -Q . HW4 Maps.v
        ```
    - Then, run:
        ```
        coqc -Q . HW4 STLC.v
        ```
    
    Should you need help in running the scripts,
    feel free to reach out to me at (mda109@sfu.ca).
*)
From Coq Require Import Strings.String.
Declare Custom Entry stlc.
From HW4 Require Import Maps.
From Coq Require Import Logic.FunctionalExtensionality.

(* ================================================================= *)
(** ** Types *)

Inductive ty : Type :=
  | Ty_Bool     : ty
  | Ty_Nat      : ty 
  | Ty_Arrow    : ty -> ty -> ty.

(* ================================================================= *)
(** ** Terms *)

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_true     : tm
  | tm_false    : tm
  | tm_zero     : tm
  | tm_succ     : tm -> tm
  | tm_if       : tm -> tm -> tm -> tm
  | tm_is_zero  : tm -> tm
  | tm_abs      : string -> ty -> tm -> tm
  | tm_app      : tm -> tm -> tm.

Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Notation "'succ' x" := (tm_succ x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Notation "'is0' x" := (tm_is_zero x) (in custom stlc at level 0,
                                     x custom stlc at level 0).
Coercion tm_var : string >-> tm.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tm_zero
  | nv_succ (t: tm) : nvalue t -> nvalue (tm_succ t).

Inductive bvalue : tm -> Prop :=
    | bv_true : bvalue tm_true
    | bv_false : bvalue tm_false.

Inductive fvalue : tm -> Prop :=
    | fv_abs (x : string) (T : ty) (t : tm) : fvalue (tm_abs x T t).

Inductive value : tm -> Prop :=
    | v_nvalue (t : tm) : nvalue t -> value t
    | v_bvalue (t : tm) : bvalue t -> value t
    | v_fvalue (t : tm) : fvalue t -> value t. 

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).

Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
    match t with
    | tm_var y => if String.eqb x y then s else t
    | <{true}> => <{true}>
    | <{false}> => <{false}>
    | tm_zero => tm_zero
    | <{ succ t1 }> => <{ succ ([x := s] t1) }>
    | <{if t1 then t2 else t3}> =>
        <{ if ([x := s] t1) then ([x := s] t2) else ([x := s] t3)}>
    | <{is0 t1}> => <{ is0 ([x := s] t1) }>
    | <{\y:T, t1}> => if String.eqb x y then t else <{\y:T, [x:=s] t1}>
    | <{ t1 t2 }> => <{([x:=s] t1) ([x:=s] t2)}>
    end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* ================================================================= *)
(** ** Evaluation *)
Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
    | ST_IfTrue     : forall t1 t2,
        step (tm_if tm_true t1 t2) t1
    | ST_IfFalse    : forall t1 t2,
        step (tm_if tm_false t1 t2) t2
    | ST_IsZero     :
        step (tm_is_zero tm_zero) tm_true
    | ST_IsZeroS    : forall t,
        nvalue t ->
        step (tm_is_zero (tm_succ t)) tm_false
    | ST_App : forall x T2 t1 v2,
        value v2 ->
        <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
    | ST_IfPredicate : forall t1 t1' t2 t3,
        t1 --> t1' ->
        <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
    | ST_IsZeroArg      : forall t1 t1',
        t1 --> t1' ->
        <{is0 t1}> --> <{is0 t1'}>
    | ST_AppLeft    : forall t1 t1' t2,
        t1 --> t1' ->
        <{t1 t2}> --> <{t1' t2}>
    | ST_AppRight   : forall v1 t2 t2',
        value v1 ->
        t2 --> t2' ->
        <{v1 t2}> --> <{v1 t2'}>
    | ST_Succ       : forall t1 t1',
        t1 --> t1' ->
        <{succ t1}> --> <{succ t1'}>
where "t '-->' t'" := (step t t').

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
    | T_Var : forall Gamma x T,
        x |-> T ; Gamma |- x \in T
    | T_True : forall Gamma,
        Gamma |- true \in Bool
    | T_False : forall Gamma,
        Gamma |- false \in Bool
    | T_Zero : forall Gamma,
        Gamma |- tm_zero \in Nat
    | T_Succ : forall Gamma t1,
        Gamma |- t1 \in Nat ->
        Gamma |- <{succ t1}> \in Nat
    | T_Abs : forall Gamma x T1 T2 t1,
        x |-> T2 ; Gamma |- t1 \in T1 ->
        Gamma |- \x:T2, t1 \in (T2 -> T1)
    | T_App : forall T1 T2 Gamma t1 t2,
        Gamma |- t1 \in (T2 -> T1) ->
        Gamma |- t2 \in T2 ->
        Gamma |- t1 t2 \in T1
    | T_If : forall Gamma t1 t2 t3 T,
        Gamma |- t1 \in Bool ->
        Gamma |- t2 \in T ->
        Gamma |- t3 \in T ->
        Gamma |- if t1 then t2 else t3 \in T
    | T_IsZero : forall Gamma t1,
        Gamma |- t1 \in Nat ->
        Gamma |- is0 t1 \in Bool
where "Gamma '|-' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Lemma ty_arrow_ty_neq : forall T1 T2,
    <{T1 -> T2}> <> T1.
Proof.
    intros.
    unfold not.
    intros.
    generalize dependent T2. 
    induction T1; intros.
        - discriminate H. 
        - discriminate H.
        - inversion H. apply IHT1_1 in H1. destruct H1.
Qed.

Theorem question4 : forall (Gamma: context),
    ~ exists τ, Gamma |- <{\x:τ, x x}> \in τ. 
Proof.
    unfold not.
    intros.
    destruct H. 
    inversion H. 
    subst.
    apply ty_arrow_ty_neq in H2.
    exact H2.
Qed.

Definition context_included (Gamma Gamma' : context) : Prop :=
    forall x T, (Gamma x = Some T) -> (Gamma' x = Some T).

Theorem question5_weakening : forall (Gamma Gamma' : context) (e : tm) (τ : ty),
    Gamma |- e \in τ -> context_included Gamma Gamma' -> Gamma' |- e \in τ.
Proof.
    intros.
    generalize dependent Gamma'.
    induction H; intros.
        - assert(Gamma' = (x0 |-> T; Gamma')).
            + symmetry. apply update_same. apply H0. apply t_update_eq.
            + rewrite H. apply T_Var.
        - apply T_True.
        - apply T_False.
        - apply T_Zero.
        - apply IHhas_type in H0. apply T_Succ. assumption.
        - apply T_Abs. apply IHhas_type.
            unfold context_included.
            intros.
            destruct (String.eqb x0 x1) eqn:E.
                + apply String.eqb_eq in E.
                    symmetry in E.  
                    rewrite E in H1. 
                    assert ((x0 |-> T2; Gamma) x0 = Some T2).
                        apply update_eq.
                    rewrite H2 in H1. rewrite <- H1. 
                    rewrite E. 
                    apply update_eq.
                + apply String.eqb_neq in E.
                    pose proof E as E2.
                    apply update_neq with (A := ty) (m := Gamma') (v := T2) in E. 
                    rewrite E. 
                    apply update_neq with (A := ty) (m := Gamma) (v := T2) in E2.
                    rewrite E2 in H1. 
                    apply H0. 
                    assumption.
        - apply T_App with T2. 
            + apply IHhas_type1. assumption.
            + apply IHhas_type2. assumption.
        - apply T_If.
            + apply IHhas_type1. assumption.
            + apply IHhas_type2. assumption.
            + apply IHhas_type3. assumption.
        - apply T_IsZero. apply IHhas_type. assumption.
Qed.

Lemma neq_permute : forall (T1 T2 : ty),
    (x |-> T1; y |-> T2) = (y |-> T2; x |-> T1).
Proof.
    intros T1 T2.
    apply functional_extensionality.
    intros z.
    assert((x |-> T1 ; (y |-> T2)) = ((y |-> T2 ; (x |-> T1)))).
        apply update_permute. discriminate. rewrite H. reflexivity.
Qed.

Lemma single_element_partial_map : forall (x y: string) (T1 T2: ty),
    (x |-> T1) y = Some T2 -> x = y /\ T1 = T2.
Proof.
    intros x y T1 T2 H.
    split.
    --
    unfold update in H.
    destruct (String.eqb x y) eqn:E.
        - apply String.eqb_eq in E. exact E.
        - apply String.eqb_neq in E.
            apply update_neq with (A := ty) (m := empty) (v := T1) in E.
            unfold update in E.
            rewrite E in H. 
            discriminate H.
    --
    unfold update in H.
    destruct (String.eqb x y) eqn:E.
        - apply String.eqb_eq in E. rewrite E in H.
            assert((y !-> Some T1; empty) y = Some T1).
                apply update_eq.
            rewrite H0 in H. 
            inversion H. 
            reflexivity.
        - apply String.eqb_neq in E. apply update_neq with (A := ty) (m := empty) (v := T1) in E.
            unfold update in E. rewrite E in H. discriminate H.
Qed.

(*
Question 6 Derivation Tree:
                                                                                                                                                  y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- O \in Nat                        
------------------------------- (T_Var)                                                                    ----------------------------------------------------------------- (T_Var)   ---------------------------------------------------------------------- (T_Succ)                     ---------------------------------------------------------------- (T_Var) ---------------------------------------------------------- (T_Zero)
x |-> <{ Bool }> |- x \in Bool                                                                     y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- y \in (Nat -> Bool)            y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- S O \in Nat                                           y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- y \in (Nat -> Bool)           y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- O \in Nat      
------------------------------------------------ (T_Weakening)    ----------------------------------------------------------------------------------------------------------------------------------------------------------------- (T_App)      ------------------------------------------------------------------------------------------------------------------------------------------------- (T_App) 
y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- x \in Bool             y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- y S O \in Bool                                                                                                                             y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- y O \in Bool
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ (T_If)
 y |-> <{ Nat -> Bool }>; x |-> <{ Bool }> |- if x then y S O else y O \in Bool
------------------------------------------------------------------------------------------------------------- (T_Abs)
 x |-> <{ Bool }> |- λy : Nat -> Bool, if x then y S O else y O \in ((Nat -> Bool) -> Bool)
--------------------------------------------------------------------------------------------------------------- (T_Abs)
|- λx : Bool, λy : Nat -> Bool, if x then y S O else y O \in (Bool -> (Nat -> Bool) -> Bool)
*)
Theorem question6 : exists τ,
    empty |- <{\x:Bool, \y:(Nat -> Bool), if x then y (succ tm_zero) else y tm_zero}> \in τ.
Proof.
    exists <{ Bool -> (Nat -> Bool) -> Bool }>.
    apply T_Abs.
    apply T_Abs.
    apply T_If.
        - apply question5_weakening with (x |-> <{ Bool }>).
            + apply T_Var.
            + unfold context_included. intros.
                apply single_element_partial_map in H.
                destruct H.
                rewrite <- H.
                assert (y <> x) by discriminate.
                apply update_neq with (A := ty) (m := (x |-> <{ Bool }>)) (v := <{ Nat -> Bool }>) in H1. 
                rewrite H1. 
                rewrite H0.
                apply update_eq.
        - apply T_App with <{Nat}>. 
            + apply T_Var.
            + apply T_Succ. apply T_Zero.
        - apply T_App with <{Nat}>.
            + apply T_Var.
            + apply T_Zero.
Qed.
