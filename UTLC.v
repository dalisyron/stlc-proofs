(*
    (UTLC.v)

    This file contains my solutions to Q1, Q2, Q3.

    They are available under:
        - Theorem question1
        - Definition question2
        - Theorem question3
*)
From Coq Require Import Strings.String.
Declare Custom Entry utlc.

(* Define `L` as the language for Untyped Lambda Calculus *)
Inductive L : Type :=
    | e_abs (x: string) (e: L)
    | e_app (e1 e2: L)
    | e_var (x: string).

Notation "<{ e }>" := e (e custom utlc at level 99).
Notation "( x )" := x (in custom utlc, x at level 99).
Notation "x" := x (in custom utlc at level 0, x constr at level 0).
Coercion e_var : string >-> L.
Notation "\ x , y" := (e_abs x y) (
    in custom utlc at level 90,
    x at level 99,
    y custom utlc at level 99,
    left associativity
).
Notation "x y" := (e_app x y) (in custom utlc at level 1, left associativity).


Inductive value : L -> Prop :=
    | v_fun (x: string) (e: L): value <{ \x, e }>.


Reserved Notation "e1 '[' v '/' x ']' == e2'" (in custom utlc at level 20, x constr).

Inductive subst : L -> L -> string -> L -> Prop :=
    | subst_app_rep
        (e1 e2 e1' e2' v: L)
        (x: string)
        (H1: <{e1 [v / x] == e1'}>)
        (H2: <{e2 [v / x] == e2'}>) :
        <{(e1 e2) [v / x] == e1' e2'}>
    | subst_abs_rep
        (x y: string)
        (Hneq: x <> y)
        (e e' v: L)
        (H: <{e [v / y] == e'}>) :
        <{(\x, e) [v / y] == \x, e'}>
    | subst_abs_shadow
        (x: string)
        (e v: L) :
        <{(\x, e) [v / x] == \x, e}>
    | subst_var_neq
        (x y: string)
        (Hneq: x <> y)
        (v: L) :
        <{x [v / y] == x}>
    | subst_var_eq
        (x: string)
        (v: L) :
        <{x [v / x] == v}>
where "e1 [ v / x ] == e2" := (subst e1 e2 x v) (in custom utlc).

Inductive step : L -> L -> Prop :=
    | step_app_L
        (e1 e1' e2: L) :
        step e1 e1' ->
        step <{e1 e2}> <{e1' e2}>
    | step_app_R
        (v e2 e2': L)
        (Hv: value v)
        (Hev: step e2 e2') :
        step <{v e2}> <{v e2'}>
    | step_app
        (x: string)
        (e v e': L)
        (Hv: value v)
        (Hsubst: <{e [v / x] == e'}>) :
        step (<{(\x, e) v}>) e'.

Notation "e1 '-->' e2" := (step e1 e2) (at level 40).

Inductive multi_step : L -> L -> Prop :=
    | multi_step_base (e1 e2: L) (Hstep: e1 --> e2) :
        multi_step e1 e2
    | multi_step_refl (e: L) :
        multi_step e e
    | multi_step_trans (e1 e2 e3: L) :
        multi_step e1 e2 ->
        multi_step e2 e3 ->
        multi_step e1 e3.

Notation "e1 '-->*' e2" := (multi_step e1 e2) (at level 40).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Definition a : string := "a".
Definition b : string := "b".
Definition c : string := "c".
Definition d : string := "d".
Definition f : string := "f".
Definition w : string := "w".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.
Hint Unfold a : core.
Hint Unfold b : core.
Hint Unfold c : core.
Hint Unfold d : core.
Hint Unfold f : core.
Hint Unfold w : core.


Definition term_q1 : L :=
    <{((\x, \y, x y y) ((\z, z) (\a, \b, b a))) ((\c, c c) (\d, d))}>.

Theorem question1 : exists (e: L), (term_q1 --> e).
Proof.
    exists <{ (\ x, \ y, x y y) (\ a, \ b, b a) ((\ c, c c) (\ d, d)) }>. 

    apply step_app_L.
    apply step_app_R. 
        + apply v_fun.
        + apply step_app.
            -- apply v_fun.
            -- apply subst_var_eq.
Qed.

(*
Question 1 Derivation:

                                    --------------------------- (v_fun)    --------------------------------------------- (subst_var_eq)
                                    (value <{ (λa. λb. b a) }>)            <{ z [(λ a. λ b. b a) / z]== (λ a. λ b. b a)}>  
--------------------------(v_fun)   ------------------------------------------------------------------------------------ (step_app)
value <{ λx. λy. x y y }>               <{ (λz. z) (λa. λb. b a) }> --> <{ λa. λb. b a }>
------------------------------------------------------------------------------------------ (step_app_R)
<{ (λx. λy. x y y) ((λz. z) (λa. λb. b a)) }> --> <{ (λx. λy. x y y) (λa. λb. b a) }>
------------------------------------------------------------------------------------------------------------------------------ (step_app_L)
<{((λx. λy. x y y) ((λz. z) (λa. λb. b a))) ((λc. c c) (λd. d))}> --> <{ (λx. λy. x y y) (λa. λb. b a) ((λc. c c) (λd. d)) }>

*)


(* int n e, means that int(n) = e, int is the same as app defined in question
    I'm not using the name app, because there is already a term called app in the language
*)
Inductive int: nat -> L -> Prop :=
    | int_base : int 0 <{ \f, \x, x }>
    | int_succ
        (n: nat)
        (e: L)
        (H: int n <{ \f, \x, e }>) :
        int (S n) <{ \f, \x, (f e) }>.

Hint Constructors int : core.

Example int_0 : int 0 <{ \f, \x, x }>. Proof. auto. Qed.
Example int_4 : int 4 <{ \f, \x, f (f (f (f x))) }>. Proof. auto. Qed.

(* I will also define a `function` to yield `int`, 
    and after proving that it is equivalent to the inductive relation,
    use this for the rest of the question (for ease of use) *)
Fixpoint int_f_body (n: nat): L :=
    match n with
    | 0 => x
    | S n' => e_app f (int_f_body n')
    end.

Definition int_f (n: nat): L := let b := int_f_body n in <{ \f, \x, b }>.
Coercion int_f : nat >-> L.

Lemma int_f_equiv_int: forall (n: nat) (e: L),
    int n e <-> e = int_f n.
Proof.
    split; intros.
    - induction H.
        + reflexivity.
        + unfold int_f in *. simpl. inversion IHint. reflexivity.
    - generalize dependent e. induction n; intros.
        + rewrite H. auto. 
        + rewrite H. unfold int_f. simpl. apply int_succ. apply IHn. auto.
Qed.


Definition n : string := "n".
Hint Unfold n : core.


Hint Constructors step : core.
Hint Constructors value : core.
Hint Constructors subst : core.
Hint Constructors multi_step : core.
Hint Extern 1 => constructor : core. (* For auto unfold *)

Hint Resolve String.eqb : core.
Hint Resolve String.eqb_spec : core. 
Hint Unfold not : core.
Hint Extern 1 => discriminate : core.

Hint Constructors int : core.

Definition e_true := <{\x, \y, x}>. 
Definition e_false := <{\x, \y, y}>. 
Definition iszero := <{\n, n (\x, e_false) e_true }>.

Definition question2 := iszero.

Hint Unfold iszero : core.

Example iszero_0 : <{iszero 0}> -->* e_true.
Proof.
    unfold iszero.
    eapply multi_step_trans.
        + apply multi_step_base.
            Set Printing Parentheses.
            apply step_app.
                - auto.
                - apply subst_app_rep.
                    -- apply subst_app_rep.
                        ++ auto.
                        ++ auto.
                    -- auto.
        + eapply multi_step_trans.
            - apply multi_step_base. auto.
            - apply multi_step_base. auto.
Qed.

Example iszero_1 :
    <{iszero 1}> -->* e_false.
Proof.
    intros.
    unfold iszero.
    unfold e_false.
    unfold e_true.
    eapply multi_step_trans. 
        - apply multi_step_base.
            simple apply step_app.
                + auto. 
                + apply subst_app_rep.
                    -- apply subst_app_rep.
                        ++ auto. 
                        ++ auto. 
                    -- auto.
        - eapply multi_step_trans. 
            + apply multi_step_base.
                unfold int_f. 
                unfold int_f_body. 
                apply step_app_L. 
                apply step_app. 
                    -- auto. 
                    -- auto. 
            + eapply multi_step_trans.
                -- apply multi_step_base.
                    unfold int_f. 
                    unfold int_f_body. 
                    apply step_app. 
                        --- auto. 
                        --- auto.  
                -- auto.
Qed.

Example iszero_2: forall (n: nat),
    <{iszero 2}> -->* e_false.
Proof.
    intros.
    unfold iszero.
    unfold e_false.
    unfold e_true.
    eapply multi_step_trans. 
        - apply multi_step_base.
            simple apply step_app.
                + auto. 
                + apply subst_app_rep.
                    -- apply subst_app_rep.
                        ++ auto. 
                        ++ auto. 
                    -- auto.
        - eapply multi_step_trans.
            + apply multi_step_base.
                unfold int_f. 
                unfold int_f_body. 
                apply step_app_L. 
                apply step_app. 
                    -- auto. 
                    -- auto.
            + eapply multi_step_trans.
                -- apply multi_step_base.
                    unfold int_f. 
                    unfold int_f_body. 
                    apply step_app.
                        --- auto. 
                        --- auto.
                -- eapply multi_step_trans.
                    ++ apply multi_step_base.
                        unfold int_f. 
                        unfold int_f_body. 
                        apply step_app_R. 
                            --- auto. 
                            --- auto. 
                    ++ auto.
Qed.

(*
Question 3: Derivation
                    ----------------------- (var_eq)     ------------------------------ (abs_shadow)         ------- (by definition)
                      z [λw. w / z] = (λw. w)               (λz. z) [λw. w / z] = (λz. z)                     x ≠ z                        
                    ---------------------------------------------------------------------- (app_rep)     -------------------- (var_neq)
                                (z (λz. z)) [λw. w / z] = ((λw. w) (λz. z))                                x [λw. w / z] = x            
 ------- (by definition)         ----------------------------------------------------------------------------------------------- (app_rep)
  x ≠ z                            ((z (λz. z)) x) [λw. w / z] = (((λw. w) (λz. z)) x) 
--------------------------------------------------------------------------------------- (abs_rep)
  (λx. z (λz. z) x) [(λw. w) / z] = (\x, (\w, w) (\z, z) x)
*)
Theorem question3 : exists (e': L), 
    <{(\x, z (\z, z) x) [(\w, w) / z] == e'}>.
Proof.
    exists <{(\x, (\w, w) (\z, z) x)}>.
    apply subst_abs_rep.
        + discriminate.
        + apply subst_app_rep.
            -- apply subst_app_rep.
                ++ apply subst_var_eq.
                ++ apply subst_abs_shadow.
            -- apply subst_var_neq.
                ++ discriminate.
Qed.