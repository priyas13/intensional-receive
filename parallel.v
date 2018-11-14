(** * Parallel: Working with Parallel composition *)

Require Export Induction.

(** Parallel Composition **)

(** Generalizing the definition of parllel composition, we can
    describe the type of parallel composition like this: 
    "A parallel composition component
    is either the empty or else a composition of one or and more entity 
    of type A" **)

Set Implicit Arguments.

Inductive comp (A : Type) : Type :=
 | empty_comp : comp A
 | par_comp : A -> comp A -> comp A.

Implicit Arguments empty_comp [A].

Infix "|:" := par_comp (at level 60, right associativity).

Theorem empty_cons : forall (A:Type)(x:A) (l:comp A), 
  empty_comp <> x |: l.
 intros.
 discriminate.
Qed.

Fixpoint app (A : Type)(l m:comp A) : comp A :=
  match l with
  | empty_comp => m
  | a |: l' => a |: (app l' m)
  end.

(* Structural Congruence *)
(* Two processes are structurally congruent, if they are identical up to structure. *)
Inductive congruence (A : Type) : comp A -> comp A -> Prop :=
| no_pro : forall P, 
            congruence P (app P empty_comp)
| commutative : forall P Q, 
                         congruence (app P Q) (app Q P)
| associative : forall P Q R, 
                       congruence (app P (app Q R)) 
                      (app (app P Q) R)
| par_com : forall P Q P' Q', 
                  congruence P P' ->
                  congruence Q Q' ->
                  congruence (app P Q) (app P' Q')
| same : forall P,
              congruence P P
| symmetric : forall P Q,
                     congruence P Q ->
                     congruence Q P
| transitive : forall P Q R,
                   congruence P Q ->
                   congruence Q R ->
                   congruence P R.

Check congruence.

Print congruence.

Inductive comp_operation (A : Type) : comp A -> comp A-> Prop :=
| par1 : comp_operation empty_comp empty_comp
| par2 : forall Q R Q',
            comp_operation Q Q' ->
            comp_operation (app Q R) (app Q' R)
| par3 : forall Q R R',
            comp_operation R R' ->
            comp_operation (app Q R) (app Q R').

Check comp_operation.

Print comp_operation.

(** P --> P' then there exists P'' such that P' == P'' /\ P --> P''. **)
Theorem x: forall (A : Type) (P P' : comp A),
comp_operation P P' ->
exists P'', congruence P' P'' /\
comp_operation P P''.
Proof.
 intros A P P' H.
 induction H.
 exists empty_comp.
 split.
 apply same.
 apply par1.
 exists (app Q' R).
 split.
 apply same.
 apply par2.
 assumption.
 exists (app Q R').
 split.
 apply same.
 apply par3.
 assumption.
Qed.

(** P --> Q there exists Q' such that P --> Q' then Q == Q'. *)
Theorem b : forall (A : Type) (P Q : comp A),
comp_operation P Q ->
exists Q', comp_operation P Q' ->
congruence Q Q'.
Proof.
 intros A P Q H.
 destruct H.
 exists empty_comp.
 intros.
 apply same.
 exists (app Q' R).
 intros.
 apply same.
 exists (app Q R').
 intros.
 apply same.
Qed.

(** P == P' /\ P' --> Q' /\ Q == Q'
then P --> Q. **)
Theorem z : forall (A : Type) (P Q P' Q' : comp A),
congruence P P' /\
comp_operation P' Q' /\ congruence Q Q' ->
exists (P : comp A) , exists (Q : comp A), comp_operation P Q.
Proof.
 intros A P Q P' Q' H.
 destruct H. destruct H0.
 exists P'. exists Q'.
 assumption.
Qed.

(** P --> Q then there exists P' : P == P' /\ P' --> Q. **)
Theorem y : forall (A : Type) (P Q : comp A),
comp_operation P Q ->
exists (P' : comp A), congruence P P' /\ 
comp_operation P' Q.
Proof.
 intros A P Q H.
 induction H.
 exists empty_comp.
 split.
 apply same.
 apply par1.
 exists (app Q R).
 split.
 apply same.
 apply par2.
 assumption.
 exists (app Q R).
 split.
 apply same.
 apply par3.
 assumption.
Qed.

(** P --> Q then 
there exists P' Q' : P' --> Q' /\ Q == Q' /\ P == P'. **)
Theorem a : forall (A : Type) (P Q : comp A),
comp_operation P Q ->
exists (P' : comp A) , exists (Q' : comp A), 
comp_operation P' Q' /\ congruence Q Q' /\
congruence P P'.
Proof.
 intros A P Q H.
 induction H.
 exists empty_comp.
 exists empty_comp.
 split.
 apply par1.
 split.
 apply same.
 apply same.
 destruct IHcomp_operation.
 exists (app Q R).
 exists (app Q' R).
 split.
 apply par2.
 assumption.
 split.
 apply same.
 apply same.
 exists (app Q R).
 exists (app Q R').
 split.
 apply par3.
 assumption.
 split.
 apply same.
 apply same.
Qed.

(** P |+| Q == Q |+| P. **)
Theorem congruence_commutative : forall (A : Type) (P Q : comp A),
congruence (app P Q) (app Q P).
Proof.
 intros A P Q.
 apply commutative.
Qed.

(** P |+| Q == Q |+| P. **)
Theorem congruence_associativity : forall (A : Type) (P Q R : comp A),
congruence (app P (app Q R)) 
                      (app (app P Q) R).
Proof.
 intros A P Q R.
 apply associative.
Qed.

(** P |+| no_process == P **)
Theorem congruence_no_process : forall (A : Type) (P : comp A),
congruence (app P empty_comp) P.
Proof.
 intros A P.
 apply symmetric.
 apply no_pro.
Qed.

(** P == P |+| no_process **)
Theorem congruence_no_process' : forall (A : Type) (P : comp A),
congruence P (app P empty_comp).
Proof.
 intros A P.
 apply symmetric.
 apply symmetric.
 apply no_pro.
Qed.

(** Two processes are said to bisimilar if they can mimic each other step by step **)
CoInductive bisimilar (A : Type) : comp A -> comp A -> Prop :=
bsm : forall P Q,
             (forall P',
            comp_operation P P' ->
            exists Q', comp_operation Q Q' /\
            bisimilar P' Q') /\
            (forall Q',
            comp_operation Q Q' ->
            exists P', comp_operation P P' /\
            bisimilar P' Q') ->
            bisimilar P Q.

Hypothesis eq_A : forall (A : Type) (x y : A), {x = y}+{x <> y}.

(* override updates a type p in the program P with p1. *)
Fixpoint override (A : Type ) (p : A) (P : comp A) (p1 : A) : comp A :=
match P with 
| empty_comp => empty_comp
| p' |: P' => match eq_A p p' with 
               | left _ => p1 |: P'
               | right _ => p' |: override p P' p1
              end
end.

(* in_comp states that process P is present in composition. *)
Fixpoint  in_comp (A : Type) (Q : A) (P : comp A) : bool :=
match P with 
| empty_comp => false
| P1 |: P1' => match eq_A Q P1 with 
                     | left _ => true
                     | right _ => in_comp Q P1'
end
end.

(** Remove process from the parallel composition **)
 Fixpoint remove (A : Type) (x : A) (l : comp A) : comp A :=
    match l with
      | empty_comp => empty_comp
      | y |: tl => if (eq_A x y) then remove x tl else y |: (remove x tl)
    end.

(* Subset *)
Fixpoint is_subset (A : Type) (P : comp A) (P' : comp A) : bool :=
match P with 
| empty_comp => true 
| P1 |: P1' => if (in_comp P1 P') then (is_subset P1' (remove P1 P1')) else false
end.

(* Number of entity in the parallel composition. *)
Fixpoint number (A : Type) (P : comp A) : nat :=
match P with 
| empty_comp => 0
| P1 |: P1' => S (number P1')
end.


Variable P1 : Type.
Variable P2 : Type.
Variable P3 : Type.
Variable P4 : Type.
Variable P5 : Type.

Example test_number_parallel1:  number (P1 |: (P2 |: (P3 |: empty_comp))) = 3.
Proof.
reflexivity.
Qed.

(** Addition **)
(** The [add_comp] a entity to the existing parallel composition .**)
Fixpoint add_comp (A : Type) (P : comp A) (P1 : A) : comp A :=
 match P with 
  | empty_comp => P1 |: empty_comp
  | Q |: P' => Q |: (add_comp P' P1)
 end.

Example test_add_comp1:  add_comp (P1 |: (P2 |: (P3 |: empty_comp))) P4 = 
(P1 |: (P2 |: (P3 |: (P4 |: empty_comp)))).
Proof.
reflexivity.
Qed.

Example test_add_comp2:  add_comp empty_comp P4 = 
(P4 |: empty_comp).
Proof.
reflexivity.
Qed.

(* Same parallel compositions *)
Definition same_comp (A : Type) (P: comp A) (Q: comp A) : Prop := 
is_subset P Q = true /\ is_subset Q P = true.

(* P = Q *)
Axiom equal_comp : forall (A : Type) (P Q : comp A),
same_comp P Q -> P = Q.

Example test_override_1 : forall (A : Type) (P1 P1' : comp A), override P1 empty_comp P1' = 
empty_comp.
Proof.
reflexivity.
Qed.


