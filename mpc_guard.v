Add LoadPath "/Users/swarnpriya/Desktop/masters/intensional-receive".
Require Export SfLib.
Require Export parallel.
Import ListNotations.

(* TYPES *)

(* ty represent value types in the MPC and cty represent the
    communication types of MPC. *)
Inductive ty : Type :=
 | bool_ty  : ty
 | arrow_ty : ty -> cty -> ty -> ty
 | nat_ty : ty
 | unit_ty : ty
 | prod_ty : ty -> ty -> ty
 | process_ty : ty -> cty -> ty
with cty : Type :=
 | null : cty
 | par : cty -> cty -> cty
 | choice : cty -> cty -> cty
 | r_cty : ty -> cty
 | s_cty : ty -> cty
 | seq : list cty -> cty.

Print ty.

Check ty.

(* Expressions *)
Inductive exp : Type :=
 | send_exp : exp -> exp -> exp
 | spawn_exp : id -> ty -> exp -> exp
 | receive_exp : id -> ty -> exp -> exp -> exp
 | become_exp : exp -> exp
 | set_exp : exp -> exp
 | get_exp : exp
 | self_exp : exp
 | stop_exp : exp
 | pair_exp : exp -> exp -> exp
 | fst_exp : exp -> exp
 | snd_exp : exp -> exp
 | true_exp : exp
 | false_exp : exp
 | abs_exp : id -> ty -> exp -> exp
 | app_exp : exp -> exp -> exp
 | var_exp : id -> exp
 | unit_exp : exp
 | nat_exp : nat -> exp
 | if_exp : exp -> exp -> exp -> exp
 | seq_exp : exp -> exp -> exp
 | val_exp : id -> exp
 | guard_exp : id -> ty -> exp -> exp -> exp -> exp.

(* process_st represents the state of a process with type 
represented by ty,name id and the value it contains. *)
Inductive process_st : Type :=
 | st_decl : ty -> id -> exp -> process_st.

Inductive value : exp -> Prop :=
 | abs_val : forall x T e,
   value (abs_exp x T e)
 | true_val : 
   value true_exp
 | false_val : 
   value false_exp
 | pair_val : forall v v',
   value v ->
   value v' ->
   value (pair_exp v v')
 | nat_val : forall n,
   value (nat_exp n)
 | unit_val : value unit_exp
 | process_val : forall x,
   value (val_exp x).

Inductive action : Type :=
 | send : exp -> exp -> exp -> action 
 | receive : exp -> exp -> action
 | become : exp -> action
 | spawn : exp -> exp -> action
 | get : exp -> action
 | set : exp -> action
 | self : action
 | local : exp -> action.

(* mail_box represents the list of messages that are 
   send to any process. *)
Definition mail_box := list exp.

(* This hypothesis states that there are two expressions e1 and 
    e2 are either equal or not equal. *)
Hypothesis is_equal_exp : forall e e' : exp, {e = e'} + {e <> e'}.

(* process_conf represents process configuration where 
   process_st represents the state in the process, exp 
   represents the body of the process, mail_box stores 
   the messages send to the process and exp represents 
   the address of the process. *)
Inductive process_conf : Type :=
 | Sigma : process_st -> exp -> mail_box -> exp -> process_conf.

(* glb_conf is a set of process configurations *)
Definition global_conf := comp process_conf.

(* concat_mail function concatenate the list of expression. *)
Fixpoint concat_mail (M : mail_box) (e : exp) : mail_box :=
match M with 
 | nil => (e :: nil)
 | e' :: M' => e' :: (concat_mail M' e)
end.

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   (*Case "n1 = n2".*)
     left. rewrite Heq. reflexivity.
   (*Case "n1 \u2260 n2".*)
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

Lemma eq_id : forall (T:Type) x (p q:T),
              (if eq_id_dec x x then p else q) = p.
Proof.
  intros.
  destruct (eq_id_dec x x); try reflexivity.
  apply ex_falso_quodlibet; auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y ->
               (if eq_id_dec x y then p else q) = q.
Proof.
  intros. destruct (eq_id_dec x y).
  apply H in e. inversion e.
  reflexivity.
Qed.

(** SUBSTITUTION **)

Fixpoint subst (x:id) (e':exp) (e:exp) : exp :=
match e with
 | var_exp y => 
   if eq_id_dec x y then e' else e
 | abs_exp y T' e2 => 
   abs_exp y T' (if eq_id_dec x y then e2 else 
   (subst x e' e2))
 | app_exp e2 e3 => 
   app_exp (subst x e' e2) (subst x e' e3)
 | nat_exp n => 
   nat_exp n
 | pair_exp e1 e2 => 
   pair_exp (subst x e' e1) (subst x e' e2)
 | fst_exp e1 =>
   fst_exp (subst x e' e1)
 | snd_exp e1 =>
   snd_exp (subst x e' e1)
 | unit_exp => unit_exp
 | if_exp e1 e2 e3 => if_exp (subst x e' e1) 
   (subst x e' e2) (subst x e' e3)
 | true_exp => true_exp
 | false_exp => false_exp
 | (send_exp e1 e2) => (send_exp (subst x e' e1) 
   (subst x e' e2))
 | (spawn_exp st T' e1) => 
   (spawn_exp st T' (subst x e' e1))
 | (set_exp e1) =>  (set_exp (subst x e' e1))
 | (get_exp) =>(get_exp)
 | (receive_exp m T' e1 e2) => (receive_exp m T' 
   (if eq_id_dec x m then e1 else (subst x e' e1)) 
   (subst x e' e2))
 | (become_exp e1) => (become_exp (subst x e' e1))
 | self_exp => self_exp
 | (seq_exp e1 e2) => (seq_exp (subst x e' e1) 
   (subst x e' e2))
 | val_exp p => val_exp p
 | stop_exp => stop_exp
 | (guard_exp m T' e1 e2 e3) => (guard_exp m T' (subst x e' e1) 
   (if eq_id_dec x m then e2 else (subst x e' e2)) 
   (subst x e' e3))
end.

(* append_mail_box is a function which appends an expression
    with the mail_box at its end. *)
Fixpoint append_mail_box (M : mail_box) (e : exp) : mail_box :=
match M with 
 | nil => e :: nil
 | e1 :: M1 => e1 :: (append_mail_box M1 e)
end.

(* append_cty is a function which appends a communication type
    with the list of communication types at its end. *)
Fixpoint append_cty (C : list cty) (c : cty) : list cty :=
match C with 
 | nil => c :: nil
 | c1 :: C1 => c1 :: (append_cty C1 c)
end.

(* is_equal_process_global_conf checks whether two list of 
    configurations are equal or not. *)
Hypothesis is_equal_global_conf : forall c1 c2 : global_conf, 
{c1 = c2} + {c1 <> c2}.

(* is_equal_id checks whether two ids are equal or not. *)
Theorem is_equal_id : forall id1 id2 : id, 
{id1 = id2} + {id1 <> id2}.
Proof.
 intros.
 destruct id1.
 destruct id2.
 destruct (eq_nat_dec n n0).
 left.
 rewrite -> e.
 reflexivity.
 right.
 intros contra.
 inversion contra.
 apply n1.
 apply H0.
Qed.

(* is_equal_exps checks whether two list of expressions are equal
or not. *)
Hypothesis is_equal_exps : forall e1 e2 : list exp, {e1 = e2} 
+ {e1 <> e2}.

(* is_equal_ty checks whether two value types are equal
or not. *)
Hypothesis is_equal_ty : forall T1 T2 : ty, {T1 = T2} 
+ {T1 <> T2}.

(* is_equal_cty checks whether two coomunication types are equal
or not. *)
Hypothesis is_equal_cty : forall C1 C2 : cty, {C1 = C2} 
+ {C1 <> C2}.

(* is_equal_mail_box checks whether two mail box are equal 
    or not. *)
Theorem is_equal_mail_box : forall m1 m2 : mail_box, 
{m1 = m2} + {m1 <> m2}.
Proof.
 intros.
 destruct m1.
 destruct m2.
 left.
 reflexivity.
 right.
 intros contra.
 inversion contra.
 destruct (is_equal_exps (e :: m1) m2).
 left. assumption.
 right.
 intros contra.
 inversion contra.
 apply n. assumption.
Qed.

(* is_equal_state checks whether two state declaration are equal
or not. *)
Hypothesis is_equal_state : forall st1 st2 :  process_st, 
{st1 = st2} + {st1 <> st2}.

(* This hypothesis states that two process configuration pConf1 
and pConf2 are either equal or not equal. *)
Lemma is_equal_process_conf : forall pConf1 pConf2 : 
process_conf, {pConf1 = pConf2} + {pConf1 <> pConf2}.
Proof.
 intros.
 destruct pConf1.
 destruct pConf2.
 destruct (is_equal_exp e e1).
 destruct (is_equal_mail_box m m0).
 destruct (is_equal_state p p0).
 destruct (is_equal_exp e0 e2).
 left.
 rewrite -> e3.
 rewrite -> e4.
 rewrite -> e5.
 rewrite -> e6.
 reflexivity.
 right.
 intros contra.
 inversion contra.
 apply n.
 assumption.
 right.
 intros contra.
 inversion contra.
 apply n.
 assumption.
 right.
 intros contra.
 inversion contra.
 apply n.
 assumption.
 right.
 intros contra.
 inversion contra.
 apply n.
 assumption.
Qed.

(* is_mem_process_global_conf checks whether a process p 
    is present in the global_conf or not *)
Fixpoint is_mem_process_global_conf (p : exp) (P : global_conf) : bool :=
match P with 
 | empty_comp _ => false
 | (Sigma sts e M' p1) |: P1' => match is_equal_exp 
   p p1 with 
 | left _ => true
 | right _ => is_mem_process_global_conf p (P1')
end
end.

(* fresh states that process address p is fresh that means it is 
   not present in any of the process configuration in the 
   global_conf P. *)
Inductive fresh (p : exp) (P : global_conf) : Prop :=
 | fresh_address : is_mem_process_global_conf p P = false ->
                             fresh p P.

Hypothesis h : forall v'' T' x' v''' e v M p st' e' M' v' P, 
 is_mem_process_global_conf v''
 (Sigma (st_decl T' x' v''') e (v :: M) (val_exp p)
 |: Sigma st' e' M' v' |: P) = false.

(* default function states that the default value v is of type T. *)
Inductive default (v : exp) : ty -> Prop :=
 | default_val : forall T,
                 default v T.

(** TYPING **)

Definition typing_env := partial_map ty.

(** AUXILIARY FUNCTIONS **)

Definition empty {A:Type} : partial_map A := (fun _ => None).

Definition extend {A:Type} (Gamma : partial_map A) (x:id) 
(T : A) := fun x' => if eq_id_dec x x' then Some T else Gamma x'.

(** SUBTYPING **)
(* subtype takes two types as arguments and states that 
    one is subtype of another. *)

Inductive subtype_ty : ty -> ty -> Prop :=
 | reflexive_subtype_ty : forall T,
   subtype_ty T T
 | transitive_subtype_ty : forall S U T,
   subtype_ty S U ->
   subtype_ty U T ->
   subtype_ty S T
 | arrow_subtype_ty : forall T1 T2 T1' T2' C C',
   subtype_ty T2 T1 ->
   subtype_ty T1' T2' ->
   subtype_cty C C' ->
   subtype_ty (arrow_ty T1 C T1') (arrow_ty T2 C' T2')
with 
 subtype_cty : cty -> cty -> Prop :=
 | reflexive_subtype_cty : forall C,
   subtype_cty C C
 | transitive_subtype_cty : forall S U T,
   subtype_cty S U ->
   subtype_cty U T ->
   subtype_cty S T
 | par_subtype_cty : forall C1 C1' C2 C2',
   subtype_cty C1 C1' ->
   subtype_cty C2 C2' ->
   subtype_cty (par C1 C2) (par C1' C2')
 | choice_subtype_cty1 : forall C1 C1' C2 C2',
   subtype_cty C1 C1' ->
   subtype_cty C2 C2' ->
   subtype_cty (choice C1 C2) C1' 
 | choice_subtype_cty2 : forall C1 C1' C2 C2',
   subtype_cty C1 C1' ->
   subtype_cty C2 C2' ->
   subtype_cty (choice C1 C2) C2'
 | choice_subtype_cty3 : forall C1' C1 C2,
   subtype_cty C1' C1 ->
   subtype_cty C1' (choice C1 C2)
 | choice_subtype_cty4 : forall C2' C1 C2,
   subtype_cty C2' C2 ->
   subtype_cty C2' (choice C1 C2)
 | seq_subtype_cty1 : forall C' C1,
   seq_subtype C' C1 -> 
   subtype_cty (seq C') (seq C1)
 | null_subtype_cty : forall C,
   subtype_cty null C
 | seq_subtype_cty2 : forall C C',
   In C' C ->
   subtype_cty C' (seq C)
with seq_subtype : list cty -> list cty -> Prop := 
 | seq_sub1 : forall C1 C1' Cn Cn',
   subtype_cty C1 C1' ->
   seq_subtype Cn Cn' ->
   seq_subtype (C1 :: Cn) (C1' :: Cn').


(* is_mem_cty is a relation that checks whether type  receive type T is 
    present in the communication type or not. *)
Inductive is_mem_cty : cty -> cty -> bool -> Prop :=
 | is_mem_null : forall T, is_mem_cty (r_cty T) null false
 | is_mem_par1 : forall C1 C2 T,
                          is_mem_cty (r_cty T) C1 true ->
                          is_mem_cty (r_cty T) (par C1 C2) true 
 | is_mem_par2 : forall C1 C2 T,
                          is_mem_cty (r_cty T) C2 true ->
                          is_mem_cty (r_cty T) (par C1 C2) true 
 | is_mem_choice1 : forall C1 C2 T,
                               is_mem_cty (r_cty T) C1 true ->
                               is_mem_cty (r_cty T) (choice C1 C2) true
 | is_mem_choice3 : forall C1 C2 T,
                               is_mem_cty (r_cty T) C2 true ->
                               is_mem_cty (r_cty T) (choice C1 C2) true
 | is_mem_seq1 : forall C1' C1'' T,
                           is_mem_cty (r_cty T) C1' true ->
                           is_mem_cty (r_cty T) (seq (C1' :: C1'')) true
 | is_mem_seq2 : forall C1' C1'' T,
                         is_mem_cty (r_cty T) C1' false ->
                         is_mem_list_cty (r_cty T) C1'' true ->
                         is_mem_cty (r_cty T) (seq (C1' :: C1'')) true
 | is_mem_r_ty : forall T, is_mem_cty (r_cty T) (r_cty T) true
 | is_mem_s_ty : forall T, is_mem_cty (r_cty T) (s_cty T) false

with 

is_mem_list_cty : cty -> list cty -> bool -> Prop :=
 | is_mem_nil : forall T, is_mem_list_cty (r_cty T) nil false
 | is_mem1 : forall C'' C''' T,
                   is_mem_cty (r_cty T) C'' true ->
                   is_mem_list_cty (r_cty T) (C'' :: C''') true
 | is_mem2 : forall C'' C''' T,
                   is_mem_cty (r_cty T) C'' false ->
                   is_mem_list_cty (r_cty T) C''' true ->
                   is_mem_list_cty (r_cty T) (C'' :: C''') true.


(* updated_cty is a relation that cuts the communication types 
    from the receive type and ignores all the states in which process
    might have enaged before receiving the message. *)
Inductive updated_cty : cty -> cty -> cty -> Prop :=
 | updated_null : forall T,
                           updated_cty (r_cty T) null null
 | updated_send : forall T,
                             updated_cty (r_cty T) (s_cty T) null
 | updated_parallel1 : forall T C2 C2',
                                  updated_cty (r_cty T) C2 C2' ->
                                  updated_cty (r_cty T) (par null C2) C2'
 | updated_parallel2 : forall T C1 C1',
                                  updated_cty (r_cty T) C1 C1' ->
                                  updated_cty (r_cty T) (par C1 null) C1'
 | updated_parallel3 : forall T C1 C2' C1' C2,
                                  updated_cty (r_cty T) C1 C1' ->
                                  updated_cty (r_cty T) C2 C2' ->
                                  updated_cty (r_cty T) (par C1 C2) (choice C1' C2')
 | updated_choice1 : forall T C2 C2',
                                 updated_cty (r_cty T) C2 C2' ->
                                 updated_cty (r_cty T) (choice null C2) C2'
 | updated_choice2 : forall T C1 C1',
                                 updated_cty (r_cty T) C1 C1' ->
                                 updated_cty (r_cty T) (choice C1 null) C1'
 | updated_choice3 : forall T C1 C2' C1' C2,
                                 updated_cty (r_cty T) C1 C1' ->
                                 updated_cty (r_cty T) C2 C2' ->
                                 updated_cty (r_cty T) (choice C1 C2) (choice C1' C2')
 | updated_receive : forall T,
                                updated_cty (r_cty T) (r_cty T) (r_cty T)
 | updated_seq : forall T C2 C1 C1',
                           updated_list_cty (r_cty T) (C1 :: C2) C1' ->
                           updated_cty (r_cty T) (seq (C1 :: C2)) (seq C1')
with 
updated_list_cty : cty -> list cty -> list cty -> Prop :=
 | update_nil : forall T, updated_list_cty (r_cty T) nil [null]
 | update1 : forall C1 C1' C2' T C2,
                   updated_cty (r_cty T) C1 C1' ->
                   updated_list_cty (r_cty T) C2 C2' ->
                   updated_list_cty (r_cty T) (C1 :: C2) (C1' :: C2').

(* Static type rules for the expressions. *)
Inductive has_type : typing_env -> exp -> ty -> cty -> Prop :=
 | T_send_exp : forall e e' T T' C C' C'' Gamma C''',
   has_type Gamma e' T' C' ->
   has_type Gamma e (process_ty T C) C'' ->
   is_mem_cty (r_cty T') C true ->
   In C' (append_cty (C' :: C'' :: s_cty T' :: nil) (C''')) ->
   updated_cty (r_cty T') C C''' ->
   has_type Gamma (send_exp e e') T' 
   (seq (append_cty (C' :: C'' :: s_cty T' :: nil) (C''')))
 | T_spawn_exp : forall e x T T' C' self_st Gamma,
   has_type (extend Gamma self_st T) e T' C' ->
   Gamma self_st = Some T' ->
   has_type Gamma (spawn_exp x T e) (process_ty T' C') null
 | T_receive_exp : forall x e e' T T' C' C'' Gamma,
   has_type (extend Gamma x T) e T' C' ->
   In C' [r_cty T ; C'] ->
   has_type Gamma e' T' C'' ->
   has_type Gamma (receive_exp x T e e') T' (choice (seq [r_cty T ; C']) C'')
 | T_become_exp : forall e T C Gamma,
   has_type Gamma e T C ->
   has_type Gamma (become_exp e) T C
 | T_set_exp : forall e self_st T T' C' Gamma,
   Gamma self_st = Some T ->
   has_type Gamma e T' C' ->
   subtype_ty T' T ->
   has_type Gamma (set_exp e) T C'
 | T_get_exp : forall self_st T Gamma,
   Gamma self_st = Some T ->
   has_type Gamma (get_exp) T null
 | T_self_exp : forall Gamma C T',
   has_type Gamma (self_exp) (process_ty T' C) null
 | T_pair_exp : forall Gamma e1 e2 T T' C C',
   has_type Gamma e1 T C ->
   has_type Gamma e2 T' C' ->
   In C [C ; C'] ->
   In C' [C ; C'] ->
   has_type Gamma (pair_exp e1 e2) (prod_ty T T') (seq [C ; C'])
 | T_fst_exp : forall Gamma e T T' C,
   has_type Gamma e (prod_ty T T') C ->
   has_type Gamma (fst_exp e) T C
 | T_snd_exp : forall Gamma e T T' C,
   has_type Gamma e (prod_ty T T') C ->
   has_type Gamma (snd_exp e) T' C
 | T_true_exp : forall Gamma,
   has_type Gamma true_exp bool_ty null
 | T_false_exp : forall Gamma,
   has_type Gamma false_exp bool_ty null
 | T_abs_exp : forall Gamma x T T' e C,
   has_type (extend Gamma x T) e T' C ->
   has_type Gamma (abs_exp x T e) (arrow_ty T C T') null
 | T_app_exp : forall T T' Gamma e e' C C' C'',
   has_type Gamma e (arrow_ty T C'' T') C -> 
   has_type Gamma e' T C' ->
   In C [C ; C'; C''] ->
   In C' [C ; C' ; C''] ->
   In C'' [C ; C' ; C''] ->
   has_type Gamma (app_exp e e') T' (seq [C ; C' ; C''])
 | T_unit_exp : forall Gamma,
   has_type Gamma unit_exp unit_ty null
 | T_nat_exp : forall Gamma n1,
   has_type Gamma (nat_exp n1) nat_ty null
 | T_if_exp : forall Gamma e1 e2 e3 T C C' C'',
   has_type Gamma e1 bool_ty C ->
   has_type Gamma e2 T C' ->
   has_type Gamma e3 T C'' ->
   In C [C ; (choice C' C'')] ->
   In (choice C' C'') [C; choice C' C''] ->
   has_type Gamma (if_exp e1 e2 e3) T (seq [C ; (choice C' C'')])
 | T_seq_exp : forall Gamma e e' T T' C C',
   has_type Gamma e T C ->
   has_type Gamma e' T' C' ->
   In C [C ; C'] ->
   In C' [C ; C'] ->
   has_type Gamma (seq_exp e e') T' (seq [C ; C'])
 | T_var_exp : forall Gamma x T,
   Gamma x = Some T ->
   has_type Gamma (var_exp x) T null
 | T_val_exp : forall Gamma x T' C',
   has_type Gamma (val_exp x) (process_ty T' C') null
 | T_guard_exp : forall x e e' e'' T T' C C' C'' Gamma,
   has_type (extend Gamma x T) e' T' C'   ->
   has_type Gamma e bool_ty C  ->
   has_type Gamma e'' T' C'' ->
   In C' (append_cty [C] (choice (seq [r_cty T ; C']) C'')) ->
   In C'' (append_cty [C] (choice (seq [r_cty T; C']) C'')) ->
   has_type Gamma (guard_exp x T e e' e'') T' 
  (seq (append_cty [C] (choice (seq [r_cty T ; C']) C''))).

(* Subsume rule for the value type. *)
Axiom subsume_ty: forall Gamma e T T' C,
 has_type Gamma e T' C ->
 subtype_ty T' T ->
 has_type Gamma e T C.

(* Subsume rule for the communication type. *)
Axiom subsume_cty : forall Gamma e T C' C,
   has_type Gamma e T C' ->
   subtype_cty C' C ->
   has_type Gamma e T C.

(* concat_actions cocatenates two set of actions. *)
Fixpoint concat_actions (a1 : list action) (a2 : list action) : list action :=
match a2 with
 | nil => nil
 | cons x l => cons x (concat_actions a1 l)
end.

(* Operational Semantics rules for the configuration. *)
Inductive step : global_conf -> action -> global_conf -> Prop :=
 | ST_state_asgn1 : forall v' x T M p v''' P st' 
   e' v M' v'' ,
   step (Sigma (st_decl T x v''') (set_exp v') 
   (v :: M) (val_exp p) |: 
   (Sigma st' e' M' v'') |: P) 
   (set (val_exp p))
   (Sigma (st_decl T x v') v' (v :: M) 
   (val_exp p) |: (Sigma st' e' M' v'') |: P)
 | ST_state_asgn2 : forall a e x v'' T p M P P' st' 
   e' M' v v' st'' e'' M'' st''' e''' M''',
   step (Sigma (st_decl T x v'') e (v :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) a 
   (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P') ->
   step (Sigma (st_decl T x v'') (set_exp e) (v :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) a
   (Sigma st'' (set_exp e'') M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P')
 | ST_state_read : forall x v T M p P st' e' 
   M' v' v'',
   step (Sigma (st_decl T x v) (get_exp) (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v'') |: P) 
   (get (val_exp p))
   (Sigma (st_decl T x v) v (v' :: M) (val_exp p) |: 
   (Sigma st' e' M' v'') |: P)
 | ST_send_exp1 : forall v v' v'' v''' st' e' M' x T
   M p P,
   value v ->
   value v' ->
   step (Sigma (st_decl T x v''') (send_exp v v') 
   (v'' :: M) (val_exp p) |: 
   (Sigma st' e' M' v) |: P) 
   (send v' (val_exp p) v)
   (Sigma (st_decl T x v''') v' (v'' :: M) 
   (val_exp p) |: 
   (Sigma st' e' (append_mail_box M' v') v) |: P)
 | ST_send_exp2 : forall v a e e' x' T' st' M M' p 
   P P' st'' e'' M'' st''' e''' M''' v' v'' v''',
   value v ->
   step (Sigma (st_decl T' x' v''') e (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) a 
   (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P') ->
   step (Sigma (st_decl T' x' v''') (send_exp e v) 
   (v'' :: M) (val_exp p) |: 
   (Sigma st' e' M' v') |: P) a 
   (Sigma st'' (send_exp e'' v) M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P')
 | ST_send_exp3 : forall v a e e' x T st' M M' p P P' 
   st'' e'' M'' st''' e''' M''' v' v'' v''',
   value v ->
   step (Sigma (st_decl T x v''') e (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) a 
   (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P') ->
   step (Sigma (st_decl T x v''') (send_exp v e) 
   (v'' :: M) (val_exp p) |: 
   (Sigma st' e' M' v') |: P) a
   (Sigma st'' (send_exp v e'') M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P')
 | ST_send_exp4 : forall e2 a e1 e' x T st' M M' 
   p P P' st'' e1' M'' st''' e''' M''' v v' v''',
   step (Sigma (st_decl T x v''') e1 (v :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) a 
   (Sigma st'' e1' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P') ->
   step (Sigma (st_decl T x v''') (send_exp e1 e2) 
   (v :: M) (val_exp p) |: 
   (Sigma st' e' M' v') |: P) a 
   (Sigma st'' (send_exp e1' e2) M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P')
 | ST_receive_exp1 : forall v T T' x' x e e' M p st'
   e'' M' v' P v'',
   value v ->
   has_type empty v T null ->
   step (Sigma (st_decl T' x' v'') 
   (receive_exp x T e e') (v :: M) (val_exp p) |: 
   (Sigma st' e'' M' v') |: P) 
   (receive v (val_exp p))
   (Sigma (st_decl T' x' v'') (subst x v e) M 
   (val_exp p) |: (Sigma st' e'' M' v') |: P)
 | ST_receive_exp2 : forall v T T' T'' x' e e' x M p 
   st' e'' M' v' v'' P,
   has_type empty v T'' null ->
   step (Sigma (st_decl T' x' v'') 
   (receive_exp x T e e') (v :: M) (val_exp p) |: 
   (Sigma st' e'' M' v') |: P) 
   (receive v (val_exp p))
   (Sigma (st_decl T' x' v'') (e') (v :: M) 
   (val_exp p) |: (Sigma st' e'' M' v') |: P)
 | ST_become_exp : forall T x e M p st' e' M' v v' 
   v'' P,
   step (Sigma (st_decl T x v'') (become_exp e) 
   (v :: M) (val_exp p) |: 
   (Sigma st' e' M' v') |: P) 
   (become (val_exp p))
   (Sigma (st_decl T x v'') e (v :: M) (val_exp p) |: 
   (Sigma st' e' M' v') |: P)
 | ST_spawn_exp : forall T' x' M p T x v st'' e e'' 
   M'' v'' v''' v' v1 P,
   default v' T ->
   fresh v (Sigma (st_decl T' x' v''') 
   (spawn_exp x T e) (v1 :: M) (val_exp p) |: 
   (Sigma st'' e'' M'' v'') |: P) ->
   step (Sigma (st_decl T' x' v''') (spawn_exp x T e) 
   (v1 :: M) (val_exp p) |: 
   (Sigma st'' e'' M'' v'') |: P) 
   (spawn (val_exp p) v)
   (Sigma (st_decl T' x' v''') v (v1 :: M) 
   (val_exp p) |: (Sigma st'' e'' M'' v'') |:
   (Sigma (st_decl T x v') e nil v) |: P)
 | ST_self_exp : forall T x M p st' e' M' v v' 
   v'' P,
   step (Sigma (st_decl T x v'') (self_exp) 
   (v :: M) (val_exp p) |: 
   (Sigma st' e' M' v') |: P) 
   (self)
   (Sigma (st_decl T x v'') (val_exp p) (v :: M) (val_exp p) |: 
   (Sigma st' e' M' v') |: P)
 | ST_app_abs : forall T' x' x T1 e1 v M p st' e' M' 
   v' v'' v''' v1 P,
   value v1 ->
   step (Sigma (st_decl T' x' v''') 
   (app_exp (abs_exp x T1 e1) v1) (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) 
   (local (val_exp p))
   (Sigma (st_decl T' x' v''') (subst x v1 e1) 
   (v :: M) (val_exp p) |: 
   (Sigma st' e' M' v') |: P)
 | ST_app_exp1 : forall T' x' st' e1 e2 M p P a e1' 
   M' P' st'' M'' st''' e''' M''' v v' v''' e',
   step (Sigma (st_decl T' x' v''') e1 (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' e1' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P') ->
   step (Sigma (st_decl T' x' v''') (app_exp e1 e2) 
   (v' :: M) (val_exp p) |: 
   (Sigma st' e' M' v) |: P) a 
   (Sigma st'' (app_exp e1' e2) M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_app_exp2 : forall T x st' e1 e2 M p P a e2' 
   M' st'' M'' st''' e''' M''' e' v v' v''' P',
   value e1 ->
   step (Sigma (st_decl T x v''') e2 (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' e2' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P') ->
   step (Sigma (st_decl T x v''') (app_exp e1 e2) 
   (v' :: M) (val_exp p) |: 
   (Sigma st' e' M' v) |: P) a 
   (Sigma st'' (app_exp e1 e2') M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_pair_exp1 : forall T x st' e1 e2 M p P a e1'
   M' st'' M'' st''' e''' M''' e' v v' v''' P',
   step (Sigma (st_decl T x v''') e1 (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' e1' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P') ->
   step (Sigma (st_decl T x v''') (pair_exp e1 e2) 
   (v' :: M) (val_exp p) |: (Sigma st' e' M' v) |: P) 
   a 
   (Sigma st'' (pair_exp e1' e2) M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_pair_exp2 : forall T x e1 e2 M p P a e2' st' e' 
   M' v v' v''' st'' M'' st''' e''' M''' P',
   value e1 ->
   step (Sigma (st_decl T x v''') e2 (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' e2' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P') ->
   step (Sigma (st_decl T x v''') (pair_exp e1 e2) 
   (v' :: M) (val_exp p) |: 
   (Sigma st' e' M' v) |: P) a 
   (Sigma st'' (pair_exp e1 e2') M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_fst_exp1 : forall T x st' e M p P a e' M' 
   st'' e'' M'' st''' e''' M''' v v' v''' P',
   step (Sigma (st_decl T x v''') e (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P') ->
   step (Sigma (st_decl T x v''') (fst_exp e) 
   (v' :: M) (val_exp p) |: 
   (Sigma st' e' M' v) |: P) a 
   (Sigma st'' (fst_exp e'') M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_fst_exp2 : forall T x e1 e2 M p st' e' M' 
   v v' v''' P,
   value e1 ->
   value e2 ->
   step (Sigma (st_decl T x v''') 
   (fst_exp (pair_exp e1 e2)) (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) 
   (local (val_exp p))
   (Sigma (st_decl T x v''') (e1) (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P)
 | ST_snd_exp1 : forall T x st' e M p P a e' M' st'' 
   e'' M'' st''' e''' M''' v v' v''' P',
   step (Sigma (st_decl T x v''') e (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P') ->
   step (Sigma (st_decl T x v''') (snd_exp e) 
   (v' :: M) (val_exp p) |: (Sigma st' e' M' v) |: P) 
   a 
   (Sigma st'' (snd_exp e'') M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_snd_exp2 : forall T x e1 e2 M p st' e' M' v 
   v' v''' P,
   value e1 ->
   value e2 ->
   step (Sigma (st_decl T x v''') 
   (snd_exp (pair_exp e1 e2)) (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) 
   (local (val_exp p))
   (Sigma (st_decl T x v''') (e2) (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P)
 | ST_if_exp1 : forall T x e1 M p P e2 st' e' M' 
   v v' v''',
   step (Sigma (st_decl T x v''') 
   (if_exp true_exp e1 e2) (v' :: M) (val_exp p) |: 
   (Sigma st' e' M' v) |: P) 
   (local (val_exp p))
   (Sigma (st_decl T x v''') e1 (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P)
 | ST_if_exp2 : forall T x e1 M p P e2 st' e' M' 
   v v' v''',
   step (Sigma (st_decl T x v''') 
   (if_exp false_exp e1 e2) 
   (v' :: M) (val_exp p) |: (Sigma st' e' M' v) |: P) 
   (local (val_exp p))
   (Sigma (st_decl T x v''') e2 (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P)
 | ST_if_exp3 : forall T x st' e1 e1' e3 M M' p P P' 
   a e2 st'' e' M'' st''' e''' M''' v v' v''',
   step (Sigma (st_decl T x v''') e1 
   (v' :: M) (val_exp p) |: (Sigma st' e' M' v) |: P) 
   a 
   (Sigma st'' e1' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P') ->
   step (Sigma (st_decl T x v''') 
   (if_exp e1 e2 e3) (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' (if_exp e1' e2 e3) M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_seq_exp1 : forall T x st' e1 e1' M p P P' a e2 
   st'' e' M' v v' v''' st''' e''' M'' M''',
   step (Sigma (st_decl T x v''') e1 (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' e1' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P') ->
   step (Sigma (st_decl T x v''') (seq_exp e1 e2) 
   (v' :: M) (val_exp p) |: 
   (Sigma st' e' M' v) |: P) a 
   (Sigma st'' (seq_exp e1' e2) M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_seq_exp2 : forall T x st' e1 M M' p P P' a e2 
   st'' e' e''' st''' M''' M'' v v' v''',
   value e1 ->
   step (Sigma (st_decl T x v''') 
   (seq_exp e1 e2) (v' :: M) 
   (val_exp p) |: (Sigma st' e' M' v) |: P) a 
   (Sigma st'' e2 M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v) |: P')
 | ST_guard_exp1 : forall v T T' x' x e' M p st'
   e'' M' v' P v'' e''',
   value v ->
   has_type empty v T null ->
   step (Sigma (st_decl T' x' v'') 
   (guard_exp x T true_exp e' e'') (v :: M) (val_exp p) |: 
   (Sigma st' e''' M' v') |: P) 
   (receive v (val_exp p))
   (Sigma (st_decl T' x' v'') (subst x v e') M 
   (val_exp p) |: (Sigma st' e''' M' v') |: P)
 | ST_guard_exp2 : forall v T T' x' x e' M p st'
   e'' M' v' P v'' e''',
   value v ->
   has_type empty v T null ->
   step (Sigma (st_decl T' x' v'') 
   (guard_exp x T false_exp e' e'') (v :: M) (val_exp p) |: 
   (Sigma st' e''' M' v') |: P) 
   (receive v (val_exp p))
   (Sigma (st_decl T' x' v'') e'' M 
   (val_exp p) |: (Sigma st' e''' M' v') |: P)
 | ST_guard_exp3 : forall v T T' T'' x' e e' x M p 
   st' e'' M' v' v'' P e''',
   has_type empty v T'' null ->
   step (Sigma (st_decl T' x' v'') 
   (guard_exp x T e e' e'') (v :: M) (val_exp p) |: 
   (Sigma st' e''' M' v') |: P) 
   (receive v (val_exp p))
   (Sigma (st_decl T' x' v'') (e'') (v :: M) 
   (val_exp p) |: (Sigma st' e''' M' v') |: P).

(** FREE OCCURENCE **)

(* A variable [x] appears free in an expression e if it contains 
some occurrence of x that is not under an abstraction labelled x. *)
Inductive appears_free_in : id -> exp -> Prop :=
 | afi_send_exp1 : forall e e' x,
   appears_free_in x e ->
   appears_free_in x (send_exp e e')
 | afi_send_exp2 : forall x e e',
   appears_free_in x e' ->
   appears_free_in x (send_exp e e')
 | afi_receive_exp1 : forall T e e' x x',
   x <> x' ->
   appears_free_in x' e ->
   appears_free_in x' (receive_exp x T e e')
 | afi_receive_exp2 : forall T e e' x x',
   appears_free_in x' e' ->
   appears_free_in x' (receive_exp x T e e')
 | afi_become_exp : forall x e,
   appears_free_in x e ->
   appears_free_in x (become_exp e)
 | afi_spawn_exp1 : forall x x' T e,
   appears_free_in x e ->
   appears_free_in x (spawn_exp x' T e)
 | afi_spawn_exp2 : forall x T e,
   appears_free_in x (spawn_exp x T e)
 | afi_set_exp : forall x e,
   appears_free_in x e ->
   appears_free_in x (set_exp e)
 | afi_self_exp : forall x,
   appears_free_in x (self_exp)
 | afi_var_exp : forall x,
   appears_free_in x (var_exp x)
 | afi_val_exp : forall x,
   appears_free_in x (val_exp x)
 | afi_app_exp1 : forall x e1 e2,
   appears_free_in x e1 -> 
   appears_free_in x (app_exp e1 e2)
 | afi_app_exp2 : forall x e1 e2,
   appears_free_in x e2 -> 
   appears_free_in x (app_exp e1 e2)
 | afi_seq_exp1 : forall x e1 e2,
   appears_free_in x e1 -> 
   appears_free_in x (seq_exp e1 e2)
 | afi_seq_exp2 : forall x e1 e2,
   appears_free_in x e2 -> 
   appears_free_in x (seq_exp e1 e2)
 | afi_abs_exp : forall x y T e,
   y <> x  ->
   appears_free_in x e ->
   appears_free_in x (abs_exp y T e)
 | afi_pair_exp1 : forall x e1 e2,
   appears_free_in x e1 ->
   appears_free_in x (pair_exp e1 e2)
 | afi_pair_exp2 : forall x e1 e2,
   appears_free_in x e2 ->
   appears_free_in x (pair_exp e1 e2)
 | afi_fst_exp : forall x e,
   appears_free_in x e ->
   appears_free_in x (fst_exp e)
 | afi_snd_exp : forall x e,
   appears_free_in x e ->
   appears_free_in x (snd_exp e)
 | afi_if_exp1 : forall x e1 e2 e3,
   appears_free_in x e1 ->
   appears_free_in x (if_exp e1 e2 e3)
 | afi_if_exp2 : forall x e1 e2 e3,
   appears_free_in x e2 ->
   appears_free_in x (if_exp e1 e2 e3)
 | afi_if_exp3 : forall x e1 e2 e3,
   appears_free_in x e3 ->
   appears_free_in x (if_exp e1 e2 e3)
 | afi_stop : forall x,
   appears_free_in x (stop_exp)
 | afi_self_st : forall self_st e,
   appears_free_in self_st e
 | afi_get_exp : forall x,
   appears_free_in x (get_exp)
 | afi_guard_exp1 : forall T e e' e'' x x',
   appears_free_in x' e ->
   appears_free_in x' (guard_exp x T e e' e'')
 | afi_guard_exp2 : forall T e e' e'' x x',
   x <> x' ->
   appears_free_in x' e' ->
   appears_free_in x' (guard_exp x T e e' e'')
 | afi_guard_exp3 : forall T e e' e'' x x',
   appears_free_in x' e'' ->
   appears_free_in x' (guard_exp x T e e' e'').

Hint Constructors appears_free_in.

(* This axiom states that self_st can not be equal to other variables. *)
Axiom not_equal : forall (self_st x : id), self_st <> x.

(* This lemma states that Gamma' assigns the same type as 
Gamma to all the variables that appears free in e *)
Lemma context_invariance : forall Gamma Gamma' e T C,
has_type Gamma e T C ->
(forall x, appears_free_in x e -> Gamma x = Gamma' x)  ->
has_type Gamma' e T C.
Proof with eauto.
 intros. 
 generalize dependent Gamma'.
 induction H; intros Gamma' Heqv...
- (* Send *)
 apply T_send_exp with T C.
 apply IHhas_type1.
 intros. 
 rewrite <- Heqv. reflexivity.
 apply afi_send_exp2. assumption. 
 apply IHhas_type2.
 intros.
 rewrite <- Heqv. reflexivity. 
 apply afi_send_exp1. assumption. 
 assumption.
 assumption. 
 assumption.
- (* Spawn *)
 apply T_spawn_exp with self_st. 
 apply IHhas_type. 
 intros x0 Hafi. 
 unfold extend. rewrite <- Heqv. reflexivity. 
 apply afi_spawn_exp1. 
 assumption.  
 rewrite <- Heqv. assumption.
 apply afi_self_st.
- (* Receive *)
 apply T_receive_exp. 
 apply IHhas_type1.
 intros x0 Hafi.
 unfold extend. destruct (eq_id_dec x x0). reflexivity.
 rewrite <- Heqv. reflexivity. 
 apply afi_receive_exp1. assumption.
 assumption. assumption.
 apply IHhas_type2. 
 intros. 
 unfold extend.
 rewrite <- Heqv. reflexivity. 
 apply afi_receive_exp2. assumption.
- (* Become *) 
 apply T_become_exp.
 apply IHhas_type. 
 intros.
 rewrite <- Heqv. reflexivity.
 apply afi_become_exp. assumption.
- (* Set *)
 apply T_set_exp with self_st T'.
 rewrite <- Heqv.  assumption.
 apply afi_self_st.
 apply IHhas_type.
 intros. 
 apply Heqv. apply afi_set_exp.
 assumption. assumption.
- (* Get *)
 apply T_get_exp with self_st.
 rewrite<- Heqv. assumption.
 apply afi_get_exp.
- (* Self *)
 apply T_self_exp.
-(* Pair *)
 apply T_pair_exp. 
 apply IHhas_type1. 
 intros. rewrite<- Heqv. reflexivity. 
 apply afi_pair_exp1. assumption. 
 apply IHhas_type2. 
 intros. rewrite<- Heqv. reflexivity. 
 apply afi_pair_exp2. assumption. 
 assumption. assumption.
- (* First *)
 apply T_fst_exp with T'. 
 apply IHhas_type. 
 intros. rewrite<- Heqv. reflexivity. 
 apply afi_fst_exp. assumption. 
- (* Second *)
 apply T_snd_exp with T. 
 apply IHhas_type. 
 intros. rewrite<- Heqv. reflexivity. 
 apply afi_snd_exp. assumption.
- (* True *)
 apply T_true_exp.
-(* False *)
 apply T_false_exp.
- (* Abs *)
 apply T_abs_exp. 
 apply IHhas_type. 
 intros y Hafi. unfold extend. 
 destruct (eq_id_dec x y)...
- (*App *)
 apply T_app_exp with T. 
 apply IHhas_type1. 
 intros. apply Heqv.
 apply afi_app_exp1. assumption. 
 apply IHhas_type2.
 intros. apply Heqv. 
 apply afi_app_exp2. assumption. assumption.
 assumption. assumption.
- (* Unit *)
 apply T_unit_exp.
- (* Nat *)
 apply T_nat_exp.
- (* If *)
 apply T_if_exp. 
 apply IHhas_type1. 
 intros. rewrite <- Heqv. reflexivity.
 apply afi_if_exp1. assumption. 
 apply IHhas_type2. 
 intros. rewrite <- Heqv. reflexivity. 
 apply afi_if_exp2. assumption. 
 apply IHhas_type3. 
 intros. rewrite <- Heqv. reflexivity.
 apply afi_if_exp3. assumption.
 assumption. assumption.
- (* Seq *)
 apply T_seq_exp with T.
 apply IHhas_type1. 
 intros. rewrite <- Heqv. reflexivity. 
 apply afi_seq_exp1. assumption. 
 apply IHhas_type2. 
 intros. rewrite <- Heqv. reflexivity. 
 apply afi_seq_exp2. assumption.
 assumption. assumption.
- (* Var *)
 apply T_var_exp.
 rewrite <- Heqv. assumption. 
 apply afi_var_exp.
- (* Val *)
 apply T_val_exp.
- (* Guard *)
 apply T_guard_exp. 
 apply IHhas_type1.
 intros x0 Hafi. unfold extend.
 destruct (eq_id_dec x x0). reflexivity.
 rewrite <- Heqv. reflexivity.
 apply afi_guard_exp2. assumption.
 assumption.
 apply IHhas_type2. intros.
 rewrite <- Heqv. reflexivity.
 apply afi_guard_exp1. assumption.
 apply IHhas_type3. intros. unfold extend.
 rewrite <- Heqv. reflexivity.
 apply afi_guard_exp3. 
 assumption. assumption.
 assumption.
Qed.

Lemma extend_shadow : forall A (ctxt: partial_map A) t1 t2 x1 x2,
extend (extend ctxt x2 t1) x2 t2 x1 = extend ctxt x2 t2 x1.
Proof with auto.
 intros. 
 unfold extend. destruct (eq_id_dec x2 x1)...
Qed.

(** PROGRESS **)

Theorem progress : forall  T T' P e st M st' e' 
M' v v' v'' v''' v0 x' p C,
value v ->
value v0 ->
fresh v'' ((Sigma st e (v :: M) (val_exp p)) |: 
(Sigma st' e' M' v') |: P) ->
has_type empty e T C -> 
value e \/ exists st'', exists e'', exists M'', exists st''', 
exists e''', exists M''', exists v', exists a, exists P', exists T'', 
has_type empty v T'' null ->
step ((Sigma (st_decl T' x' v''') e (v :: M) (val_exp p)) |: 
(Sigma st' e' M' v') |: P) a 
((Sigma st'' e'' M'' (val_exp p)) |: 
(Sigma st''' e''' M''' v') |: P').
Proof.
 intros.
 remember (@empty ty) as Gamma.
 generalize dependent HeqGamma.
 induction H2;  intros HeqGamma; subst.
- (* Send *)
 right. 
 destruct IHhas_type1. 
 inversion H1. 
 apply fresh_address. assumption.
 reflexivity. 
 destruct IHhas_type2. 
 inversion H1. apply fresh_address. 
 assumption. reflexivity.
 exists (st_decl T' x' v'''). 
 exists e'0. exists (v :: M). exists st'. 
 exists e'. exists (append_mail_box M' e'0). 
 exists e. exists (send e'0 (val_exp p) e).
 exists P. exists T'0. intros.  
 apply ST_send_exp1.
 assumption. assumption. destruct H6. 
 exists x. destruct H6.
 exists (send_exp x0 e'0). destruct H6. 
  exists x1. destruct H6.
 exists x2. destruct H6. exists x3. 
 destruct H6. exists x4. 
 destruct H6. exists x5.
 destruct H6. exists x6. 
 destruct H6. exists x7.
 inversion H6. exists x8. intros. 
 apply ST_send_exp2. 
 assumption.
 apply H7. assumption.
 destruct IHhas_type2. 
 inversion H1. 
 apply fresh_address. 
 assumption. reflexivity. destruct H5.
 exists x. destruct H5. 
 exists (send_exp e x0). 
 destruct H5. exists x1. destruct H5.
 exists x2. destruct H5. exists x3.
 destruct H5. exists x4. 
 destruct H5. exists x5. 
 destruct H5. exists x6. destruct H5.
 exists x7. destruct H5. exists x8. intros.
 apply ST_send_exp3. 
 assumption.
 apply H5. assumption. 
 destruct H6. 
 exists x. destruct H6.
 exists (send_exp x0 e'0). 
 destruct H6. exists x1. 
 destruct H6. exists x2. destruct H6.
 exists x3. destruct H6. 
 exists x4. destruct H6. 
 exists x5. destruct H6. exists x6.
 destruct H6. exists x7. destruct H6.
 exists x8. intros. 
 apply ST_send_exp4. 
 apply H6. assumption.
- (* Spawn *)
 right. 
 exists (st_decl T' x' v'''). exists v''. 
 exists (v :: M). exists st'.
 exists e'. exists M'. exists v'. 
 exists (spawn (val_exp p) v''). 
 exists ((Sigma (st_decl T x v0) e nil v'') |: P).
 exists T. intros.
 apply ST_spawn_exp. 
 apply default_val.
 inversion H1. apply fresh_address. assumption.
(* Receive *)
- right. 
 destruct IHhas_type2.  
 inversion H1. 
 apply fresh_address. assumption.
 reflexivity. exists (st_decl T' x' v''').
 exists (subst x v e). exists M.
 exists st'. exists e'. exists M'. exists v'.
 exists (receive v (val_exp p)). exists P.
 exists T. 
 apply ST_receive_exp1. 
 assumption.
 exists (st_decl T' x' v''').
 exists e'0. exists (v :: M). exists st'. exists e'.
 exists M'. exists v'.
 exists (receive v (val_exp p)). exists P.
 inversion H3. inversion H4. inversion H5.
 inversion H6. inversion H7. inversion H8.
 inversion H9. inversion H10. inversion H11. inversion H12.
 inversion H12. exists x10. intros.
 apply ST_receive_exp2 with x10. 
 assumption.
(* Become *)
- right. exists (st_decl T' x' v'''). exists e. 
 exists (v :: M). exists st'. exists e'.
 exists M'. exists v'. exists (become (val_exp p)).
 exists P. exists T. intros. 
 apply ST_become_exp.
(* Set *)
- right. destruct IHhas_type.
 inversion H1. apply fresh_address. 
 assumption. reflexivity.
 exists (st_decl T' x' e). exists e. 
 exists (v :: M). exists st'. exists e'.
 exists M'. exists v'. 
 exists (set (val_exp p)).
 exists P. exists T. intros. 
 apply ST_state_asgn1. 
 destruct H5. exists x. destruct H5. 
 exists (set_exp x0). 
 destruct H5. exists x1.
 destruct H5. exists x2. destruct H5. 
 exists x3. destruct H5. exists x4.
 destruct H5. exists x5. destruct H5. 
 exists x6. destruct H5. exists x7.
 destruct H5. exists x8. intros.
 apply ST_state_asgn2. apply H5. assumption.
(* Get *)
- right. 
 exists (st_decl T' x' v'''). exists v'''. 
 exists (v :: M). exists st'. exists e'.
 exists M'. exists v'. exists (get (val_exp p)).
 exists P. exists T. intros. 
 apply ST_state_read.
(* Self *)
- right. 
 exists (st_decl T' x' v'''). exists (val_exp p).
 exists (v :: M). exists st'. exists e'.
 exists M'. exists v'. exists (self).
 exists P. exists T'. intros. 
 apply ST_self_exp.
(* Pair *)
- destruct IHhas_type1. 
 inversion H1. apply fresh_address. 
 assumption. reflexivity. 
 destruct IHhas_type2.
 inversion H1. apply fresh_address. 
 assumption. reflexivity. 
 left. apply pair_val. 
 assumption. assumption.
 right. destruct H5. 
 exists x. destruct H5. 
 exists (pair_exp e1 x0). destruct H5.
 exists x1. destruct H5. 
 exists x2. destruct H5. 
 exists x3. destruct H5. exists x4.
 destruct H5. exists x5. 
 destruct H5. exists x6. 
 destruct H5. exists x7. 
 destruct H5. exists x8. intros.
 apply ST_pair_exp2.
 assumption. apply H5. 
 assumption. right. destruct H4.
 exists x. destruct H4. exists (pair_exp x0 e2).
 destruct H4. exists x1. 
 destruct H4. exists x2. 
 destruct H4. exists x3. destruct H4.
 exists x4. destruct H4. 
 exists x5. destruct H4. 
 exists x6. destruct H4. 
 exists x7. destruct H4. exists x8.
 intros. 
 apply ST_pair_exp1. 
 apply H4. assumption.
(* Fst *)
- right. 
 destruct IHhas_type. 
 inversion H1. apply fresh_address. 
 assumption. reflexivity.
 inversion H3; subst; try solve by inversion.
 exists (st_decl T' x' v''').
 exists v1. exists (v :: M). exists st'. 
 exists e'. exists M'. exists v'. 
 exists (local (val_exp p)).
 exists P. exists T. intros. 
 apply ST_fst_exp2. 
 assumption. assumption.
 destruct H3. exists x. destruct H3. 
 exists (fst_exp x0). destruct H3.
 exists x1. destruct H3. exists x2. 
 destruct H3. exists x3. destruct H3.
 exists x4. destruct H3. exists x5. 
 destruct H3. exists x6. destruct H3.
 exists x7. destruct H3. exists x8. intros.
 apply ST_fst_exp1. 
 apply H3. assumption. 
(* Snd *)
- right. 
 destruct IHhas_type. 
 inversion H1. apply fresh_address. 
 assumption. reflexivity.
 inversion H3; subst; try solve by inversion.
 exists (st_decl T' x' v''').
 exists v'0. exists (v :: M). exists st'. 
 exists e'. exists M'. 
 exists v'. exists (local (val_exp p)).
 exists P. exists T. intros. 
 apply ST_snd_exp2. 
 assumption. assumption.
 destruct H3. exists x. destruct H3. 
 exists (snd_exp x0). destruct H3.
 exists x1. destruct H3. exists x2. 
 destruct H3. exists x3. destruct H3.
 exists x4. destruct H3. exists x5. 
 destruct H3. exists x6. destruct H3.
 exists x7. destruct H3. exists x8. intros. 
 apply ST_snd_exp1.
 apply H3. assumption.
(* True *)
- left. 
 apply true_val.
(* False *)
- left. 
 apply false_val.
(* Abs *)
- left. 
 apply abs_val.
(* App *)
- right. 
 destruct IHhas_type1. 
 inversion H1. apply fresh_address. 
 assumption. reflexivity.
 subst. destruct IHhas_type2. 
 inversion H1. apply fresh_address. 
 assumption. reflexivity.
 subst. inversion H5; subst; try (solve by inversion).
 exists (st_decl T' x' v''').
 exists (subst x e'0 e0). exists (v :: M). 
 exists st'. exists e'. exists M'.
 exists v'. exists (local (val_exp p)).
 exists P. exists T. intros. 
 apply ST_app_abs. assumption.
 destruct H6. exists x. destruct H6. 
 exists (app_exp e x0). 
 destruct H6. exists x1. destruct H6.
 exists x2. destruct H6. exists x3. 
 destruct H6. exists x4. 
 destruct H6. exists x5.
 destruct H6. exists x6. destruct H6. 
 exists x7. destruct H6. exists x8. intros.
 apply ST_app_exp2.
 assumption. 
 apply H6. assumption. 
 destruct H5. exists x. 
 destruct H5. exists (app_exp x0 e'0). 
 destruct H5. exists x1. destruct H5.
 exists x2. destruct H5. exists x3. 
 destruct H5. exists x4. 
 destruct H5. exists x5.
 destruct H5. exists x6. destruct H5. 
 exists x7. destruct H5. 
 exists x8. intros.
 apply ST_app_exp1. 
 apply H5. assumption.
(* Unit *)
- left. 
 apply unit_val.
(* Nat *)
- left. 
 apply nat_val.
(* If *)
- right. 
 destruct IHhas_type1. 
 inversion H1. apply fresh_address. 
 assumption. reflexivity.
 inversion H4; subst; try solve by inversion.
 exists (st_decl T' x' v'''). exists e2. 
 exists (v :: M). exists st'. exists e'.
 exists M'. exists v'.
 exists (local (val_exp p)). exists P. 
 exists T. intros.
 apply ST_if_exp1.
 exists (st_decl T' x' v'''). exists e3. 
 exists (v :: M). exists st'. exists e'. 
 exists M'. exists v'.
 exists (local (val_exp p)). exists P.
 exists T. intros.
 apply ST_if_exp2.
 destruct H4. exists x. destruct H4. 
 exists (if_exp x0 e2 e3). 
 destruct H4. exists x1.
 destruct H4. exists x2. destruct H4. 
 exists x3. destruct H4. exists x4. 
 destruct H4. exists x5.
 destruct H4. exists x6. destruct H4.
 exists x7. destruct H4. exists x8.
 intros. 
 apply ST_if_exp3. 
 apply H4. assumption.
(* Seq *)
- destruct IHhas_type1. 
 inversion H1. apply fresh_address. 
 assumption. reflexivity.
 right. 
 exists (st_decl T' x' v'''). exists e'0. 
 exists (v :: M). exists st'. 
 exists e'. exists M'.
 exists v'. exists (local (val_exp p)). exists P.
 exists T. intros. 
 apply ST_seq_exp2. assumption.
 destruct H4. right. 
 exists x. destruct H4. 
 exists (seq_exp x0 e'0). 
 destruct H4. exists x1.
 destruct H4. exists x2. destruct H4. 
 exists x3. destruct H4. exists x4. 
 destruct H4. exists x5.
 destruct H4. exists x6. destruct H4. 
 exists x7. destruct H4. 
 exists x8. intros.
 apply ST_seq_exp1. apply H4. assumption.
(* Var *)
- inversion H2.
(* Val *)
- left. 
 apply process_val.
- (* Guard *)
 right.
 destruct IHhas_type2. inversion H1.
 apply fresh_address. 
 assumption. reflexivity.
 inversion H4; subst; try solve by inversion.
 exists (st_decl T' x' v'''). 
 exists (subst x v e'0). exists M.
 exists st'. exists e'. exists M'. exists v'.
 exists (receive v (val_exp p)). exists P.
 exists T. intros. 
 apply ST_guard_exp1. 
 assumption. assumption.
 exists (st_decl T' x' v'''). exists e''. exists M.
 exists st'. exists e'. exists M'. exists v'.
 exists (receive v (val_exp p)). exists P.
 exists T. intros. 
 apply ST_guard_exp2. 
 assumption. assumption. 
 inversion H4. inversion H5. 
 inversion H6. inversion H7.
 inversion H8. inversion H9. 
 inversion H10. inversion H11.
 inversion H12. inversion H13.
 exists (st_decl T' x' v'''). exists e''. 
 exists (v :: M). exists st'.
 exists e'. exists M'. exists v'. 
 exists (receive v (val_exp p)).
 exists P. exists T'. intros. 
 apply ST_guard_exp3 with T'.
 assumption.
Qed.

Axiom free_in_context : forall x e T C Gamma,
 appears_free_in x e ->
 has_type Gamma e T C ->
 exists T', Gamma x = Some T'.

Axiom var_subst_comm : forall x T C C' e Gamma,
 appears_free_in x (var_exp x) ->
 has_type (extend Gamma x T) (var_exp x) T C ->
 has_type Gamma e T C' ->
 subtype_cty C' C.

(** SUBSTITUTION PRESERVE TYPING **)

(* Substitution preserve typing says that suppose we
    have an expression [e] with a free variable [x], and suppose we've been
    able to assign a type [T] to [e] under the assumption that [x] has
    some type [T1].  Also, suppose that we have some other term [e'] and
    that we've shown that [e'] has type [T1].  Then, since [e'] satisfies
    the assumption we made about [x] when typing [e], we should be
    able to substitute [e'] for each of the occurrences of [x] in [e]
    and obtain a new expression that still has type [T]. *)
Lemma substitution_preserves_typing : forall x e T' e' T C' C Gamma,
has_type (extend Gamma x T') e T C -> 
has_type empty e' T' C'  ->
has_type Gamma (subst x e' e) T C.
Proof with eauto.
intros x e T' e' T C' C Gamma Hs Ht.
generalize dependent Gamma.
generalize dependent T.
generalize dependent C.
induction e; intros T C Gamma H1; 
simpl; inversion H1; subst ; simpl...
(* Send *)
- apply T_send_exp with T0 C0. 
 apply IHe2. 
 assumption. 
 apply IHe1. assumption.
 assumption. 
 assumption. assumption.
(* Spawn *)
- rename i into y.
 apply T_spawn_exp with self_st. 
 apply IHe.
 eapply context_invariance... intros.
 unfold extend. destruct (eq_id_dec self_st x0).
 rewrite <- e0. subst. 
 rewrite neq_id. reflexivity.
 apply not_equal. reflexivity. 
 unfold extend in H7. rewrite neq_id in H7. 
 assumption. apply not_equal.
(* Receive *)
- rename i into y. rename t into T1. 
 apply T_receive_exp.
 destruct (eq_id_dec x y)... 
 eapply context_invariance... subst.
 intros x0 Hafi. unfold extend.
 destruct (eq_id_dec y x0)...
 apply IHe1. eapply context_invariance...
 intros x0 Hafi.
 unfold extend. destruct (eq_id_dec y x0)... 
 subst. rewrite neq_id... assumption.
 apply IHe2. assumption.
(* Become *)
- apply T_become_exp. 
 apply IHe. assumption.
(* Set *)
- apply T_set_exp with self_st T'0. 
 unfold extend in H0.
 rewrite neq_id in H0. 
 assumption. apply not_equal.
 apply IHe. assumption. assumption.
(* Get *)
- apply T_get_exp with self_st. 
 unfold extend in H.
 rewrite neq_id in H. assumption. 
 apply not_equal.
(* Self *)
- apply T_self_exp.
(* Pair *)
- apply T_pair_exp. 
 apply IHe1. assumption.
 apply IHe2. assumption. 
 assumption. assumption.
(* Fst *)
- apply T_fst_exp with T'0. 
 apply IHe. assumption.
(* Snd *)
- apply T_snd_exp with T0. 
 apply IHe. assumption.
(* True *)
- apply T_true_exp.
(* False *)
- apply T_false_exp.
(* Abs *)
- rename i into y. rename t into T11. 
 apply T_abs_exp... 
 destruct (eq_id_dec x y). subst.
 eapply context_invariance...
 subst. 
 intros x Hafi. unfold extend. 
 destruct (eq_id_dec y x)...
 apply IHe. eapply context_invariance... 
 intros x0 Hafi. unfold extend. 
 destruct (eq_id_dec y x0)...
 subst. rewrite neq_id...
(* App *)
- apply T_app_exp with T0. 
 apply IHe1. assumption. 
 apply IHe2. assumption.
 assumption. assumption. assumption.
(* Var *)
- rename i into y.
 destruct (eq_id_dec x y). subst.
 unfold extend in H2.
 destruct (eq_id_dec y y) in H2.
 (*rewrite extend_eq in H2.*)
 inversion H2; subst. clear H2.
 apply subsume_cty with C'.
 eapply context_invariance...
 intros x Hcontra.
 destruct (free_in_context _ _ C C' empty Hcontra) as [T' HT'].
 assumption. inversion HT'. 
 apply var_subst_comm with y C e' Gamma.
 apply afi_var_exp.
 assumption. apply context_invariance with empty.
 assumption. intros x H'. 
 destruct (free_in_context _ _ C C' empty H') as [T' HT'].
 assumption. inversion HT'. destruct n. reflexivity. 
 apply T_var_exp...
 unfold extend in H2. 
 destruct (eq_id_dec x y). destruct n. assumption.
 assumption.
(* Unit *)
- apply T_unit_exp.
(* Nat *)
- apply T_nat_exp.
(* If *)
- apply T_if_exp. 
 apply IHe1. assumption. 
 apply IHe2. assumption.
 apply IHe3. assumption.
 assumption. assumption.
(* Seq *)
- apply T_seq_exp with T0. 
 apply IHe1. assumption. 
 apply IHe2. assumption.
 assumption. assumption.
(* Val *)
- apply T_val_exp.
- (* Guard *)
 apply T_guard_exp. 
 inversion H1. subst.
 destruct (eq_id_dec x i). 
 apply context_invariance with (extend (extend Gamma x T') i t).
 assumption. intros. unfold extend.
 rewrite -> e. subst.
 destruct (eq_id_dec i x0).
 reflexivity. reflexivity.
 apply IHe2. 
 apply context_invariance with (extend (extend Gamma x T') i t).
 assumption. intros. unfold extend. 
 destruct (eq_id_dec i x0).
 rewrite <- e. rewrite neq_id. 
 reflexivity. assumption. reflexivity.
 apply IHe1. assumption. 
 apply IHe3. assumption. assumption.
 assumption.
Qed.

Theorem preservation : forall e e'' T' x' v''' v M p st' e' M' st'' 
M'' st''' e''' M''' v' P' P a T C,
has_type empty e T C  ->
step ((Sigma (st_decl T' x' v''') e (v :: M) (val_exp p)) |: 
(Sigma st' e' M' v') |: P) a 
((Sigma st'' e'' M'' (val_exp p)) |: 
(Sigma st''' e''' M''' v') |: P') ->
has_type empty e'' T C.
Proof with eauto.
 remember (@empty ty) as Gamma.
 intros e e'' T' x' v''' v M p st' e' M' st'' 
 M'' st''' e''' M''' v' P' P a T C HT.
 generalize dependent st''.
 generalize dependent e''.
 generalize dependent M''. 
 generalize dependent st'''.
 generalize dependent e'''.
 generalize dependent M'''.
 generalize dependent P'.
 induction HT;
 intros P' M''' e''' st''' M'' e1' st'' HE; subst Gamma; subst; 
 try solve [inversion HE; subst; auto].
(* Send *)
- inversion HE; subst... 
 apply subsume_cty with C'.
 assumption. apply seq_subtype_cty2.
 assumption.
 apply T_send_exp with T C. assumption.
 apply IHHT2 in H24. assumption. reflexivity.
 assumption. assumption. assumption.
 apply T_send_exp with T C.
 apply IHHT1 in H24. assumption. reflexivity.
 assumption.
 assumption. assumption. assumption.
 apply T_send_exp with T C. assumption.
 apply IHHT2 in H16. assumption. reflexivity.
 assumption. assumption. assumption.
(* Spawn *)
- inversion HE; subst.
 inversion H.
(* Receive *)
- inversion HE; subst. 
 apply substitution_preserves_typing with T null.
 apply subsume_cty with C'.
 assumption. apply choice_subtype_cty3.
 apply seq_subtype_cty2. assumption. 
 apply subsume_cty with null. assumption. 
 apply reflexive_subtype_cty.
 apply subsume_cty with C''. assumption.
 apply choice_subtype_cty4.
 apply reflexive_subtype_cty.
(* Set *)
- inversion H.
(* Get *)
- inversion H.
(* Self *)
- inversion HE; subst. 
 apply subsume_cty with null.
 apply T_val_exp. apply null_subtype_cty.
(* Pair *)
- inversion HE; subst.  
 apply T_pair_exp.
 apply IHHT1 in H15. assumption.
 reflexivity. assumption. assumption.
 assumption.  apply T_pair_exp. 
 assumption. apply IHHT2 in H23. 
 assumption. reflexivity. assumption.
 assumption.
(* Fst *)
- inversion HE; subst.
 apply T_fst_exp with T'0.
 apply IHHT in H12. assumption.
 reflexivity. inversion HT. subst.
 apply subsume_cty with C0.
 assumption. apply seq_subtype_cty2.
 assumption.
(* Snd *) 
- inversion HE; subst.
 apply T_snd_exp with T.
 apply IHHT in H12. assumption.
 reflexivity. inversion HT. subst.
 apply subsume_cty with C'.
 assumption. apply seq_subtype_cty2.
 assumption.
(* App *)
- inversion HE; subst.  
 apply substitution_preserves_typing with T C'.
 inversion HT1. apply subsume_cty with C''.
 assumption. apply seq_subtype_cty2. rewrite -> H4.
 assumption. assumption. apply IHHT1 in H16.
 apply T_app_exp with T. 
 assumption. assumption. assumption.
 assumption. assumption. reflexivity.
 apply IHHT2 in H24. apply T_app_exp with T. 
 assumption. assumption. assumption.
 assumption. assumption. reflexivity.
(* If *)
- inversion HE; subst. apply subsume_cty with (choice C' C'').
 apply subsume_cty with C'. 
 assumption. apply choice_subtype_cty3.
 apply reflexive_subtype_cty.
 apply seq_subtype_cty2. assumption.
 apply subsume_cty with (choice C' C'').
 apply subsume_cty with C''. 
 assumption. apply choice_subtype_cty4.
 apply reflexive_subtype_cty.
 apply seq_subtype_cty2. assumption.
 apply T_if_exp. apply IHHT1 in H16. assumption.
 reflexivity. assumption. assumption.
 assumption. assumption.
(* Seq *)
- inversion HE; subst. apply IHHT1 in H15. 
 apply T_seq_exp with T. 
 assumption. assumption. assumption.
 assumption. reflexivity.
 apply subsume_cty with C'.
 assumption. apply seq_subtype_cty2. assumption.
(* Guard *)
- inversion HE; subst. 
 apply substitution_preserves_typing with T null.
 apply context_invariance with (extend empty x T).
 apply subsume_cty with C'.
 assumption. 
 apply seq_subtype_cty2. assumption.
 intros. reflexivity. assumption. 
 apply subsume_cty with C''. assumption.
 apply seq_subtype_cty2. assumption.
 apply subsume_cty with C''. assumption.
 apply seq_subtype_cty2. assumption.
Qed.

(* multi denotes the multi step taken by a global configuration *)
Inductive multi : global_conf -> (list action) -> global_conf -> Prop :=
 | multi_step : forall T' x' v''' e v M p st' e' M' 
   P a st'' e'' M'' st''' e''' M''' v' P' st1 e1 M1 
   st2 e2 M2 tr P'',
   step ((Sigma (st_decl T' x' v''') e (v :: M) 
   (val_exp p)) |: (Sigma st' e' M' v') |: P) a 
   ((Sigma st'' e'' M'' (val_exp p)) |: 
   (Sigma st''' e''' M''' v') |: P') ->
   multi ((Sigma st'' e'' M'' (val_exp p)) |: 
   (Sigma st''' e''' M''' v') |: P') tr
   ((Sigma st1 e1 M1 (val_exp p)) |: 
   (Sigma st2 e2 M2 v') |: P'') ->
   multi ((Sigma (st_decl T' x' v''') e (v :: M) 
   (val_exp p)) |: (Sigma st' e' M' v') |: P) 
   (a :: tr)
   ((Sigma st1 e1 M1 (val_exp p)) |: 
   (Sigma st2 e2 M2 v') |: P'')
 | multi_refl : forall T' x' v''' e v M p st' e' 
   M' v' P a,
   step ((Sigma (st_decl T' x' v''') e (v :: M) 
   (val_exp p)) |: (Sigma st' e' M' v') |: P) a
   ((Sigma (st_decl T' x' v''') e (v :: M) 
   (val_exp p)) |: (Sigma st' e' M' v') |: P) ->
   multi ((Sigma (st_decl T' x' v''') e (v :: M) 
   (val_exp p)) |: (Sigma st' e' M' v') |: P) 
   (a :: nil)
   ((Sigma (st_decl T' x' v''') e (v :: M) 
   (val_exp p)) |: (Sigma st' e' M' v') |: P).

(* A global configuration in normal form is a configuration that 
   cannot make progress *)
Definition normal_form (P : global_conf) : Prop :=
~ exists P',
exists a, step P a P'.

Definition stuck (P : global_conf) (e : exp) : Prop :=
normal_form P /\ ~ (value e).

Theorem soundness: forall v0 T'' T T' x' v''' v'' e v M p st' e' M' P tr st'' 
e'' M'' v' st''' e''' M''' P' C,
value v ->
value v0 ->
value v'' ->
has_type empty v T'' null ->
has_type empty e T C ->
multi ((Sigma (st_decl T' x' v''') e (v :: M) (val_exp p)) |: (Sigma st' e' M' v') |: P) tr
((Sigma st'' e'' M'' (val_exp p)) |: (Sigma st''' e''' M''' v') |: P') ->
~ stuck ((Sigma st'' e'' M'' (val_exp p)) |: (Sigma st''' e''' M''' v') |: P') e''.
Proof.
 intros v0 T'' T T' x' v''' v'' e v M p st' e' M' P tr st'' 
 e'' M'' v' st''' e''' M''' P' C. 
 intros H1 H2 H3 H4 Hhas_type Hmulti.
 unfold stuck. intros [Hnf Hnot_val]. 
 unfold normal_form in Hnf.
 induction Hmulti. subst.
 apply progress with T T'0 P0 e (st_decl T'0 x'0 v'''0) M0 st'0 e'0 
 M'0 v v'0 v'' v'''0 v0 x'0 p0 C in Hhas_type.
 destruct Hhas_type;auto.
 assumption.
 assumption.
 apply fresh_address. apply h. 
 unfold normal_form in Hnf.
 apply preservation with e e'' T'0 x'0 v'''0 v0 M0 p0 st'0 e'0 M'0 st'' 
 M'' st''' e''' M''' v'0 P' P a T C in Hhas_type.
 unfold not in Hnf. apply Hnf.
 exists ((Sigma (st_decl T'0 x'0 v'''0) e0 (v1 :: M0) (val_exp p0)
 |: Sigma st'0 e'0 M'0 v'0 |: P0)). exists a. assumption.
 unfold not in Hnf. apply ex_falso_quodlibet. apply Hnf.
 exists ((Sigma (st_decl T'0 x'0 v'''0) e0 (v1 :: M0) (val_exp p0)
 |: Sigma st'0 e'0 M'0 v'0 |: P0)). exists a. assumption.
Qed.

Theorem guarenteed_delivery: forall T''' v0  v'' T'' T T' x' v''' 
e v M p st' e' M' P tr st'' e'' M'' v' st''' e''' M''' P' C,
value v ->
has_type empty v T''' null ->
default v0 T'' ->
value v'' ->
has_type empty e T C ->
multi ((Sigma (st_decl T' x' v''') e (v :: M) (val_exp p)) |: 
(Sigma st' e' M' v') |: P) tr
((Sigma st'' e'' M'' (val_exp p)) |: 
(Sigma st''' e''' M''' v') |: P') ->
normal_form ((Sigma st'' e'' M'' (val_exp p)) |: 
(Sigma st''' e''' M''' v') |: P') /\
~ stuck ((Sigma st'' e'' M'' (val_exp p)) |: 
(Sigma st''' e''' M''' v') |: P') e'' ->
M'' = nil.
Proof.
 intros T''' v0 v'' T'' T T' x' v''' e v M p 
 st' e' M' P tr st'' e'' M'' v' st''' e''' M''' P' C. 
 intros H1 H2 H3 H4 Hhas_type Hmulti.
 destruct M''. reflexivity. intros. destruct H.
 unfold not in H0. destruct H0.
 unfold stuck. split. assumption.
 induction Hmulti.
 apply IHHmulti. assumption.
 unfold normal_form in H. unfold not in H.
 destruct H.
 exists (Sigma (st_decl T'0 x'0 v'''0) e1 (v1 :: M0) (val_exp p0)
 |: Sigma st'0 e'0 M'0 v'0 |: P0). exists a. assumption.
Qed.

Inductive is_subset_action (t1 : list action) (t2 : list action) : bool -> Prop :=
	| nil_t1 : t1 = nil ->
		is_subset_action t1 t2 true
	| non_empty_t1 : forall t'2 t''2,
		t2 = t'2 ++ t1 ++ t''2 -> is_subset_action t1 t2 true.

(* adjacent_action represents two adjacent actions that means they 
    follow immediately after the other. *)
Inductive adjacent_action (a1 : action) (a2 : action) : Prop :=
| adj_act : forall t,
	In a1 t ->
	In a2 t ->
	is_subset_action [a1; a2] t true -> 
	adjacent_action a1 a2.

(* instance_of_process returns the process identifier of an action a.*)
Inductive instance_of_process : action -> exp -> Prop :=
 | ins1 : forall v' p v,
             instance_of_process (send v' p v) p
 |  ins2 : forall v p,
              instance_of_process (receive v p) p
 | ins3 : forall p,
             instance_of_process (become p) p
 | ins4 : forall p v,
             instance_of_process (spawn p v) p
 | ins5 : forall p,
             instance_of_process (get p) p
 | ins6 : forall p,
             instance_of_process (set p) p
 | ins7 : forall p,
             instance_of_process (local p) p.

(* This represents definiton 2 in the paper which states that
    two adjacent actions a1 and a2 in trace tr are neighbors 
    if they are performed by different process instance P1 and P2.*)
Inductive neighbors_action (a1 : action) (a2 : action) : Prop :=
 | neighbors : forall t P1 P2,
		In a1 t  ->
		In a2 t ->
		adjacent_action a1 a2 ->
		instance_of_process a1 = P1 ->
		instance_of_process a2 = P2 ->
		neighbors_action a1 a2.

(* commuting_act states that actions a1 and a2 commute if swapping
    them results in same final state. *)
Inductive commuting_action : action -> action -> Prop :=
	| commuting : forall P1 P2 a a' K K' K'',
		neighbors_action a a' ->
		instance_of_process a = P1 ->
		instance_of_process a' = P2 ->
		step K a K' /\ step K' a' K'' ->
		step K a' K' /\ step K' a K'' ->
		commuting_action a a'.

(* conflicting_action states that actions a1 and a2 conflict if swapping 
    them does not results in same final state. *)
Inductive conflicting_action : action -> action -> Prop :=
	| conflicting : forall a a' P1 P2,
		neighbors_action a a' ->
		instance_of_process a = P1 ->
		instance_of_process a' = P2 ->
		~ commuting_action a a' ->
		conflicting_action a a'.

(* right_mover_act states that actions a1 and a2 are neighbour actions 
    and if a1 is a right mover then swapping them results in same 
    final state. *)
Inductive right_mover_action : action -> Prop :=
	| right : forall P P' a a' K K1' K2' K'',
		neighbors_action a a' ->
		instance_of_process a = P ->
		instance_of_process a' = P' ->
		step K a K1' /\ step K1' a' K'' ->
		step K a' K2' /\ step K2' a K'' ->
		right_mover_action a.

(* left_mover_act states that actions a1 and a2 are neighbour actions 
   and if a2 is a left mover then swapping them results in same final state. *)
Inductive left_mover_action : action -> Prop :=
	| left : forall P P' a a' K K1' K2' K'',
		neighbors_action a a' ->
		instance_of_process a = P ->
		instance_of_process a' = P' ->
		step K a K1' /\ step K1' a' K'' ->
		step K a' K2' /\ step K2' a K'' ->
		left_mover_action a'.

Inductive non_mover_action : action -> Prop :=
	| non1 : forall a a' P P',
		neighbors_action a a' ->
		instance_of_process a  = P ->
		instance_of_process a' = P' ->
		~ left_mover_action a ->
		~ right_mover_action a ->
		non_mover_action a
	| non2 : forall a a' P P',
		neighbors_action a a' ->
		instance_of_process a = P ->
		instance_of_process a' = P' ->
		~ left_mover_action a' ->
		~ right_mover_action a' ->
		non_mover_action a' .

Inductive both_mover_action : action -> Prop :=
	| both : forall P a,
		instance_of_process a = P ->
		left_mover_action a ->
    right_mover_action a ->
    both_mover_action a.

(* happens_before represents happes before relation between 
   the actions in MPC. *)
Inductive happens_before : action -> action -> Prop :=
	| send_before_receive : forall v v' p,
		happens_before (send v' p v) (receive v' v)
	| send_before_become : forall v v' p,
		happens_before (send v' p v) (become v)
	| send_before_new : forall v' p v,
		happens_before (send v' p v) (spawn v v')
  | receive_before_receive : forall v p v' p',
    happens_before (send v p p') (send v' p p') ->
    happens_before (receive v p') (receive v' p').

(* Element at any position n in the trace. We need to assume 
   a default trace since it does not matter if position is some nat 
   and trace is empty. *)
Fixpoint trace_lookup (n:nat) (l: list action) (default : action) : action :=
 match n, l with
  | 0, x :: l' => x
  | 0, other => default
  | S m, nil => default
  | S m, x :: t => nth m t default
 end.

Inductive is_subset_upto_n : list action -> list action -> nat -> nat -> bool -> Prop :=
 	| non_empty_tr1 : forall tr'2 tr''2 tr1 tr2,
		tr2 = tr'2 ++ tr1 ++ tr''2 ->
    is_subset_upto_n tr1 tr2 (S (length tr'2)) (length tr'2 + length tr1) true
  | non_empty_tr'2 : forall tr'2 tr''2 tr1 tr2 ,
		tr2 = tr'2 ++ tr1 ++ tr''2 ->
    is_subset_upto_n tr'2 tr2 0 (length tr'2) true
  	| non_empty_tr''2 : forall tr'2 tr''2 tr1 tr2,
		tr2 = tr'2 ++ tr1 ++ tr''2 ->
    is_subset_upto_n tr''2 tr2 (S (length tr1)) (length tr'2 + length tr1 + length tr''2) true.


Inductive divide : list action -> list action -> list action -> list action -> Prop :=
 | divide_nil_actions : forall tr,
   tr = nil ->
   divide tr nil nil nil 
| divide_non_empty_actions : forall tr tr1 tr2 tr3,
  is_subset_upto_n tr1 tr 0 (length tr1) true ->
  is_subset_upto_n tr2 tr (S(length tr1)) (length tr1 + length tr2) true->
  is_subset_upto_n tr3 tr (S(length tr2)) (length tr1 + length tr2 + length tr3) true ->
  divide tr tr2 tr1 tr3.

(* append_actions is a function which appends list of actions*)
Fixpoint append_actions (C : list action) (c : list action) : list action :=
match C with 
 | nil => c 
 | c1 :: C1 => c1 :: (append_actions C1 c)
end.

Inductive lipton_reorder (tr : list action) : list action -> Prop :=
 | lipton_reorder1 : forall a a' tr1 tr2,
       divide tr [a;a'] tr1 tr2 ->
       right_mover_action a ->
       lipton_reorder tr (append_actions tr1 (append_actions [a' ; a] tr2))
 | lipton_reorder2 : forall a a' tr1 tr2,
       divide tr [a;a'] tr1 tr2 ->
       left_mover_action a' ->
       lipton_reorder tr (append_actions tr1 (append_actions [a' ; a] tr2))
 | lipton_reorder3 : forall a a' tr1 tr2,
       divide tr [a;a'] tr1 tr2 ->
       non_mover_action a' ->
       non_mover_action a ->
       lipton_reorder tr (append_actions tr1 (append_actions [a ; a'] tr2))
 | lipton_reorder4 : forall a a' a'' tr1 tr2,
      divide tr [a;a';a''] tr1 tr2 ->
      left_mover_action a' /\ right_mover_action a' ->
      lipton_reorder tr (append_actions tr1 (append_actions tr1 (append_actions [a' ; a ; a''] tr2))) ->
      lipton_reorder tr (append_actions tr1 (append_actions tr1 (append_actions [a' ; a'' ; a] tr2))).

Inductive greater_than : nat -> nat -> bool -> Prop :=
 | greater_than_O : forall n,
                              greater_than n 0 true
 | greater_than_S : forall n n' m m',
                             n' = S m' ->
                             n = S m ->
                             greater_than m m' true ->
                             greater_than n n' true.

(* This lemma states the MPC's action's mover properties. *)
Lemma mover_properties : forall a a' tr v p p' P P' tr1 tr2 K K1' K2' K'',
                   adjacent_action a a' ->
                   neighbors_action a a' ->
                   instance_of_process a = P ->
                   instance_of_process a' = P' ->
 		               step K a K1'  ->
 		               step K1' a' K'' ->
 		               step K a' K2'  ->
 		               step K2' a K'' ->
                   tr = (append_actions tr1 (append_actions [a ; a'] tr2)) ->
                   is_subset_action [a ; a'] tr true ->
                   In a tr  ->
                   In a' tr  ->
                   ((a' = (send v p p') -> lipton_reorder (append_actions tr1 (append_actions [a ; a'] tr2)) (append_actions tr1 (append_actions [a' ; a] tr2)))) \/
                   ((a' = (receive v p) -> lipton_reorder (append_actions tr1 (append_actions [a ; a'] tr2)) (append_actions tr1 (append_actions [a ; a'] tr2)))) \/
                   (((a' = (local p) -> lipton_reorder (append_actions tr1 (append_actions [a ; a'] tr2)) (append_actions tr1 (append_actions [a' ; a] tr2)))) /\
                   ((a = (local p) -> lipton_reorder (append_actions tr1 (append_actions [a ; a'] tr2)) (append_actions tr1 (append_actions [a' ; a] tr2))))) \/
                   (((a' = (get p) -> lipton_reorder (append_actions tr1 (append_actions [a ; a'] tr2)) (append_actions tr1 (append_actions [a' ; a] tr2)))) /\
                   ((a = (get p) -> lipton_reorder (append_actions tr1 (append_actions [a ; a'] tr2)) (append_actions tr1 (append_actions [a' ; a] tr2))))) \/
                   (((a' = (set p) -> lipton_reorder (append_actions tr1 (append_actions [a ; a'] tr2)) (append_actions tr1 (append_actions [a' ; a] tr2)))) /\
                   ((a = (set p) -> lipton_reorder (append_actions tr1 (append_actions [a ; a'] tr2)) (append_actions tr1 (append_actions [a' ; a] tr2))))).
  Proof.
  intros.
  left.
  intros.
  apply lipton_reorder2. 
  apply divide_non_empty_actions.
  apply non_empty_tr'2 with tr2 [a;a']. reflexivity.
  apply non_empty_tr1 with tr2. reflexivity.
  apply non_empty_tr''2. reflexivity. 
  apply left with P P' a K K1' K2' K''.
  apply neighbors with tr P P'. assumption. assumption.
  apply adj_act with tr. assumption. assumption. inversion H8.  assumption. assumption. assumption. assumption.
  assumption. assumption. split. assumption. assumption. split. assumption. assumption.
  Qed.

Theorem congruence_no_process' : forall  (P : comp process_conf),
congruence P (app P (empty_comp _)).
Proof.
intros P.
apply symmetric.
apply symmetric.
apply no_pro.
Qed.

(* Transitive and reflexive closure of step relation *)
Inductive reduction : global_conf -> list action -> global_conf -> Prop :=
  | one_step_red : forall T x v''' e v'' M p st' e' M' P st'' e'' M'' st''' e''' M''' 
    v' P' a ,
    step (Sigma (st_decl T x v''') e (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) a
   (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P') -> 
   reduction (Sigma (st_decl T x v''') e (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) (a :: nil)
   (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P')
  | refl_red : forall T x v''' e v'' M p st' e' M' v' P, 
    reduction (Sigma (st_decl T x v''') e (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) nil
   (Sigma (st_decl T x v''') e (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) 
  | trans_red : forall T x v''' e v'' M p st' e' M' P st'' e'' M'' v' P' a1 
    st''' e''' M''' a2
    P'' st1 e1 M1 st2 e2 M2,
    reduction (Sigma (st_decl T x v''') e (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) (a1 :: nil)
   (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P')  ->
    reduction (Sigma st'' e'' M'' (val_exp p) |: 
   (Sigma st''' e''' M''' v') |: P') (a2 :: nil) (Sigma st1 e1 M1 (val_exp p) |: 
   (Sigma st2 e2 M2 v') |: P'') -> 
   reduction  (Sigma (st_decl T x v''') e (v'' :: M) 
   (val_exp p) |: (Sigma st' e' M' v') |: P) (a1 :: a2 :: nil) 
   (Sigma st1 e1 M1 (val_exp p) |: 
   (Sigma st2 e2 M2 v') |: P'').

Lemma reduction_send3 : forall T x v''' e v'' M p st' e' M' P a 
st'' e'' M'' st''' e''' M''' v' P' v,value v ->reduction (Sigma (st_decl T x v''') e (v'' :: M)(val_exp p) |: (Sigma st' e' M' v') |: P) a (Sigma st'' e'' M'' (val_exp p) |:(Sigma st''' e''' M''' v') |: P') ->reduction (Sigma (st_decl T x v''') (send_exp v e) (v'' :: M) (val_exp p) |:(Sigma st' e' M' v') |: P) a(Sigma st'' (send_exp v e'') M'' (val_exp p) |: (Sigma st''' e''' M''' v') |: P').
Proof.
 intros.
 inversion H0. subst.
 apply one_step_red.
 apply ST_send_exp3.
 assumption.
 assumption. subst.
 apply refl_red. subst.
 apply trans_red with st''0 (send_exp v e''0) M''0 P'0 st'''0 e'''0 M'''0.
 apply one_step_red. apply ST_send_exp3.
 assumption. inversion H14. subst.
 assumption. inversion H22. subst.
 apply one_step_red. apply ST_send_exp3.
 assumption. assumption.
Qed.

Lemma reduction_send4 : forall T x v''' M p st' e' M' P a st'' M'' 
st''' e''' M''' v' P' v e2 e1 e1',reduction (Sigma (st_decl T x v''') e1 (v :: M) 
(val_exp p) |: (Sigma st' e' M' v') |: P) a 
(Sigma st'' e1' M'' (val_exp p) |: 
(Sigma st''' e''' M''' v') |: P') ->
reduction  (Sigma (st_decl T x v''') (send_exp e1 e2) 
(v :: M) (val_exp p) |: 
(Sigma st' e' M' v') |: P) a 
(Sigma st'' (send_exp e1' e2) M'' (val_exp p) |: 
(Sigma st''' e''' M''' v') |: P').
Proof.
 intros.
 inversion H. subst.
 apply one_step_red.
 apply ST_send_exp4.
 assumption.
 apply refl_red. subst.
 apply trans_red with st''0 (send_exp e'' e2) M''0 P'0 st'''0 e'''0 M'''0.
 apply one_step_red. apply ST_send_exp4.
 inversion H13. subst.
 assumption. inversion H21. subst.
 apply one_step_red. apply ST_send_exp4.
 assumption.
Qed.

Lemma reduction_send2 : forall T x v''' e v'' M p st' e' M' P a st'' 
e'' M'' st''' e''' M''' v' P' v,value v ->reduction (Sigma (st_decl T x v''') e (v'' :: M)(val_exp p) |: (Sigma st' e' M' v') |: P) a (Sigma st'' e'' M'' (val_exp p) |:(Sigma st''' e''' M''' v') |: P') ->reduction (Sigma (st_decl T x v''') (send_exp e v) (v'' :: M) (val_exp p) |:(Sigma st' e' M' v') |: P) a(Sigma st'' (send_exp e'' v) M'' (val_exp p) |: (Sigma st''' e''' M''' v') |: P').
Proof.
 intros.
 inversion H0. subst.
 apply one_step_red.
 apply ST_send_exp2.
 assumption.
 assumption. subst.
 apply refl_red. subst.
 apply trans_red with st''0 (send_exp e''0 v) M''0 P'0 st'''0 e'''0 M'''0.
 apply one_step_red. apply ST_send_exp2.
 assumption. inversion H14. subst.
 assumption. inversion H22. subst.
 apply one_step_red. apply ST_send_exp2.
 assumption. assumption.
Qed.

Lemma reduction_send1 : forall T x v''' v'' M p st' e' M' v' v P,value v ->
value v' ->reduction (Sigma (st_decl T x v''') (send_exp v v') 
(v'' :: M) (val_exp p) |: 
(Sigma st' e' M' v) |: P) 
((send v' (val_exp p) v) :: nil)(Sigma (st_decl T x v''') v' (v'' :: M) 
(val_exp p) |: 
(Sigma st' e' (append_mail_box M' v') v) |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_send_exp1.
 assumption. assumption.
Qed.

Lemma reduction_state_asgn1 : forall T x v''' v'' M p st' e' M' v' v P,value v ->
value v' ->reduction (Sigma (st_decl T x v''') (set_exp v') 
(v :: M) (val_exp p) |: 
(Sigma st' e' M' v'') |: P) 
[(set (val_exp p))]
(Sigma (st_decl T x v') v' (v :: M) 
(val_exp p) |: (Sigma st' e' M' v'') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_state_asgn1.
Qed.

Lemma reduction_state2 : forall T x v''' e v'' M p st' e' M' P 
a st'' e'' M'' st''' e''' M''' v' P',reduction (Sigma (st_decl T x v''') e (v'' :: M)(val_exp p) |: (Sigma st' e' M' v') |: P) a (Sigma st'' e'' M'' (val_exp p) |:(Sigma st''' e''' M''' v') |: P') ->reduction (Sigma (st_decl T x v''') (set_exp e) (v'' :: M) (val_exp p) |:(Sigma st' e' M' v') |: P) a(Sigma st'' (set_exp e'') M'' (val_exp p) |: (Sigma st''' e''' M''' v') |: P').
Proof.
 intros.
 inversion H. subst.
 apply one_step_red.
 apply ST_state_asgn2.
 assumption.
 apply refl_red. subst.
 apply trans_red with st''0 (set_exp e''0) M''0 P'0 st'''0 e'''0 M'''0.
 apply one_step_red. apply ST_state_asgn2.
 inversion H13. subst.
 assumption. inversion H21. subst.
 apply one_step_red. apply ST_state_asgn2.
 assumption.
Qed.

Lemma reduction_state_read : forall T x v'' M p st' e' M' v' v P,value v ->reduction (Sigma (st_decl T x v) (get_exp) (v' :: M) 
(val_exp p) |: (Sigma st' e' M' v'') |: P) 
[(get (val_exp p))]
(Sigma (st_decl T x v) v (v' :: M) (val_exp p) |: 
(Sigma st' e' M' v'') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_state_read.
Qed.

Lemma reduction_receive1 : forall T x v'' M p st' e' M' v' v P e
x' T' e'',value v ->
has_type empty v T null ->reduction (Sigma (st_decl T' x' v'') 
(receive_exp x T e e') (v :: M) (val_exp p) |: 
(Sigma st' e'' M' v') |: P) 
[(receive v (val_exp p))]
(Sigma (st_decl T' x' v'') (subst x v e) M 
(val_exp p) |: (Sigma st' e'' M' v') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_receive_exp1.
 assumption.
 assumption.
Qed.

Lemma reduction_receive2 : forall T'' T x v'' M p st' e' M' v' v P e
x' T' e'',value v ->
has_type empty v T'' null ->reduction  (Sigma (st_decl T' x' v'') 
(receive_exp x T e e') (v :: M) (val_exp p) |: 
(Sigma st' e'' M' v') |: P) 
[(receive v (val_exp p))]
(Sigma (st_decl T' x' v'') (e') (v :: M) 
(val_exp p) |: (Sigma st' e'' M' v') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_receive_exp2 with T''.
 assumption.
Qed.

Lemma reduction_become : forall T x v'' M p st' e' M' v' v P e,reduction (Sigma (st_decl T x v'') (become_exp e) 
(v :: M) (val_exp p) |: 
(Sigma st' e' M' v') |: P) 
[(become (val_exp p))]
(Sigma (st_decl T x v'') e (v :: M) (val_exp p) |: 
(Sigma st' e' M' v') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_become_exp.
Qed.

Lemma reduction_spawn : forall T x v'' M p v' v P e
v1 v''' x' T' M'' e'' st'',
default v' T ->
fresh v (Sigma (st_decl T' x' v''') 
(spawn_exp x T e) (v1 :: M) (val_exp p) |: 
(Sigma st'' e'' M'' v'') |: P) ->reduction (Sigma (st_decl T' x' v''') (spawn_exp x T e) 
(v1 :: M) (val_exp p) |: 
(Sigma st'' e'' M'' v'') |: P) 
[(spawn (val_exp p) v)]
(Sigma (st_decl T' x' v''') v (v1 :: M) 
(val_exp p) |: (Sigma st'' e'' M'' v'') |:
(Sigma (st_decl T x v') e nil v) |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_spawn_exp.
 assumption.
 assumption.
Qed.

Lemma reduction_self : forall T x v'' M p v' v P
M' e' st',reduction (Sigma (st_decl T x v'') (self_exp) 
(v :: M) (val_exp p) |: 
(Sigma st' e' M' v') |: P) 
[(self)]
(Sigma (st_decl T x v'') (val_exp p) (v :: M) (val_exp p) |: 
(Sigma st' e' M' v') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_self_exp.
Qed.

Lemma reduction_guard1 : forall T x v'' M p st' e' M' v' v P
x' T' e'' e''',value v ->
has_type empty v T null ->
reduction (Sigma (st_decl T' x' v'') 
(guard_exp x T true_exp e' e'') (v :: M) (val_exp p) |: 
(Sigma st' e''' M' v') |: P) 
[(receive v (val_exp p))]
(Sigma (st_decl T' x' v'') (subst x v e') M 
(val_exp p) |: (Sigma st' e''' M' v') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_guard_exp1.
 assumption.
 assumption.
Qed.

Lemma reduction_guard2 : forall T x v'' M p st' e' M' v' v P
x' T' e'' e''',value v ->
has_type empty v T null ->
reduction (Sigma (st_decl T' x' v'') 
(guard_exp x T false_exp e' e'') (v :: M) (val_exp p) |: 
(Sigma st' e''' M' v') |: P) 
[(receive v (val_exp p))]
(Sigma (st_decl T' x' v'') e'' M 
(val_exp p) |: (Sigma st' e''' M' v') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_guard_exp2.
 assumption.
 assumption.
Qed.

Lemma reduction_guard3 : forall T T'' x v'' M p st' e' M' v' v P
x' T' e'' e''' e,value v ->
has_type empty v T'' null ->
reduction (Sigma (st_decl T' x' v'') 
(guard_exp x T e e' e'') (v :: M) (val_exp p) |: 
(Sigma st' e''' M' v') |: P) 
[(receive v (val_exp p))]
(Sigma (st_decl T' x' v'') (e'') (v :: M) 
(val_exp p) |: (Sigma st' e''' M' v') |: P).
Proof.
 intros.
 apply one_step_red.
 apply ST_guard_exp3 with T''.
 assumption.
Qed.
