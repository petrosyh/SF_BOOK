Require Import Arith NPeano.

(** Important: 
    - You are NOT allowed to use the [admit] tactic
      because [admit] simply admits any goal 
      regardless of whether it is provable or not.

      But, you can leave [admit] for problems that you cannot prove.
      Then you will get zero points for those problems.

    - You are NOT allowed to use the following tactics.

      [tauto], [intuition], [firstorder], [omega].

    - Here is the list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [apply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [auto]
      [repeat]
      [try]
      [;]
**)

Definition admit {T: Type} : T.  Admitted.

(**
  Definition of [list] 
 **)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil _  => l2
  | cons _ h t => cons X h (app X t l2)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments app {X} l1 l2.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Check (3 :: ([0; 1] ++ [])).

(**
  You may want to use the following lemmas.
 **)

Check mult_comm.
Check mult_1_r.
Check mult_assoc.
Check plus_comm.
Check plus_0_r.
Check plus_assoc.
Check plus_minus.
Check mult_plus_distr_l.
Check mult_plus_distr_r.
Check mult_minus_distr_l.
Check mult_minus_distr_r.

Check le_not_lt.
Check lt_le_trans.
Check lt_irrefl.

(*=========== 3141592 ===========*)

(** Easy:
    Prove the following theorem.
 **)

Lemma forall_not_ex_not: forall (X: Type) (P: X -> Prop)
    (ALL: forall x, P x),
  ~ exists x, ~ P x.
Proof.
  intros. unfold not. intros. inversion H.
  apply H0. auto. Qed.

(*=========== 3141592 ===========*)

(** Easy:
    Define a function [square_sum] satisfying:

      square_sum n = 1^2 + 2^2 + ... +n^2

 **)

Fixpoint square_sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n * n + square_sum n'
  end.

Example square_sum_example1: square_sum 5 = 55.
Proof. auto. Qed.

Example square_sum_example2: square_sum 10 = 385.
Proof. auto. Qed. 

(*=========== 3141592 ===========*)

(** Medium:
    Define a function [fibonacci] satisfying:

      fibonacci 0 = 0
      fibonacci 1 = 1
      fibonacci (n+2) = fibonacci (n+1) + fibonacci n

 **)

Fixpoint fibonacci (n: nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
           | 0 => 1
           | S n'' => (fibonacci n') + fibonacci n''
           end
  end.

Example fibonacci_example1: fibonacci 5 = 5.
Proof. auto. Qed.

Example fibonacci_example2: fibonacci 10 = 55.
Proof. auto. Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Fixpoint odd_sum (n: nat) : nat :=
  match n with
  | 0 => 0
  | S m => 1 + 2*m + odd_sum m
  end.

Theorem odd_sum__square: forall n,
  odd_sum n = n * n.
Proof.
  induction n; auto.
  simpl. SearchAbout "*".
  rewrite <- plus_n_O. rewrite IHn.
  assert (S n = 1 + n).
  { auto. } rewrite H.
  rewrite mult_plus_distr_l.
  rewrite mult_1_r.
  rewrite plus_assoc. auto. Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Lemma app_tail_cancel: forall X (l1 l2: list X) a
    (EQ: l1 ++ [a] = l2 ++ [a]),
  l1 = l2.
Proof.
  induction l1.
  - intros. induction l2. auto.
    inversion EQ. induction l2; inversion H1.
  - intros. induction l2.
    + inversion EQ. induction l1; inversion H1.
    + simpl in *. inversion EQ. apply IHl1 in H1. subst. auto.
Qed.

(*=========== 3141592 ===========*)

(** Medium:
    Prove the following theorem.
 **)

Lemma odd_or_even: forall n,
  exists k, n = 2*k \/ n = 1 + 2*k.
Proof.
  induction n; auto.
  - exists 0. left. auto.
  - inversion IHn. destruct H.
    + exists x. right. rewrite H. auto.
    + exists (1+x). rewrite H. left.
      simpl. auto.
Qed.

(*=========== 3141592 ===========*)

(** Hard:
    Prove the following theorem.
 **)

Lemma aux0
      n
  :
    n + n = 2 * n.
Proof.
  induction n; auto.
  simpl. rewrite plus_0_r. auto. Qed.
Lemma aux1
      n m
      (CONT: 2 * n = 1 + 2 * m)
  :
    False.
Proof.
  revert CONT. revert m.
  induction n.
  - intros. inversion CONT.
  - intros. induction m.
    + inversion CONT. rewrite <- plus_n_Sm in H0. inversion H0.
    + simpl in CONT. rewrite <- plus_n_Sm in CONT. inversion CONT.
      rewrite <- plus_n_Sm in H0. repeat rewrite plus_0_r in H0.
      repeat rewrite aux0 in H0. apply IHn in H0. inversion H0.
Qed.
  
Lemma aux2
      n
  :
    exists k, (n = 2*k \/ n = 1 + 2*k).
Proof.
  induction n.
  - exists 0. left. auto.
  - inversion IHn.
    inversion H.
    + exists x. right.
      rewrite H0. auto.
    + rewrite H0. exists (1+x). left. simpl.
      rewrite <- plus_n_Sm. auto.
Qed.

Lemma two_three_rel_prime: forall n m
    (EQ: 2 * n = 3 * m),
  exists k, m = 2 * k.
Proof.
  intros.
  destruct (aux2 m). inversion H. exists x. auto.
  
  induction n.
  - intros. inversion EQ. exists 0. admit.
  - intros. rewrite H0 in EQ. admit.
Admitted.


(*=========== 3141592 [30] ===========*)

(** Easy:
    Define a predicate [sorted_min: nat -> list nat -> Prop], where
    [sorted_min n l] holds iff the elements in the list [l] is greater
    than or equal to [n] and sorted in the increasing order.
 **)

Inductive sorted_min: nat -> list nat -> Prop :=
| nil_sort
    n
  :
    sorted_min n []
| more_sort
    n tl hd
    (COND1: sorted_min hd tl)
    (COND2: n <= hd)
  :
    sorted_min n (hd::tl).


Example sorted_min_example1: sorted_min 0 [1; 3; 4; 4; 5].
Proof. repeat constructor. Qed.

Example sorted_min_example2: sorted_min 2 [2; 2; 3; 6].
Proof. repeat constructor. Qed.

Example sorted_min_non_example1: sorted_min 1 [0; 1] -> False.
Proof. intros. inversion H. subst. inversion COND2. Qed.





(** Medium:
    Prove the following theorem. 
 **)

Inductive appears_in (n : nat) : list nat -> Prop :=
| ai_here : forall l, appears_in n (n::l)
| ai_later : forall m l, appears_in n l -> appears_in n (m::l).

Lemma sorted_not_in: forall n m l
    (SORTED: sorted_min m l)
    (LT: n < m),
  ~ appears_in n l.
Proof.
  intros. induction SORTED.
  - unfold not. intros. inversion H.
  - unfold not. intros. inversion H; subst.
    + admit.
    +
  (* FILL IN HERE *) admit.
Qed.









(** Hard:
    Prove the following theorem.
 **)

(* [beq_nat n m] returns [true]  if [n = m] holds; 
                 returns [false] otherwise. *)
Check beq_nat.
Check beq_nat_false.
Check beq_nat_true.
Check beq_nat_refl.

(* [ltb n m] returns [true]  if [n < m] holds; 
             returns [false] otherwise.
   Note that [ltb n m] is displayed as [n <? m]. *)
Check ltb.
Check ltb_lt.

Fixpoint appears_inb (n: nat) (l: list nat) : bool :=
  match l with
  | nil => false
  | m :: l' => 
    if ltb n m
    then false
    else (if beq_nat n m
          then true
          else appears_inb n l')
  end.

Theorem appears_inb_correct: forall n l
    (SORTED: sorted_min 0 l)
    (NOTAPPEAR: appears_inb n l = false),
  ~ appears_in n l.
Proof.
  (* FILL IN HERE *) admit.
Qed.

