From LF.ch01 Require Export Basics04.
(* separate compilation *)

Compute 2.


Check negation_fn_applied_twice.


(* Proof by Induction *)

Theorem add_0_r_firsttry: forall n : nat,
    n + 0 = n.
Proof.
    intros. destruct n as [| n'] eqn:E.
    - reflexivity.
    - simpl. 
       destruct n'.
       + reflexivity.
Abort.

Theorem add_0_r : forall n : nat, n + 0 = n.
Proof.
    intros n. induction n as [ | n' IHn'].
    - reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
Qed.

