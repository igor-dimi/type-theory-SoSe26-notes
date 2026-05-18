(* Tutorial 2 - Pattern Matching and Recusion*)
(* Igor Dimitrov*)

From Stdlib Require Import List.
Import ListNotations.

(* Exercise 1*)
(*a.*) Check [1; 2; 3]. (*: list nat*)
(*b.*) Check true :: true :: nil. (* : list bool *)
(*c.*) Check 1 + 0. (* : nat *)
(*d.*) Check fun (x : nat) (y : nat) => [x; y]. (* : nat -> nat -> list nat*)
(*e.*) (*Check fun (x : nat) (y : bool) => [x; y]. *) (*This doesn't work, lists have to be homogenous*)
(*f.*) Check (fun (n : nat) => 2 * n) 5. (* : nat *)

(* Exercise 2*)
(*a.*)
Fixpoint length {A : Type} (l : list A): nat :=
    match l with
    | []        => 0
    | _::xs     => 1 + length xs
    end.

Compute map length [[]; [1]; [1;2]; [1; 2; 3]]. (* a simple demo that it works*)

(*b*)
Fixpoint concat {A : Type} (xs ys  : list A) : list A :=
    match xs with
    | []     => ys
    | x::xs  => x::(concat xs ys)
    end.
Infix "+++" := concat (at level 60, right associativity) : list_scope.
Compute concat [1; 2] [3; 4]. (* example*)
Compute [true; false] +++ [false]. (* example*)

(*c*)
Fixpoint suffix {A : Type} (l : list A) : list (list A) :=
    match l with
    | []    => [[]]
    | l::ls => (l::ls)::(suffix ls)
    end.

Compute suffix [1; 2; 3].

(* Exercise 3 *)
(* a *)

Inductive EqBool : bool -> bool -> Set :=
| tt : EqBool true true
| ff : EqBool false false.

Notation "b ≡ b'" := (EqBool b b') (at level 120, no associativity).

Check tt.
Check ff.

Theorem negb_inv (b : bool) : negb (negb b) ≡ b.
Proof.
    destruct b.
    - simpl. exact tt.
    - simpl. exact ff.
Qed.


(* b *)
Definition eqb : bool -> bool -> bool :=
    fun b b' =>
    match b, b' with
    | true, true     => true
    | false, false   => true
    | _, _ => false
    end.

Notation "b == b'" := (eqb b b') (at level 120, no associativity).

(* examples *)
Compute eqb true true. 
Compute eqb true false. 
Compute eqb false true. 
Compute eqb false false. 

Compute true == true. 
Compute true == false. 
Compute false == true. 
Compute false == false. 

Theorem ex3b (b : bool) : (negb (negb b) == b) = true.
Proof.
    destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.






