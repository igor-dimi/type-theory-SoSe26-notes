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
    | x::xs     => 1 + length xs
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







