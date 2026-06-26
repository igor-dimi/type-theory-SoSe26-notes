Inductive day :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

Check day.
Check monday.

Definition next_working_day (d : day) : day :=
match d with
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday => monday
| saturday => monday
| sunday => monday
end.

Check next_working_day.

Compute (next_working_day (next_working_day friday)).

Example test_next_working_day:
    (next_working_day (next_working_day saturday)) = tuesday.
Proof.
    simpl. reflexivity. 
Qed.

(* Booleans *)

Inductive bool := | true | false.

Definition negb (b : bool) : bool :=
match b with
| false => true
| true => false
end.

Check negb false.
Compute negb false.
Compute negb true.

Definition orb (b b' : bool) : bool :=
match b with
| false => b'
| _ => true
end.

Compute orb false false.
Compute orb false true.
Compute orb true false.
Compute orb true true.

Definition andb (b b' : bool) : bool :=
match b with
| true => b'
| _ => false
end.

Compute andb false false.
Compute andb false true.
Compute andb true false.
Compute andb true true.


Example test_orb1: (orb true false) = true.
Proof.
    simpl. reflexivity.
Qed.

Notation "x && y" := (andb x y).
Compute false && false.
Compute false && true.
Compute true && false.
Compute true && true.

Notation "x || y" := (orb x y).
Compute false || false.
Compute false || true.
Compute true || false.
Compute true || true.

Example test_orb' : false || false || false || true = true.
Proof.
    simpl. reflexivity.
Qed.

Definition nandb (b b' : bool) : bool :=
match b, b' with
| true, true => false
| _, _ => true
end.

Compute nandb false false.
Compute nandb false true.
Compute nandb true false.
Compute nandb true true.


Theorem nandb_eq_negb_andb: forall b b' : bool, nandb b b' = negb (andb b b').
Proof.
    intros b b'.
    destruct b. 
    - destruct b'.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct b'.
      + simpl. reflexivity.
      + simpl. reflexivity.
Qed.


Definition andb3 (b1 b2 b3 : bool) : bool :=
match b1, b2, b3 with
| true, true, true => true
| _, _, _ => false
end.


Compute andb3 false false false.
Compute andb3 true true true.


Theorem andb3_eq_andb_andb: 
    forall b1 b2 b3: bool, 
    andb3 b1 b2 b3 = andb (andb b1 b2) b3.
Proof.
    intros b1 b2 b3.
    destruct b1, b2, b3.
    all: simpl.
    all: reflexivity. 
Qed.

Check true.
Check (negb true).
Check negb.


(* new types from old - composing types *)

Inductive rgb := | red | green | blue.

Check red.
Check green.
Check blue.

Inductive color :=
| black
| white 
| primary (p : rgb).

Check black.
Check white.
Check primary green.

Definition foo : bool := true.
Check foo.

Module Playground.
    Definition foo: rgb := blue.
End Playground.

Check Playground.foo.

Module TuplePlayground.

Inductive bit :=
| B (b : bool).

Inductive nybble :=
| bits (b0 b1 b2 b3 : bit).

Check bits (B false) (B true) (B false) (B true).

End TuplePlayground.

Module NatPlayground.

Inductive nat :=
| O
| S (n : nat).

Check O.
Check S (S (S O)).

Check S.

Definition pred (n : nat) : nat :=
match n with
| O => O
| S n => n
end.

Compute pred (S O).
Compute pred (pred (S (S O))).
Compute pred (pred (pred (S (S (S O))))).

End NatPlayground.

Check (S (S (S O))).

Check S.

Definition minustwo (n : nat) : nat :=
match n with
| O => O
| S O => O
| S (S n) => n
end.

Compute minustwo 0.
Compute minustwo 1.
Compute minustwo 2.
Compute minustwo 3.

Check S : nat -> nat.
Check S.

Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n) => even n
    end.

Compute even 13.
Compute even 22.

Definition odd (n : nat) : bool :=
    match n with
    | O => false
    | S n => even n
    end.


Compute odd 13.
Compute odd 14.
Compute odd 0.
Compute odd 1.

Example test_odd1: odd 1 = true.
Proof.
    simpl. reflexivity.
Qed.

Example test_odd2: odd 4 = false.
Proof.
    simpl. reflexivity.
Qed.

Module NatPlayground2.

Fixpoint plus (n m : nat) : nat :=
match n with
| O => m
| S n => S (plus n m)
end.

Compute (plus 3 2).
Compute (plus 0 2).


Fixpoint minus (n m : nat) : nat :=
match n, m with
| O, _ => O
| S _, O => n
| S n, S m => minus n m
end.


End NatPlayground2.

Compute 3 * 2.

Fixpoint exp (base power : nat) : nat := 
    match power with
    | O => 1
    | S power => base * (exp base power)
    end.

Compute exp 3 2.
Compute exp 3 4.
Compute exp 3 5.
Compute exp 2 5.
Compute exp 3 9.


Fixpoint factorial (n : nat) : nat :=
    match n with
    | 0 => 1
    | S n => (S n) * (factorial n)
    end.

Compute factorial 6.

Example test_factorial1: (factorial 3) = 6.
Proof.
    simpl. reflexivity.
Qed.

Fixpoint eqnat (n m : nat) : bool :=
    match n, m with
    | 0, 0 => true
    | S n, 0 => false
    | 0, S m => false
    | S n, S m => eqnat n m
    end.


Compute eqnat 0 0.
Compute eqnat 0 1.
Compute eqnat 1 0.
Compute eqnat 15 0.
Compute eqnat 3 2.
Compute eqnat 10 10.
Compute eqnat 100 100.

Fixpoint leqnat (n m : nat) : bool :=
    match n, m with
    | 0, 0 => true
    | 0, S m => true
    | S n, 0 => false
    | S n, S m => leqnat n m
    end.

Compute leqnat 2 2.
Compute leqnat 2 4.
Compute leqnat 0 0.
Compute leqnat 0 1.
Compute leqnat 3 2.

Notation "x =? y" := (eqnat x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leqnat x y) (at level 70) : nat_scope.

Compute 4 <=? 2.
Compute 2 <=? 4.

Definition ltnat (n m : nat) : bool :=
    negb (leqnat m n).

Compute ltnat 2 3.
Compute ltnat 3 3.
Compute ltnat 3 4.










