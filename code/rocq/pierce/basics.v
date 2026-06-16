Inductive day : Type := 
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
    | monday    => tuesday
    | tuesday   => wednesday
    | wednesday => thursday
    | thursday  => friday
    | friday    => monday
    | saturday  => monday
    | sunday    => monday
    end.

Compute (next_working_day (next_working_day friday)).

Example test_next_working_day :
    (next_working_day (next_working_day saturday)) = tuesday.
Proof.
    simpl.
    reflexivity.
Qed.

Inductive bool : Type :=
    | true
    | false.

Definition negb (b : bool) : bool :=
match b with
| true  => false
| false => true
end.

Definition andb (b1 b2 : bool) : bool :=
match b1 with
| true  => b2
| false => false
end.

Definition orb (b1 b2 : bool) : bool :=
match b1 with
| true => true
| false => b2
end.

Compute orb true false.
Compute orb false false.
Compute orb false true.
Compute orb true true.

Example test_orb1: (orb true false) = true.
Proof. 
    simpl. 
    reflexivity.
Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Compute false || false || false || true. 

Example test_orb2 : false || false || false || true = true.
Proof.
    simpl.
    reflexivity.
Qed.

Inductive bw : Type :=
| bw_black
| bw_white.

Definition invert (x : bw) : bw :=
if x then bw_white
else bw_black.

Compute invert bw_white.
Compute invert bw_black.

Check invert.

Definition nandb (b1 b2 : bool) : bool :=
match b1, b2 with
| false, _ => true
| true, false => true
| true, true => false
end.

Example nandb_and_negb_andb_eq : 
    forall b b' : bool, negb (andb b b') = nandb b b'.
Proof.
    intros b.
    intros b'.
    simpl.
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

Example test_andb31: (andb3 true true true) = true.
simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
simpl. reflexivity. Qed.


Check true.

Check true : bool.
Check (negb true) : bool.

Check negb.

Inductive rgb : Type := | red | green | blue.

Inductive color :=
| white
| black
| primary (p : rgb).

Definition monochrome (c : color) : bool :=
match c with
| white 
| black         => true
| primary _     => false
end.   

Definition isRed (c : color) : bool :=
match c with
| primary red   => true
| _ => false
end.

Compute isRed (primary red).
Compute isRed (primary green).
Compute isRed (primary blue).
Compute isRed white.
Compute isRed black.


Module Playground.
    Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check Playground.foo.
Check foo.


Inductive bit := | B1 | B0.

Check B1.
Check B0.


Inductive nybble :=
| bits (b0 b1 b2 b3 : bit).

Check (bits B0 B0 B0 B0).

Definition all_zero (nb : nybble) : bool :=
match nb with
| (bits B0 B0 B0 B0) => true
| _ => false
end.

Compute all_zero (bits B0 B0 B0 B0).


Module NatPlayground.

Inductive nat : Type :=
| ε
| S (n : nat).

Check ε.
Check S (S (S ε)).

Definition pred (n : nat) : nat :=
match n with
| ε => ε
| S n => n
end.

Compute pred (pred (pred (S (S (S ε))))).

End NatPlayground.


Check (S (S (S 0))).

Definition minusTwo (n : nat) : nat :=
match n with
| 0 => 0
| S 0 => 0
| S (S n) => n
end.

Compute minusTwo (minusTwo 15).

Fixpoint even (n : nat) : bool :=
match n with
| 0 => true
| S 0 => false
| S (S n) => even n
end.

Definition odd (n : nat) : bool :=
    negb (even n).

Example test_odd1: even 4 = true.
Proof.
    simpl. reflexivity.
Qed.

Module NatPlayground2.

Fixpoint plus (n m : nat) : nat :=
    match n with
    | 0 => m
    | S n => S (plus n m)
    end.

Check plus.

Compute plus 3 2.

Fixpoint mult (n m : nat) : nat :=
    match n with
    | 0 => 0
    | S n => plus m (mult n m)
    end.

Compute mult 10 3.

Example test_mult1: (mult 3 3) = 9.
Proof. 
    simpl. reflexivity.
Qed.

Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | 0 , _ => 0
    | _ , 0 => n
    | S n, S m => minus n m
    end.

Compute minus 3 3.

End NatPlayground2.


Fixpoint exp (base power : nat) : nat :=
    match power with
    | 0 => 1
    | S power => mult base (exp base power)
    end.

Compute exp 3 4. 

