(* Introduction *)

Inductive day := 
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.


Check monday.
Check day.


Definition next_working_day (d : day) : day :=
match d with
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday 
| saturday
| sunday => monday
end.

Check next_working_day.

Compute (next_working_day friday).
Compute (next_working_day (next_working_day friday)).

Check fun x => x + 3.


Example test_next_working_day : 
    (next_working_day (next_working_day saturday)) = tuesday.
Proof.
    reflexivity.
Qed.

Check test_next_working_day.

(* Booleans *)

Inductive bool := | true | false.

Check bool.

Definition negb (b : bool) : bool :=
match b with
| true => false
| _ => true
end.

Compute negb false.
Compute negb true.

Definition andb (b b' : bool) : bool :=
match b with
| false => false
| true => b'
end.

Compute andb false false.
Compute andb false true.
Compute andb true false.
Compute andb true true.


Definition orb (b b' : bool) : bool :=
match b with
| false => b'
| true => true
end.

Compute orb false false.
Compute orb false true.
Compute orb true false.
Compute orb true true.

Example test_orb1 : forall b : bool, orb true b = true.
Proof.
    intros. destruct b.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Example test_orb2 (b : bool) : orb true b = true.
Proof.
    destruct b.
    all: reflexivity.
Qed.

Check test_orb2.
Check test_orb1.

Notation "x && y" := (andb x y).
Notation "b || b'" := (orb b b').

Compute false && false.
Compute false && true.
Compute true && false.
Compute true && true.


Compute false || false.
Compute false || true.
Compute true || false.
Compute true || true.


Definition nandb (b b' : bool) : bool :=
match b, b' with
| true, true => false
| _, _ => true
end.


Compute nandb false false.
Compute nandb false true.
Compute nandb true false.
Compute nandb true true.

(* Types *)

Inductive rgb :=
| red | green | blue.

Inductive color :=
| black
| white
| primary (p : rgb).

Check primary.
Check primary red.
Check black.


Module TuplePlayground.

Inductive bit := | B0 | B1.

Check B0.
Check bit.

Inductive nybble :=
| bits (b0 b1 b2 b3 : bit).

Check bits.

Check bits B0 B0 B0 B0.

End TuplePlayground.


Module NatPlayground.

Inductive nat :=
| ε
| S (n : nat).


Check S.
Check ε.
Check S ε.
Check S (S ε).
Check S (S (S ε)).

Definition pred (n : nat) : nat :=
match n with
| ε => ε
| S n => n
end.

Check pred.
Compute pred ε.
Compute pred (S (S (S ε))).


End NatPlayground.

Check S O.
Check S (S (S O)).

Definition minustwo (n : nat) : nat :=
    match n with
    | 0 => 0
    | S O => O
    | S (S n) => n
    end.

Check minustwo.

Compute minustwo 4.

(* Defining recursive functions on numbers *)

Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S n) => even n
    end.

Definition odd (n : nat) : bool := negb (even n).

Compute even 4.
Compute even 3.
Compute odd 3.
Compute odd 2.

Module NatPlayground2.

Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n => S (plus n m)
    end.

Compute plus 4 2.
Compute plus 0 2.
Check plus.

Fixpoint mult (n m : nat) : nat :=
    match n with
    | 0 => 0
    | S n => plus m (mult n m)
    end.

Compute mult 3 3.
Compute mult 10 12.

Fixpoint minus (n m : nat) : nat :=
    match n, m with
    | 0, _ => 0
    | _, 0 => n
    | S n, S m => minus n m
    end.

Compute minus 3 2.
Compute minus 3 4.


End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
    match power with
    | 0 => 1
    | S power => mult base (exp base power)
    end.

Compute exp 3 4.
Compute exp 3 0.
Compute exp 4 4.

Fixpoint factorial (n : nat) : nat :=
    match n with
    | 0 => 1
    | S n => mult (S n) (factorial n)
    end.

Compute factorial 5.
Compute factorial 4.
Compute factorial 6.


Fixpoint eqnat (n m : nat) : bool :=
    match n, m with
    | 0, 0 => true
    | S n, 0 => false
    | 0, S m => false
    | S n, S m => eqnat n m
    end.

Compute eqnat 1 0.
Compute eqnat 1 1.
Compute eqnat 1 3.
Compute eqnat 10 10.


Fixpoint leqnat (n m : nat) : bool := 
    match n, m with
    | 0, 0 => true
    | 0, S m => true
    | S n, 0 => false
    | S n, S m => leqnat n m
    end.

Compute leqnat 1 0.
Compute leqnat 1 1.
Compute leqnat 1 3.
Compute leqnat 10 10.
Compute leqnat 10 3.


Notation "x =? y" := (eqnat x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leqnat x y) (at level 70) : nat_scope.

Definition ltnat (n m : nat) : bool :=
    negb (leqnat m n).


Compute ltnat 1 0.
Compute ltnat 1 1.
Compute ltnat 1 3.
Compute ltnat 10 10.
Compute ltnat 10 3.


(* Proof by Simplification *)

Check plus.

Example plus_1_1 : 1 + 1 = 2.
Proof.
    simpl. reflexivity.
Qed.


Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
    intros n.
    simpl.
    reflexivity.
Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
    intros n.
    simpl. reflexivity.
Qed.


Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
    intros n.
    simpl. reflexivity.
Qed.


(* Proofs by rewriting *)

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
    intros.
    rewrite -> H.
    reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat, 
    n = m -> m = o -> n + m = m + o.
Proof.
    intros.
    rewrite -> H.
    rewrite -> H0.
    reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_O_m_O : forall p q : nat,
    (p * 0) + (q * 0) = 0.
Proof.
    intros.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
Qed.


Theorem mult_n_1 : forall n : nat,
    n * 1 = n.
Proof.
    intros.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
