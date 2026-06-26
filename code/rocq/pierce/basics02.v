Inductive day :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday.

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
Compute (next_working_day (next_working_day saturday)).

Example test_next_working_day :
    (next_working_day (next_working_day saturday)) = tuesday.
Proof. 
    simpl. reflexivity.
Qed.

(* Booleans *)

Inductive bool : Type :=
    | true
    | false.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => false
    end.

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
    | true => true
    | false => b'
    end.


Compute orb false false.
Compute orb false true.
Compute orb true false.
Compute orb true true.

Definition andb3 (b1 b2 b3 : bool) : bool :=
    match b1 with
    | false => false
    | true => match b2 with
              | false => false
              | true => b3
              end
    end.

Example teste_andb3 : (andb3 true true false) = false.
Proof.
    simpl. reflexivity.
Qed.
                

