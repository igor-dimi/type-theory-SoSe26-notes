(* some comment*)


Check 1.

Check fun x : nat => x * 2 + 1.

Check fun x : nat => (fun y : nat => x * y + 1).
Check (fun x : nat => (fun y : nat => x * y + 1)3)4.

(* function definitions *)

Definition f :=
    fun x : nat => x * 2 + 1.

Check f.

Definition g :=
    fun x : nat => (fun y : nat => x * y + 1).

Check g.

Definition h := g 3.

Check h.

Compute h 10.

Definition negb1 :=
    fun b =>
    match b with
    | true => false
    | false => true
    end.

Check negb1.

Check negb1 true.

Compute negb true.
Compute negb false.

Definition negb2 (b : bool) :=
    match b with
    | true => false
    | false => true
    end.

Check fun x : nat => 2 * x : nat.


Definition h2 (x y : nat) : nat :=
    x + y * 2.

Check h2.
Compute h2 3 4.

Check h2 3.

Definition h2_2 : nat -> nat -> nat :=
    fun x : nat => (fun y : nat => x + y * 2).

Check h2_2.

Check h2_2 3. 

Check fun x y => x * y + 1.

Check true = false.

Check bool.

Check Type.

Check Set.

Check Prop.


Module my2Notes.

    Definition negb :=
        fun b =>
            match b with
            | true => false
            | false => true
            end.

Compute negb true.
Compute negb false.


Definition andb : bool -> bool -> bool :=
    fun b1 b2 =>
    match b1, b2 with
    | false, _ => false
    | true, b2 => b2
    end.

Check andb.
Check andb false.
Compute andb false false.
Compute andb false true.
Compute andb true false.
Compute andb true true.


Definition orb :=
    fun b1 b2 => 
    match b1, b2 with
    | true, _ => true
    | false, b2 => b2
    end.


Check orb.
Check orb false.
Compute orb false false.
Compute orb false true.
Compute orb true false.
Compute orb true true.


Check negb (negb true) = true.


Theorem negb_negb_true_eq_true : negb (negb true) = true.
Proof.
    simpl.
    reflexivity.

Theorem negb_negb_false_eq_false: negb (negb false) = false.
Proof.
    reflexivity.
Qed.

Theorem fail_to_unify : negb (negb false) = true.
Proof.
    Fail reflexivity.
Admitted.


Theorem negb_inv (b : bool) : negb (negb b) = b.
Proof.
    destruct b.
    - simpl. 
      reflexivity.
    - exact negb_negb_false_eq_false.
Qed.

Check 1.

Check negb_inv.


Check negb_inv true.
Check negb_inv false.




Definition implb : bool -> bool -> bool :=
    fun b b' => if b then b' else true.

Compute implb false false.
Compute implb false true.
Compute implb true false.
Compute implb true true.


Theorem implb_eq_orb_negb (b b' : bool) : implb b b' = orb (negb b) b'.
Proof.
    destruct b.
    - destruct b'.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct b'.
      + simpl. reflexivity.
      + simpl. reflexivity.
Qed.

Check implb_eq_orb_negb.

Theorem implb_eq_orb_negb2 (b b' : bool) : implb b b' = orb (negb b) b'.
Proof.
    destruct b, b'.
    all: reflexivity.
Qed.

Check implb_eq_orb_negb2.