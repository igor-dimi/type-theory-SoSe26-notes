Check true.
Check false.

Check bool. 
About bool.
Check Set. 
Check Type.
Check Prop.

Check negb.
About negb.

Check negb false.
Compute negb false.

Check orb true false.
Compute orb true false.
Check bool -> (bool -> bool).

Compute negb false.

Check orb true false.

Compute 1 + 1.

Check nat. 


Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.


Check negb.


Check fun b : bool => fun n : nat => 1.


Check fun b : bool => 1.
Compute (fun b : bool => 1) true.


Compute ((fun n : nat => fun m : nat => n * m + 1) 3) 4.


Definition y := 10.

Definition f : nat -> nat :=
    fun x : nat => x * y + 1.

Check y.
Compute y.

Check f.

Compute f 3.



Check (fun x  => x * 2 + 1).

Check Prop.
Check Set. 

Definition g (b : bool) := 
    negb b.

Compute g true.

Theorem negation_is_involutive_true : negb (negb true) = true.
Proof.
    simpl.
    reflexivity.
Qed.

Theorem negative_is_involutive_incorrect : negb (negb false) = true.
Proof.
    simpl.
    Fail reflexivity.
Admitted.

Definition negation_is_involutive_true' : negb (negb false) = false :=
    eq_refl.

Check negation_is_involutive_true'.

Print negation_is_involutive_true'.
Print negation_is_involutive_true.

Theorem neg_inv (b : bool) : negb (negb b) = b.
Proof.
    destruct b.
    - exact negation_is_involutive_true.
    - reflexivity.
Qed.




Check neg_inv.
Check neg_inv true.
Check neg_inv false.

Check implb.
Compute implb true false.


Theorem implb_eq_orb_negb (b b' : bool) : implb b b' = orb (negb b) b'.
Proof.
    destruct b.
    - destruct b'.
        + reflexivity.
        + reflexivity.
    - destruct b'.
        all: reflexivity.
Qed.

Theorem implb_eq_negb_andb_negb (b b' : bool) : implb b b' = negb (andb b (negb b')).
    Proof.
        destruct b, b'.
        all: reflexivity.
    Qed.

Definition eval_at :=
    fun (f : bool -> bool) (b : bool) => f b.

Compute eval_at negb false.


Check bool.

Check negb (negb true) = true.