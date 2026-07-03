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

(* Proof by simplification *)

Example plus_1_1 : 1 + 1 = 2.
Proof. 
    simpl. reflexivity.
Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
    intros n. simpl. reflexivity.
Qed.


Theorem plus_1_n : forall n : nat, 1 + n = S n.
Proof. 
    intros n.  reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
    intros n. simpl. reflexivity.
Qed.

Theorem plus_id_exercise : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
    intros n m. 
    intros H.
    rewrite <- H.
    reflexivity.
Qed.

Theorem plus_id_exercise' : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o.
    intros H.
    intros H'.
    rewrite -> H.
    rewrite -> H'.
    reflexivity.
Qed.

Check mult_n_O.
(* ==> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ==> forall n m : nat, n * m + n = n * S m *)


Theorem mult_n_0_m_0 : forall p q : nat,
    (p * 0) + (q * 0) = 0.
Proof.
    intros p q.
    rewrite <- mult_n_O. 
    (* since 0 = n * 0 is the theorem rewriting 'turns' n * 0 to 0 *)
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
Qed.

(* Exercise: mult n 1 *)
Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
Proof.
    intros p.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_O.
    simpl. reflexivity.
Qed.

(* Proof by Case Analysis *)

Theorem plus_1_neq_0_firstry : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
    intros n.
    destruct n as [ | n'] eqn : E.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.


(* Fixpoint myadd (n m : nat) : nat :=
    match n with
    | 0 => m
    | S n => S (myadd n m)
    end.

Check myadd.

Notation "n (+) m" := (myadd n m) (at level 70) : nat_scope.

Compute 13 (+) 12. *)

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
    intros b.
    destruct b eqn: E.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
    intros b c.
    destruct b eqn:Eb.
    - destruct c eqn:Ec.
      + simpl. reflexivity.
      + simpl. reflexivity.
    - destruct c eqn:Ec.
      + simpl. reflexivity.
      + simpl. reflexivity.
Qed.

Check andb_commutative.

Compute andb_commutative.


Theorem andb3_exchange:
    forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
    intros.
    destruct b, c, d.
    all: simpl.
    all: reflexivity.
Qed.

(* Exercise: 2 stars, standard (andb_true_elim2) *)

Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
    intros b c.
    intros H.
    destruct b eqn:Eb.
    - simpl in H. rewrite -> H. reflexivity.
    - simpl in H. destruct c eqn:Ec.
      + reflexivity.
      + rewrite -> H. reflexivity.
Qed.

Theorem andb_commutative'' :
    forall b c, andb b c = andb c b.
Proof.
    intros [] [].
    all: simpl.
    all: reflexivity.
Qed.

(* Exercise: 1 star, standard (zero nbez plus 1) *)
Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
Proof.
    intros [ | n'].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(* More on notation *)

(* Fixpoints and Structural Recursion *)

(* More exercises *)

Theorem identity_fn_applied_twice:
    forall (f: bool -> bool),
    (forall (b : bool), f b = b) ->
    forall (b : bool), f (f b) = b.
Proof.
    intros f.
    intros H.
    intros b.
    rewrite -> H. 
    rewrite -> H. 
    reflexivity.
Qed.

Theorem identity_negation_fn_applied_twice:
    forall (f : bool -> bool),
    (forall (b : bool), f b = negb b) ->
    forall (b : bool), f (f b) = b.
Proof.
    intros.
    rewrite -> H. 
    rewrite -> H.
    rewrite negb_involutive. reflexivity.
Qed.

Theorem andb_eq_orb :
    forall (b c : bool),
    (andb b c = orb b c) ->
    b = c.
Proof.
    intros.
    destruct b eqn:Eqb.
    - simpl in H. rewrite -> H. reflexivity.
    - simpl in H. rewrite <- H. reflexivity.
Qed.

(* Course Late Policies *)
Module LateDays.

Inductive letter := | A | B | C | D | F.
Inductive modifier := | Plus | Natural | Minus.
Inductive grade :=
    Grade (l: letter) (m: modifier).

Inductive comparison :=
| Eq
| Lt
| Gt.


Definition letter_comparison (l1 l2 : letter) : comparison :=
    match l1, l2 with
    | A, A => Eq
    | A, _ => Gt
    | B, A => Lt
    | B, B => Eq
    | B, _ => Gt
    | C, (A | B) => Lt
    | C, C => Eq
    | C, _ => Gt
    | D, F => Gt
    | D, D => Eq
    | D, _ => Lt
    | F, F => Eq
    | F, _ => Lt
    end.

Compute letter_comparison B A.
Compute letter_comparison D D.
Compute letter_comparison B F.
Compute letter_comparison D F.

Theorem letter_comparison_eq:
    forall l, letter_comparison l l = Eq.
Proof.
    intros.
    destruct l eqn:E.
    all: simpl.
    all: reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
    match m1, m2 with
    | Plus, Plus => Eq
    | Plus, _ => Gt
    | Natural, Plus => Lt
    | Natural, Natural => Eq
    | Natural, _ => Gt
    | Minus, Minus => Eq
    | Minus, _ => Lt
    end.

Definition grade_comparison (g1 g2 : grade) : comparison :=
    match g1, g2 with
    | Grade l1 m1, Grade l2 m2 =>
        match letter_comparison l1 l2 with
        | Eq => modifier_comparison m1 m2
        | other => other
        end
    end.





     

