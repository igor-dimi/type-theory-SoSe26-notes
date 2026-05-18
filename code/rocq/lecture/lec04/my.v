(* Inductive Wff :=
  P     : nat -> Wff
| Neg   : Wff -> Wff
| Impl  : Wff -> Wff -> Wff
| Conj  : Wff -> Wff -> Wff   
| Disj  : Wff -> Wff -> Wff.

Check P.
Check P 0.
Check Neg.
Check Impl.

Check Neg (P 0).
 
Check Impl (P 1) (P 2).

Definition F_1 := Neg (P 0).
Definition F_2 := Conj (P 1) (P 2).

Check F_1.
Check F_2.

Check Impl F_1 F_2.
Compute Impl F_1 F_2.

Check Wff.

Section Scratch.
    Variable phi : Wff.
    Check Impl phi.
End Scratch.

Definition b  := true : bool.
Check b.

Definition b' : bool := true.
Check b'.
Compute b.
Compute b'.

Notation "a /\ b" := (Conj a b) (at level 80, right associativity).
Notation "a \/ b" := (Disj a b) (at level 85, right associativity).
Notation "a ==> b" := (Impl a b) (at level 99, right associativity).
Notation "~ a" := (Neg a) (at level 75, format "~ a").


Check Conj.

Check ~P 0.
Compute ~P 1.

Check ~P 1 ==> P 3 \/ P 4.

Compute max 1 2.


Fixpoint ht (F : Wff) :=
    match F with
    | P i       => 0
    | ~F        => 1 + ht F
    | F /\ F'   => 1 + max (ht F) (ht F')
    | F \/ F'   => 1 + max (ht F) (ht F')
    | F ==> F'  => 1 + max (ht F) (ht F')
    end.

Compute ht (~P 0).
Check ht (~P 0).
Compute ht (P 1).

Compute ht ((P 1 /\ P 2) \/ ~~P 3).


Definition ht_0: Wff -> nat :=
    fix ht(F : Wff) : nat :=
    match F with
    | P _       => 0
    | ~F        => 1 + ht F
    | F ==> F' | F \/ F' | F /\ F' => 1 + max (ht F) (ht F')
    end.

Goal ht = ht_0.
Proof.
    reflexivity.
Qed.

Definition ht_1 (F : Wff) : nat.
    Proof.
        induction F.
        - exact 0.
        - exact (1 + IHF).
        - exact (1 + (max IHF1 IHF2)).
        - exact (1 + (max IHF1 IHF2)).
        - exact (1 + (max IHF1 IHF2)).
    Defined.

Goal ht = ht_1.
Proof.
    reflexivity.
Qed.


Compute ht_1 (P 1 /\ P 2).

Definition ht_2 (F : Wff) : nat.
    Proof.
        induction F.
        exact 0.
        exact (1 + IHF).
        all: exact (1 + (max IHF1 IHF2)).
    Defined.

Compute ht_2(P 1 /\ P 2 \/ ~~P 3).


Compute ht_1 (P 1 /\ P 2).

Compute ht (~ P 1 /\ P 2).

Goal ht = ht_2.
Proof.
    reflexivity.
Qed.

Check list nat.
Check list bool.
Check Wff.

Check nil.
Check cons.

Check @nil.
Check @cons.

Check @nil bool.

Inductive Nat :=
    | ε : Nat
    | S: Nat -> Nat.

Check Nat.
Check S (S (S ε)).


Check (nil : list nat).
Check cons true (cons false nil).

Open Scope list_scope.
Check 1 :: 2 :: 3 :: nil.

From Stdlib Require Import List.
Import ListNotations.

Check 1 :: 2 :: 3 :: nil.
Check [1; 2; 3].
Check 1 :: [2; 3].
Compute 1 :: 2 :: 3 :: nil.
Check [41].

Fixpoint strict_sf (F : Wff) : list Wff :=
    match F with
    | P i        => nil
    | ~ F        => F :: strict_sf F
    | F \/ F'
    | F ==> F'
    | F /\ F'    => F :: strict_sf F ++ F' :: strict_sf F' 
    end.


Compute strict_sf (P 1 ==> P 1 \/ P 3).

Definition sf (F : Wff) : list Wff :=
    F :: (strict_sf F).

Compute sf ((P 1 /\ P 2) \/ ~~P 3).


(* Substitutions *)


Fixpoint subst_Wff (F : Wff) (I : nat -> bool) (G : nat -> Wff) : Wff :=
    match F with
    | P j       => if I j then G j else P j
    | ~F        => ~(subst_Wff F I G) 
    | F ==> F'  => (subst_Wff F I G) ==> (subst_Wff F' I G)
    | F \/ F'   => (subst_Wff F I G) \/ (subst_Wff F' I G)
    | F /\ F'   => (subst_Wff F I G) /\ (subst_Wff F' I G)
    end.

Definition I (n : nat) : bool :=
    match n with
    | 0    
    | 2026  
    | 41    
    | 42    => true
    | _     => false
    end.

Compute map I [0; 2026; 41; 42; 103].

Definition G1 : nat -> Wff :=
    fun n => P (n + 2) /\ P (n + 1).

Check G1 3.
Compute G1 3.


Definition G2 : nat -> Wff :=
    fun n => match n with
    | 2025 => P 44
    | 2026 => P 1 ==> P 2
    | _    => P n
    end.

Compute subst_Wff (P 0 \/ P 2026 ==> P 42 /\ P 2025) I G2.

From Corelib Require Import Init.Nat.

Definition is_even(n : nat) : bool :=
    eqb (n mod 2) 0.

Compute map is_even [1; 2; 3; 4].

Definition G3 :=
    fun n => 
        if is_even n then P (n / 2) else P n.

Check G3.

Compute subst_Wff (P 0 \/ P 2026 ==> P 41 /\ P 2025) I G3.

 *)

From Stdlib Require Import Utf8.


Definition ℕ := nat.
Check ℕ.

Inductive Wff := 
 P      : ℕ → Wff
|Neg    : Wff → Wff
|Impl   : Wff → Wff → Wff
|Conj   : Wff → Wff → Wff
|Disj  : Wff → Wff → Wff.

Check P 2.
Check Neg (P 2).
Check P.
Check Disj.
Check Impl.

Check Disj (P 1) (P 2).

Check Disj (P 2).

Section Scratch.

    Variable dummy : Wff.
    Check Impl dummy.

End Scratch.

Check Wff.

Notation "a ∧ b" := (Conj a b) (at level 80, right associativity).
Notation "a ∨ b" := (Disj a b) (at level 85, right associativity).
Notation "a ⇒ b" := (Impl a b) (at level 99, right associativity).
Notation "¬ a" := (Neg a) (at level 75, format "¬ a").

Check P 1 ∧ P 2 ∧ P 3.

Check P 1 ⇒ P 2 ⇒ P 3.

Check P 1 ∧ P 2 ∨ P 3.

Fixpoint ht (F : Wff) :=
    match F with
      P i     => 0 
    | ¬F      => 1 + ht F
    | F ∧ F'  
    | F ∨ F'
    | F ⇒ F'  => 1 + max (ht F) (ht F')
    end.


Compute ht (P 1).
Compute ht (P 1 ∧ P 2 ∨ (P 3 ⇒ P 4 ∧ P 5)).

Check ht.

Definition ht0 :=
    fix ht (F : Wff) : nat := 
    match F with
    | P _       => 0
    | ¬F        => 1 + ht F
    | F ⇒ F'
    | F ∧ F'
    | F ∨ F'    => 1 + max (ht F) (ht F')
    end.

Goal ht = ht0.
Proof.
    reflexivity.
Qed.

Definition ht1(F : Wff) : ℕ.
    Proof.
        induction F.
        - exact 0.
        - exact (1 + IHF).
        - exact (1 + (max IHF1 IHF2)).
        - exact (1 + (max IHF1 IHF2)).
        - exact (1 + (max IHF1 IHF2)).
    Defined.

Goal ht = ht1.
Proof.
    reflexivity.
Qed.



Check @nil.
Check nil.
Check @cons.
Check cons.

Check list.
    
Arguments nil {A}.
Arguments cons {A} a l.

Compute cons true nil.

Compute nil : list bool.

Check nil.
Check @nil.
Check @cons.

Compute @cons bool true nil.
