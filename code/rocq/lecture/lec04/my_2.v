(* lecture 4 review *)


Inductive Wff :=
  P     : nat -> Wff
| Neg   : Wff -> Wff
| Impl  : Wff -> Wff -> Wff
| Conj  : Wff -> Wff -> Wff
| Disj  : Wff -> Wff -> Wff.


Check P 10.
Check Neg (P 10).

Check Impl (P 1) (P 2).

Compute P 10.

Section Scratch.
    Variable dummy : Wff.
    Check Impl dummy.
End Scratch.

Check Impl (P 10).

Notation "a ∧ b" := (Conj a b) (at level 80, right associativity).
Notation "a ∨ b" := (Disj a b) (at level 85, right associativity).
Notation "a ⇒ b" := (Impl a b) (at level 99, right associativity).
Notation "¬ a" := (Neg a) (at level 75, format "¬ a").

Check fun φ => ¬ φ.

Check max 3.

Fixpoint ht (F : Wff) : nat :=
    match F with
    | P i       => 0
    | Neg F     => 1 + ht F
    | Impl F F' 
    | Conj F F'
    | Disj F F' => 1 + max (ht F) (ht F')
    end.

Compute ht (P 0 ∧ (P 1 ⇒ (P 0 ∨ P 3))).

Definition ht0 :=
    fix ht (F : Wff) : nat :=
    match F with
    | P i       => 0
    | Neg F     => 1 + ht F
    | Impl F F' 
    | Conj F F'
    | Disj F F' => 1 + max (ht F) (ht F')
    end.


Goal ht = ht0.
Proof.
    reflexivity.
Qed.

(* Goal: anonymous theorem *)

Definition ht1 (F : Wff) : nat.
Proof.
    induction F.
    - exact 0.
    - exact (1 + IHF).
    - exact ( 1 + (max IHF1 IHF2)).
    - exact ( 1 + (max IHF1 IHF2)).
    - exact ( 1 + (max IHF1 IHF2)).
Defined.


Inductive list (A : Type) :=
| nil : list A
| cons : A -> list A -> list A.

Check nil bool.
Check cons bool true (nil bool).
Check cons bool false (cons bool true (nil bool)).

Check list nat.

Check nil.
Check P.
Check Conj.
Check cons bool.
Check cons.
Check cons Wff (P 0) (nil Wff).

Arguments nil {A}.
Arguments cons {A} a l.

Check cons true (nil).

Check cons false (cons true nil).


Check @cons bool true (@nil bool).

Open Scope list_scope.

From Stdlib Require Import List.
Import ListNotations.

Check [1; 2; 3].
Check 1 :: [2; 4].
Check [].


Fixpoint strict_sf (F : Wff) : list Wff :=
    match F with
    | P i       => nil
    | Neg F     => F :: strict_sf F
    | Conj F F'
    | Disj F F'
    | Impl F F' => (F :: strict_sf F) ++ (F' :: strict_sf F')
    end.

Compute strict_sf (P 0 ∧ P 1).

Fixpoint atoms (F : Wff) : list Wff :=
    match F with
    | P i       => [P i]
    | Neg F     => atoms F
    | Conj F F'
    | Disj F F'
    | Impl F F' => atoms F ++ atoms F'
    end.

Compute atoms (P 0).

Compute atoms (P 0 ∧ (P 1 ⇒ (¬ P 3 ∨ P 0))).

Fixpoint subst_wff (F : Wff) (I : nat -> bool) (G : nat -> Wff) : Wff :=
    match F with
    | P j       => if I j then G j else P j
    | ¬ F       => ¬(subst_wff F I G)
    | F ⇒ F'    => (subst_wff F I G) ⇒ (subst_wff F' I G)
    | F ∧ F'    => (subst_wff F I G) ∧ (subst_wff F' I G)
    | F ∨ F'    => (subst_wff F I G) ∨ (subst_wff F' I G)
    end.

(* Example characteristic function *)

Definition I :=
fun n =>
    match n with
    | 0     
    | 2026 
    | 41
    | 42    => true
    | _     => false
    end.


Definition G1 := fun n => P (n + 2) ∧ P (n + 1).

Check G1.

(* General substitution *)




