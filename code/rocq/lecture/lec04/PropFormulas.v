(* --------------------------------------------------------||
||                                                         ||
||       A TOY IMPLEMENTATION OF PROPOSITIONAL FORMULAS    ||
||                                                         ||
||           Logic and Functional Programming              ||
||               Florent Schaffhauser                      ||
||                                                         ||
||               Heidelberg University                     ||
||                   (Summer 2026)                         ||
||                                                         ||
||-------------------------------------------------------- *)

(* To be able to parse Unicode characters like

ℕ, ∧, ¬ or →

we add support for UTF8. The notation ℕ must be defined manually. *)

From Stdlib Require Import Utf8.

Definition ℕ := nat.

(* To input Unicode characters in VS Code/Codium, you can use extensions such as `latex-input` or `Unicode shortcuts`. In the online scratchpad, ASCII encoding like `->` will render as `→` on the screen, but if you copy-paste your code in a text file, you will see `->` again.

In the Rocq scratchpad (https://coq-next.vercel.app/scratchpad.html?wa), use the following block instead.

````
From Coq Require Import Utf8.

Definition ℕ := nat.
````

*)


(* ---------------------||
||    WELL-FORMED       ||
||      FORMULAS        ||
||--------------------- *)

(* The collection of well-formed formulas is the datatype `Wff` defined inductively as follows:

- Every so-called basic proposition `P₀, P₁, P₂, ...` is a well-formed formula.
- If `F` and `F'` are well-formed formulas and `♢` is one of the symbols `⇒, ∧, ∨`, then `F ♢ F'` is a well-formed formula.
- If `F` is a well-formed formula, then `¬F` is a well-formed formula. 

We now declare the type of well-formed formulas. Take a good look at the syntax of this declaration. *)

Inductive Wff :=
  P    : ℕ   → Wff
| Neg  : Wff → Wff
| Impl : Wff → Wff → Wff
| Conj : Wff → Wff → Wff
| Disj : Wff → Wff → Wff.

(* This in particular defines  

````
  P    : ℕ → Wff 
  Neg  : Wff → Wff
  Impl : Wff → Wff → Wff
  Conj : Wff → Wff → Wff
  Disj : Wff → Wff → Wff
````

called *constructors*, all of whose codomain is `Wff`. *)

Check P.
Check Neg.
Check Impl.

(* Per our declaration, basic propositions are indexed by natural numbers and type-check as well-formed formulas. *)

Check P 0.
Check P 42.

(* We can compose constructors to construct new well-formed formulas out of old ones. *)

Check Neg (P 0).

Check Impl (P 1) (P 2).
Check Conj (P 1) (P 2).

Definition F₁ := Neg (P 0).
Definition F₂ := Conj (P 1) (P 2).

Check F₁.
Check F₂.

Check Impl F₁ F₂.
Compute Impl F₁ F₂.

(* Note that `Impl`, `Conj` and `Disj` are functions of two variables but they are written in "curried notation". This means that `Imp`, for instance, is not defined on the Cartesian product` Wff × Wff`, but instead sends a given well formed formula `F` to a function `Imp F : Wff → Wff`. *)

Section Scratch.
  
  Variable (dummy_formula : Wff).
  Check Impl dummy_formula.

End Scratch.

(* As a side remark, note that Roq recognises `Wff` as something called `Set`. In the declaration, we could have written `Inductive Wff : Set :=` but this is not necessary; it is *inferred* by the type checker. *)

Check Wff.

(* ---------------------||
||      NOTATION        ||
||--------------------- *)

(* For greater convenience, let us implement infix notation for the binary logical connectives. The associativity rules we set are consistent with the ones in Rocq's core library, see https://rocq-prover.org/doc/V9.2.0/corelib/Corelib.Init.Notations.html *)

Notation "a ∧ b" := (Conj a b) (at level 80, right associativity).
Notation "a ∨ b" := (Disj a b) (at level 85, right associativity).
Notation "a ⇒ b" := (Impl a b) (at level 99, right associativity).

(* With these notations, we get the associativity rules that we talked about in the lecture, where expressions such as `P 1 ⇒ P 2 ⇒ P 3` are being parsed as `P 1 ⇒ (P 2 ⇒ P 3)`. Note that we do not need brackets around `P 1` or `P 2` (functions bind tighter that anything else, so to speak). *)

Check P 1 ⇒ (P 2 ⇒ P 3).
Check (P 1 ⇒ P 2) ⇒ P 3.
Check P 1 ⇒ P 2 ⇒ P 3.

Check P 1 ∧ P 2 ∧ P 3.
Check P 1 ∧ (P 2 ∧ P 3).
Check (P 1 ∧ P 2) ∧ P 3.

(* Since `∧` has been set at so-called "level" 80 and `∨` has been set at level 85, the binary operator `∧` binds *tighter* than `∨`. This is an arbitrary convention, but it is common (just like `*` usually binds tighter than `+` when the two pieces of notation are used together).

In practice, this means that `P 1 ∧ P 2 ∨ P 3` is parsed as `(P 1 ∧ P 2) ∨ P 3`, not `P 1 ∧ (P 2 ∨ P 3)`. *)

Check (P 1 ∧ P 2) ∨ P 3.
Check P 1 ∧ (P 2 ∨ P 3).
Check P 1 ∧ P 2 ∨ P 3.

(* It may be helpful to think of Rocq's *levels* as a measure of *distance* between the operator and its arguments: the shorter the distance, the higher the precedence. For instance, in the expression `P 1 ∧ P 2 ∧ P 3`, the distance between `∧` and its arguments is set to 80, while that of `∨` is set to 85. So `P 2` is closer to `∧` than it is to `∨` and the expression is parsed as `(P 1 ∧ P 2) ∨ P 3`.

Similar considerations apply with `⇒`, which binds looser than `∨`, hence also than `∧`. *)

Check F₁ ⇒ ((F₂ ⇒ P 42) ∨ P 3).
Check F₁ ⇒ ((F₂ ⇒ P 42) ∧ P 3).

(* Note that Rocq does not require blank spaces around the operators, but that we usually insert them. *)

Check F₁∧F₂⇒F₁.

(* Similarly for `Neg`, we can introduce a convenient notation. No associativity rule here (`Neg` is not a binary operator), but a formatting rule to guarantee that the pretty printer shows `¬P 0` instead of `¬ P 0` (try it!). *)

Notation "¬ a" := (Neg a) (at level 75, format "¬ a").

Check ¬P 0.
Compute F₁.
Compute F₁ ⇒ F₂.


(* ---------------------||
|| THE HEIGHT FUNCTION  ||
||--------------------- *)

(* When we constructed functions *out of* the type of Booleans in Lecture 3, we did so by pattern matching. We can do so because Booleans are inductively declared in Rocq. More precisely, here is the declaration, as found in Rocq's Core library (https://rocq-prover.org/doc/V9.2.0/corelib/Corelib.Init.Datatypes.html#bool).

````
Inductive bool : Set :=
| true  : bool
| false : bool
````

The intuition is that, in order to define a function `f : bool → X` (where `X` is an arbitrary set/type), it suffices to specify `f true` and `f false` as elements/terms of `X`. Similarly, we should be able to define a function `f : Wff → X` by defining it on each constructor of `Wff`.

Let us for instance declare the height function on well-formed formulas that we introduced in Lecture 2. Two observations are in order:

- A cosmetic one: we can use the notation for `Neg`, `And`, etc as valid syntax in the pattern matching, which makes the code more readable.
- A fundamental one: our height function is defined recursively (it calls upon itself in three out of four subcases), which forces us, in Rocq, to replace the keyword `Definition` with `Fixpoint`.

The answer to the question 'Why is is called `Fixpoint`?` is 'Because it is a fixed point.'. All in good time...

One important point, though, is that, with `Fixpoint`, the syntax 

````
Fixpoint ht : Wff → ℕ` := 
  fun F => match F with
```

is *not* accepted by the typechecker. *)

Fixpoint ht (F : Wff) :=
  match F with
  | P i    => 0
  | ¬F     => 1 + ht F
  | F ∧ F' (* => 1 + max (ht F) (ht F') *)
  | F ∨ F' (* => 1 + max (ht F) (ht F') *)
  | F ⇒ F' => 1 + max (ht F) (ht F')
  end.

(* Note that the return type of the height function is inferred by the type checker (because the first case returns `0` which is parsed as a natural number by the type checker). *)

Check ht.

(* Then not only does this typecheck but it also computes :) *)

Check ht ((P 1 ∧ P 2) ∨ ¬¬P 3).
Compute ht (P 1 ∧ P 2 ∨ ¬¬P 3).

(* If you want to desugar the `Fixpoint` syntax, you can write the same program as follows. Note that the last three cases in the pattern matching are treated in one go! *)

Definition ht₀ : Wff → ℕ :=
  fix ht (F : Wff) : nat :=
  match F with
  | P _                         => 0
  | ¬F0                         => 1 + ht F0
  | F0 ⇒ F' | F0 ∧ F' | F0 ∨ F' => 1 + Nat.max (ht F0) (ht F')
  end.

(* We can check that the two functions `ht` and `ht₀` are indeed equal. This is a proof by reflexivity, which implies that the two function take the same values on every well-formed formula but is, in fact, stronger than that. *)

Goal ht = ht₀.
Proof.
  reflexivity.
Qed.

(* It is possible to use Rocq's tactic language to define the above height function. Namely, one can use the `induction` tactic. It is worth taking a look at, but in practice I recommend using the `Fixpoint` construction. *)

Definition ht₁ (F : Wff) : ℕ.
  Proof.
    induction F.
      (* The `induction` tactic introduces the five sub-cases automatically, as well as the relevant appropriate induction hypotheses in each case (whenever the constructor depends on an already constructed well-formed formula). Note that the inductive hypothesis is used for `ht'` exactly in the same way that the previously defined `ht` calls on itself. *)
    - exact 0.
    - exact (1 + IHF).
    - exact (1 + (max IHF1 IHF2)).
    - exact (1 + (max IHF1 IHF2)).
    - exact (1 + (max IHF1 IHF2)).
  Defined.
  (* Qed *)

Compute ht₁ (P 1 ∧ P 2 ∨ ¬¬P 3).

Goal ht = ht₁.
Proof.
  reflexivity.
Qed.

(* Careful! If you use `Qed` instead of `Defined` in the above construction of `ht'`, then the definition becomes opaque and the computation does not return `3` (try it!). It just prints out the expression again... 

Note that if you do not use focusing points, you can also write the proof as follows. I personally find this less informative. *)

Definition ht₂ (F : Wff) : ℕ.
  Proof.
    induction F.
    exact 0.
    exact (1 + IHF).
    all: exact (1 + (max IHF1 IHF2)).
  Defined.

Compute ht₂ (P 1 ∧ P 2 ∨ ¬¬P 3).

Goal ht = ht₂.
Proof.
  reflexivity.
Qed.

(* ---------------------||
||     SUBFORMULAS      ||
||--------------------- *)

(* We will require Rocq's standard library on linked lists. More precisely, linked lists are defined in Rocq's Corelib.Init.Datatype library

https://rocq-prover.org/doc/V9.2.0/corelib/Corelib.Init.Datatypes.html#list

but the notation we will be using is defined in the standard library:

https://rocq-prover.org/doc/V9.1.0/stdlib/Stdlib.Lists.List.html#ListNotations

Let us first analyse the definition of lists. 

````
Inductive list (A : Type) : Type :=
| nil  : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.
````

It is quite general. We see that it depends on a parameter `A` which is a Type. This enables us to consider lists of natural numbers, lists of booleans, etc. For some reason, Rocq recognises these as sets rather than types. *)

Check list ℕ.
Check list bool.

(* The dependency on the parameter `A : Type` will be referred to as (parametric) **polymorphism**. We can say that `list` is a polymorphic function, in the sense that it takes a type as parameter. 

Once a type `A` is fixed, the type `list A` is defined inductively, using two constructors, `nil {A} : list A` and `cons {A} : A -> list A -> list A`. Because of the `Arguments` command placed after the definition, the parameter `A` is implicit when using `nil` and `cons`. *)

Check nil.
Check cons.

Check @nil.
Check @cons.

Check @nil bool.
Check @cons nat.

(* In general, the implicit parameter can be inferred by the typechecker, as we shall see below when we construct our first examples of lists. *)

Check (nil : list nat).
Check cons true (cons false nil).

(* The syntax with `cons` and `nil` is hard to parse. This is why `cons` is replaced by the following infix notation. 

````
Infix "::" := cons (at level 60, right associativity) : list_scope.
````

To access it, we can either put the notation in scope explicitly, or import a module that opens it (see below). *)

Open Scope list_scope.
Check 1 :: 2 :: 3 :: nil.

(* This is better, but not yet optimal in practice. So we import the following module. *)

From Stdlib Require Import List.
Import ListNotations.

(* In the Rocq scratchpad (https://coq-next.vercel.app/scratchpad.html?wa), use the following block instead.

````
From Coq Require Import List.
Import ListNotations. 
````

*)

(* This makes the pretty printer view of lists much nicer. And more importantly, we can use that same syntax to denote lists in our code, in a variety of ways. *)

Check 1 :: 2 :: 3 :: nil.
Check [1; 2; 3].
Check 1 :: [2; 3].
Check [42].

(* Let us now use lists to implement the function `strict_sf` seen in Lecture 2. Here, we do this using the constructors actual names, not the notation we introduced for them, but you can change `Neg F` to `¬F`, `Conj F F'` to `F ∧ F'` etc. Note that the order in which you enter the constructor does not matter for the pattern matching, and that you can use the notation `F` in the pattern `Neg F` etc, even though you are pattern matching on a parameter called `F` in the body of the function. *)

Fixpoint strict_sf (F : Wff) : list Wff :=
  match F with 
  | P i       => nil
  | Neg F     => F :: strict_sf F
  | Conj F F' => (F :: strict_sf F) ++ (F' :: strict_sf F')
  | Disj F F' => (F :: strict_sf F) ++ (F' :: strict_sf F')
  | Impl F F' => (cons F (strict_sf F)) ++ (cons F' (strict_sf F'))
  end.

(* The resulting function returns a list of the strict subformulas of a given formula, as expected. If you remove `list Wff` from the declaration of `strict_sf`, the return type will be inferred by the type checker, because of the syntax `F :: _` in the second case, for `F` of type `Wff` (try it!). *)

Check strict_sf.
Compute strict_sf ((P 1 ∧ P 2) ∨ ¬¬P 3).

(* We can then define the subformula function as in Lecture 2. *)

Definition sf (F : Wff) : list Wff :=
  F :: (strict_sf F).

Compute sf ((P 1 ∧ P 2) ∨ ¬¬P 3).


(* ---------------------||
||    SUBSTITUTIONS     ||
||--------------------- *)

(* Given a well-formed formula `F`, a subset `I ⊂ ℕ` and a family of well-formed formulas `G : ℕ → Wff`, we have seen in the lecture how to replace the atomic formulas `P n` by `G n` in `F`, for all `n ∈ I`. Let us now implement this function in practice. *)

Fixpoint subst_Wff (F : Wff) (I : ℕ → bool) (G : ℕ → Wff) : Wff :=
  match F with 
  | P j     => if I j then G j else P j
  | ¬F      => ¬(subst_Wff F I G)
  | F₁ ⇒ F₂ => (subst_Wff F₁ I G) ⇒ ((subst_Wff F₂ I G))
  | F₁ ∧ F₂ => (subst_Wff F₁ I G) ∧ ((subst_Wff F₂ I G))
  | F₁ ∨ F₂ => (subst_Wff F₁ I G) ∨ ((subst_Wff F₂ I G)) 
  end.

(* For the sake of simplicity, we will use the same characteristic function `I : ℕ → bool` in all our examples. Note how we define `I` using pattern matching when we want it to represent the finite subset `{0; 2026; 42}` of the set `ℕ`. *)

Definition I (n : ℕ) : bool :=
  match n with
  | 0    => true
  | 2026 => true
  | 41   => true
  | 42   => true
  | _    => false
  end.


(* ------------------------ EXAMPLE 1 ------------------------ *)
  
(* Let us define a family of formulas to be used when performing the substitution of certain atomic formulas. In this example `G₁ n` is different from `P n` for all `n`, but in the substitution, only those `G n` for which `I n = true` will matter. *)

Definition G₁ : ℕ → Wff :=
  fun n => P (n + 2) ∧ P (n + 1).

(* In the example below, every atomic subformula `P j` for which `I j = true` (so, everything except 2025) is replaced by something new, because `G₁ j ≠ P j` for all `ij. Note that `I 41 = true` but that this plays no role because `P 41` does not appear in our example for `F`. *)

Compute subst_Wff (P 0 ∨ P 2026 ⇒ P 42 ∧ P 2025) I G₁.

(* ------------------------ EXAMPLE 2 ------------------------ *)

(* We can also define a family of formulas in a way similar to what we did for `I`, meaning that we only care about defining `G₂ n` for a finite number of `n` and for all other `n` we simply set `G n = P n`. *)

Definition G₂ : ℕ → Wff :=
  fun n => match n with
  | 2025 => P 44
  | 2026 => P 1 ⇒ P 2
  | _    => P n 
  end.

(* In the example below, only `P 2026` is replaced by `G 2026` (even though `G 2025 ≠ P 2025` and `P 2025` appears in our example for `F`), because `I 2025 ≠ true`. *)

  Compute subst_Wff (P 0 ∨ P 2026 ⇒ P 42 ∧ P 2025) I G₂.
  
(* ------------------------ EXAMPLE 3 ------------------------ *)

(* For the third example, we define a family of formulas using a conditional statement. The point is to show an example where `G n ≠ P n` for an infinite quantity of `n` but also `G n = P n` for an infinite quantity of `n`. We will do so by defining the characteristic function of even numbers. *)

From Corelib Require Import Init.Nat.

(* In the Rocq scratchpad (https://coq-next.vercel.app/scratchpad.html?wa), use the following block instead.

````
From Coq Require PeanoNat.
Import Nat.
````

*)

Definition is_even (n : nat) : bool :=
  eqb (n mod 2) 0.

Definition G₃ (n : ℕ) : Wff :=
  if is_even n then P (n / 2) else P n.

(* In the example below, an atomic formula `P j` is replaced by `G (j / 2)` if and only if `I j = true` and `is_even j = true`. *)
  
Compute subst_Wff (P 0 ∨ P 2026 ⇒ P 41 ∧ P 2025) I G₃.

(* ------------ SUBSTITUTIONS IN INDEXED FAMILIES ------------ *)

(* The definition of the function `subst_Wff` suggests a general method to substitute terms in a family `P : Y → X` (family of terms of type `X` indexed by the type `Y`). All you need is a subtype of `Y` (represented by a characteristic function `I : Y → X`) and a new family `G : Y → X`, indexed by the same type `Y`. 

Then for all element `y` of `Y`, if `y` belongs to the subset `I` (which means that the characteristic function `I` evaluates to `true` on `y`), one replaces `P y` with `G y`, and if `y` does not belong to `I`, then one leaves `P y` unchanged. *)

Definition substFamily {Y} {X} : (Y → X) → (Y → bool) → (Y → X) → Y → X :=
  fun P I G y => if I y then G y else P y.

(* One can then redefine `subst_Wff` as follows and check that it behaves as expected on our examples. This time we place `(F : Wff)` last, so `subst_Wff' I G : Wff → Wff`. *)

Fixpoint subst_Wff' (I : ℕ → bool) (G : ℕ → Wff) (F : Wff) : Wff :=
  match F with 
  | P j     => substFamily P I G j (* if I j then G P I j else P j *)
  | ¬F      => ¬(subst_Wff' I G F)
  | F₁ ⇒ F₂ => (subst_Wff' I G F₁) ⇒ ((subst_Wff' I G F₂))
  | F₁ ∧ F₂ => (subst_Wff' I G F₁) ∧ ((subst_Wff' I G  F₂))
  | F₁ ∨ F₂ => (subst_Wff' I G F₁) ∨ ((subst_Wff' I G F₂))
  end.

Compute subst_Wff  (P 0 ∨ P 2026 ⇒ P 42 ∧ P 2025) I G₁.
Compute subst_Wff' I G₁ (P 0 ∨ P 2026 ⇒ P 42 ∧ P 2025).

Compute subst_Wff  (P 0 ∨ P 2026 ⇒ P 42 ∧ P 2025) I G₂.
Compute subst_Wff' I G₂ (P 0 ∨ P 2026 ⇒ P 42 ∧ P 2025).

Compute subst_Wff  (P 0 ∨ P 2026 ⇒ P 42 ∧ P 2025) I G₃.
Compute subst_Wff' I G₃ (P 0 ∨ P 2026 ⇒ P 42 ∧ P 2025).

(* ---------------------||
||      EXERCISE        ||
||--------------------- *)

(* As an exercise to practice the techniques seen in this file, add one more constructor

`Iff : Wff → Wff → Wff` 

to the type of well-formed formulas, then introduce the (non-associative) infix notation 

`⇔` (or `<=>`) 

for it, and complete the definitions of `ht`, `strict_sf` and `subst_Wff` accordingly. 

Be careful with the precedence level for `⇔`. In Rocq's notation for propositional connectives (https://rocq-prover.org/doc/V9.2.0/corelib/Corelib.Init.Notations.html), the formulas `P 1 ⇒ P 2 ⇔ P 3` and  `P 2 ⇔ P 3 ⇒ P 1` parse respectively as `P 1 ⇒ (P 2 ⇔ P 3)` and `(P 2 ⇔ P 3) ⇒ P 1`. *)
