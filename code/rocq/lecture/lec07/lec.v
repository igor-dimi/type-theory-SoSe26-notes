(* --------------------------------------------------------||
||                                                         ||
||         INTERPRETATION OF WELL-FORMED FORMULAS          ||
||                                                         ||
||           Logic and Functional Programming              ||
||                 Florent Schaffhauser                    ||
||                                                         ||
||                 Heidelberg University                   ||
||                    (Summer 2026)                        ||
||                                                         ||
||-------------------------------------------------------- *)

From Coq Require Import Utf8.

Definition ℕ := nat.

(* In this file, we use Rocq's specification language Gallina 
(also called the vernacular, hence the `.v` as extension for 
Rocq files) as a meta-language in which we can reason about 
the Boolean semantics of well-formed formulas. *)

(* ---------------------||
||     WELL-FORMED      ||
||       FORMULAS       ||
||--------------------- *)

(* We give a slightly more general definition of well-formed 
formulas, in which the atomic formulas are indexed by an 
arbitrary set called `atoms`, which we declare as an implicit 
parameter (otherwise we have to change `Wff` to `Wff atoms` 
in every constructor below). *)

Inductive Wff {atoms : Set} :=
| P     : atoms → Wff
| Neg   : Wff → Wff
| Conj  : Wff → Wff → Wff
| Disj  : Wff → Wff → Wff
| Impl  : Wff → Wff → Wff
| Equiv : Wff → Wff → Wff.

(* So now, the function `Wff` takes a set as argument and 
returns a set. Our previous version was using `nat` as an 
indexing set for basic formulas, so we recover it using 
`@Wff nat`. *)

Check @Wff.             (* @Wff : Set → Set*)
Check @Wff ℕ.           (* Wff : Set *)

(* The constructor for atomic formulas now behaves as 
follows. *)

Check @P.               (* : ∀ atoms : Set, atoms → Wff *)
Check @P ℕ.             (* P : ℕ → Wff *) 

(* But note that when `atoms = ℕ`, we can keep using the 
syntax we previously had: since the literal `3` is 
recognised as a natural number, the implict parameter 
`atoms` is automatically *inferred* to be `ℕ`. *)

Check P 3.               (* P 3: Wff *)

(* Similar considerations apply for other constructors.*)

Check @Conj.            (* Conj : ∀ atoms : Set, Wff → Wff → Wff *)
Check @Conj ℕ.          (* Conj : : Wff → Wff → Wff *)

(* We also recall the notation for the constructors of 
well-formed formulas. *)

Notation "¬ F" := (Neg F) 
  (at level 75, right associativity, format "¬ F").
Notation "F ∧ F'" := 
  (Conj F F') (at level 80, right associativity).
Notation "F ∨ F'" := 
  (Disj F F') (at level 85, right associativity).
Notation "F ⇒ F'" := 
  (Impl F F') (at level 99, right associativity).
Notation "F ⇔ F'" := 
  (Equiv F F') (at level 95, no associativity).

(* ---------------------||
||  ADDITIONAL NOTATION ||
||--------------------- *)

(* We will also need additional notation for boolean 
operators.  The symbol `≼` is obtained via the LaTeX 
command `\preccurlyeq`. In the online Scracthpad, you 
may need to use a different symbol or copy-paste that 
one. *)

Notation "! b" := (negb b) 
  (at level 75, right associativity, format "! b").
Notation "b && b'" :=
  (andb b b') (at level 40, left associativity).
Notation "b || b'" :=
  (orb b b') (at level 50, left associativity).
Notation "b ≼ b'" := 
    (implb b b') (at level 99, right associativity).

(* Let us recall the definition of the `bool`-valued 
equality on the set `bool` and the notaion for it. *)

Definition eqb : bool → bool → bool :=
  fun b b' =>
  match b, b' with
  | true, true   => true
  | true, false  => false
  | false, true  => false
  | false, false => true
  end.

Notation "b == b'" := 
  (eqb b b') (at level 95, no associativity).

(* Finally, we will need the standard notation for lists. *)

Infix "::" := 
  cons (at level 60, right associativity).

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := 
  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : list_scope.

(* ---------------------||
||    INTERPRETATIONS   ||
||--------------------- *)

(* Our goal is now to construct an interpretation (or
evaluation function) for well-formed formulas. As in the 
lecture, we will take this function to be `bool`-valued.
More precisely, given a valuation

`v : atoms → bool,

we will construct a function

`eval v : Wff → bool`

where by `Wff` we mean `@Wff atoms`. This is the function that 
was denoted by $\widehat{\nu}$ (or $[\ ]_ν$ in the lecture.

Concretely, the function `eval v` is defined recursively as 
follows (note that it again takes a set `atoms` as implicit 
parameter. *)

Fixpoint eval {atoms : Set} (v : atoms → bool) (F : Wff) 
  : bool :=
match F with
| P i    => v i
| ¬F     => !(eval v F)
| F ∧ F' => (eval v F) && (eval v F')
| F ∨ F' => (eval v F) || (eval v F')
| F ⇒ F' => (eval v F) ≼ (eval v F')
| F ⇔ F' => (eval v F) == (eval v F')
end.

(* Then, for each set `atoms`, we have a family of 
interpretations, indexed by the type of valuations 
`atoms → bool`. *)

Check @eval.
  (* eval : : ∀ atoms : Set, (atoms → bool) → Wff → bool *)

(* The special case we saw in the lecture is then recovered 
as follows. *)

Check @eval ℕ.
  (* eval :  : (ℕ → bool) → Wff → bool *)

(* Let us now construct an example, with just a few atomic 
formulas, as in the lecture. We start with a set with just 
two elements. *)

Inductive twoAtoms := (* A | B *)
| A : twoAtoms
| B : twoAtoms.

Check twoAtoms.                   (* twoAtoms : Set *)
Check A.                          (* A : twoAtoms *)

(* Then *P A* and *P B* are well-formed formulas. *)

Check @Wff twoAtoms.              (* Wff : Set *)
Check P A.                        (* P A : Wff *)

(* Since we only have two atomic formulas, there are exactly 
four possible valuations, false-false, false-true, true-false, 
and true-true. *)

Definition ff : twoAtoms → bool :=
  fun a => match a with
  | A => false
  | B => false
  end.

Definition ft : twoAtoms → bool :=
  fun a => match a with
  | A => false
  | B => true
  end.

Definition tf : twoAtoms → bool :=
  fun a => match a with
  | A => true
  | B => false
  end.

Definition tt : twoAtoms → bool :=
  fun a => match a with
  | A => true
  | B => true
  end.

Check ft.                         (* ft : twoAtoms → bool *)
Check eval ft.                    (* eval ft : Wff → bool *)

(* Now we can use any of them to evaluate the truth value of 
any formula constructed out of `A` and `B`. Note what we 
should not forget the constructor `P`  before `A` and `B` if 
we want to have well-formed formulas. *)

Check P A ∨ P B.                  (* P A ∨ P B : Wff *)
Check eval ft (P A ∨ P B).        (* eval ft (P A ∨ P B) : bool *) 
Compute eval ft (P A ∨ P B).      (* = true *)

(* This next example is taken directly from Lecture 5 (Example 
5.1.4). The type checker computes/reduces the formula to a 
boolean value. *)

Check (P A ∨ P B) ∧ ¬P A.         
  (* (P A ∨ P B) ∧ ¬P A. : Wff *)
Compute eval ft ((P A ∨ P B) ∧ ¬P A).
  (* = true *)

(* Note that the constructor `P` makes the formula look a bit
cluttered. We can get rid of it by setting up a **coercion** 
from atoms to well-formed formulas. This essentially means a 
function `coe : atoms → @Wff atoms` which we then register 
as a coercion in order to **not have to write it**. 

The precise way in which this works is: if we have a function 
`f : Wff → X`, a coercion `coe : atoms → Wff`, and an atom 
`a`, then, when we write `f a`, which is not well-typed 
(because `a` is of type `atoms`, not `Wff`), this will 
**automatically** be interpreted as `f (coe a)`, which is 
well-typed.

Here, we just use the constructor `P : atoms → Wff` to define 
the coercion, which we register using the keyword 
`Coercion`. *)

Definition twoAtomsToWff : twoAtoms -> Wff := (* P *)
  fun a => P a. 

Coercion twoAtomsToWff : twoAtoms >-> Wff.

(* Now we can do without the constructor `P` to write 
well-formed formulas and use them as arguments to functions 
out of `Wff`. *)

Check (A ∨ B) ∧ ¬A.               (* (A ∨ B) ∧ ¬A : Wff *)
Compute eval ft ((A ∨ B) ∧ ¬A).   (* = true *)

(* We will now specify a functions which returns the truth 
table of a well-formed formula constructed out of just two 
atoms. Unsurprisingly, we use lists for that. *)

Fixpoint evalList {atoms : Set} (vals : list (atoms → bool)) 
    : Wff → list bool :=
  fun F => match vals with
  | nil => nil
  | v :: vs => (eval v F) :: (evalList vs F)
  end.

(* This next list corresponds to the column in the truth table 
seen in Section 5.1.4 of the lecture. *)

Compute evalList [ff; ft; tf; tt] ((A ∨ B) ∧ ¬A).
  (* = [false; true; false; false] *)

(* If we prefer, we can hide the list of valuations and always 
present the truth table of a formula with two atoms in the 
following way. If we do that, we have to remember that we 
have chosen the order `[ff; ft; tf; tt]` for the truth values 
of the two atoms. *)

Definition truthTableTwoAtoms : @Wff twoAtoms → list bool :=
  evalList [ff; ft; tf; tt].

Compute truthTableTwoAtoms ((A ∨ B) ∧ ¬A).
  (* = [false; true; false; false] *)

(* ---------------------||
||  LOGICAL EQUIVALENCE ||
||--------------------- *)

(* With what we have done, we can formalise logical 
equivalence between well-formed formulas in the following 
way. *)

Definition LogicalEquiv {atoms : Set} (F F' : Wff) :=
  forall v : atoms → bool, eval v F = eval v F'.

(* For each set `atoms`, the function `LogicalEquiv` takes
two well-formed formulas and returns a proposition. As 
discussed in class, this `Prop` type in Rocq is here mostly 
for historical reasons. It introduces a separation between 
propositions and sets that is in particular useful for 
program extractions, in which types marked as propositions 
are erased. *)

Check @LogicalEquiv.
  (* @LogicalEquiv : ∀ atoms : Set, Wff → Wff → Prop *)

(* We introduce the notation for logical equivalence used in 
the lecture. *)

Infix "≡" := LogicalEquiv (at level 120, no associativity).

(* We define tautologies (valid formulas) as follows, using 
our `eval` function. *)

Definition isTauto {atoms : Set} (F : Wff) :=
  forall v : atoms → bool, eval v F = true.

(* For each set `atoms`, the function `isTauto` is a 
**predicate** on the set `Wff` (more precisely, `@Wff atoms`).
This means that, when applied to a well-formed formula `F`, it 
returns a proposition `isTauto F`. 

But, careful! This proposition may or may be provable. For now, 
it is is just well-typed in our language. A `Prop`-valued 
function does *not* return a (boolean) truth value. *)

Check @isTauto.

(* We can now characterise a logical equivalence `F ≡ F'` as 
we did in the lecture, by proving that it is equivalent (in 
our meta-language) to the well-formed formula `F ⇔ F'` being 
a tautology. 

This is our first complex proof in Rocq. It uses a lot of 
different tactics to manipulate the proof state and reach a 
conclusion. We will learn how to write such proofs but for now
it is mostly how we can use Rocq for the purposes of improving
our understanding of the proofs given in the lecture. *)

Theorem characLogicalEquiv {atoms : Set} (F F' : @Wff atoms) : 
  (F ≡ F') ↔ isTauto (F ⇔ F').
Proof.
  split.
    (* The `split` tactic replaces the equivalence in the goal 
    by the two subgoals corresponding to each of the two 
    implications. *)
  + intro logEq.
    unfold isTauto.
      (* the `unfold` tactic literally unfolds certain 
      definitions 
      for us, it acts on the goal but later we will also use 
      it on definitions contained in the context *)
    simpl.
    intro v.
    unfold LogicalEquiv in logEq.
    pose proof logEq v (* as H *).
      (* we add the term `logEq v` to our context, which is a 
      proof of `eval v F = eval v F'; this does not create a 
      new proof obligation *)
    revert H.
    destruct (eval v F), (eval v F').
      (* this is the step where we reason by case analysis; 
      note that, without `revert H`, the assumptions for each 
      subgoal are only displayed when reaching the subgoal, 
      which is less readable. *)
    (* - simpl. reflexivity.
    - simpl. symmetry. assumption.
    - simpl. assumption.
    - simpl. reflexivity. *)
      (* Regardless, we can use several degrees of automation 
      to complete these proofs for us. *)
    (* all: simpl; trivial.
    symmetry. assumption. *)
    all: simpl; auto.
      (* another possible proof of this implication is, after 
      `pose proof logEq v as H`, to use `rewrite H`, and to prove 
      an auxiliary result that says that 
      `∀ b : bool, b == b = true`. *)
  + intro H.
    unfold LogicalEquiv.
    intro v.
    unfold isTauto in H.
    pose proof H v (* as H0 *).
    simpl in H0.
    revert H0.
    destruct (eval v F), (eval v F').
    all: simpl; auto.
Qed.

(* Here is what the `trivial` tactic tries:

- Prove an equality by `reflexivity`.
- Use `assumption` to see is there is a proof in the context.
- Go through a list of the constructors (if the goal is inductive).
- Look through a database of already proved results that might help.

As seen above, `trivial` cannot apply basis results such as 
`symmetry`. For this, we need `auto`, which can also do more 
than that. There are further automation tactics (`tauto`for 
propositional tautologies (in the sense of `Prop`), `eauto`, 
which handles some existential quantifiers, *etc*. *)

(* ---------------------||
||      SATISFIABLE     ||
||       FORMULAS       ||
||--------------------- *)

(* Let us recall the definition of satisfiability from the 
lecture. *)

Definition isSatis {atoms : Set} (F : Wff) :=
  exists v : atoms → bool, eval v F = true.

(* Let us prove formally that a well-formed formula `F` is a 
tautology if and only if `¬F` is not satisfiable. Here, we take 
`not satisfiable` to mean the following: if it were satisfiable, 
then something absurd would follow. And as witness of absurdity 
in this context, we take the proposition `false = true` 
(equality between Boolean values. *)

Theorem isTauto_iff_neg_not_isSatis {atoms : Set} 
  (F : @Wff atoms) :
  isTauto F ↔ (isSatis (¬F) → false = true).
Proof.
  split.
  + intro h1.
    unfold isTauto in h1.
    intro h2.
    unfold isSatis in h2.
    destruct h2 as [v pf].
    simpl in pf.
    pose proof h1 v as H.
    rewrite H in pf.
      (* since we have a proof that `eval v F = true`, we can 
      substitute `eval v F` by `true` in the expression 
      `!eval v F = true`, to get `!true =true`, which can in 
      turn be simplified *)
    simpl in pf.
    exact pf.
  + intro h.
    unfold isTauto.
    unfold isSatis in h.
    intro v.
    destruct (eval v F) eqn:hvF.
    - reflexivity.
    - apply h.
        (* note how the target `false = true` of the function 
        `h` unifies with the goal we had before using the 
        `apply` tactic *) 
      exists v.
        (* the `exists` tactic introduces the witness we will 
        use to prove an existential goal *)
      simpl.
      rewrite hvF.
      reflexivity.
Qed.
    
(* Why is a proof of `false = true` a good witness of 
absurdity? You might prefer to define absurdity as having 
a proof of `False`, where `False` is the empty proposition, 
defined inductively as the proposition with no constructors. *)

Check False.
  (* False : Prop *)
Print False.
  (* Inductive False : Prop :=    . *)

(* We could also use `Empty_set`, which is the inductively 
defined set with no constructors. Then an element of the 
empty set will be our witness of an absurdity. *)

Check Empty_set.
  (* Empty_set : Set *)
Print Empty_set.
  (* Inductive Empty_set : Set :=    . *)

(* To construct a proof of `False`, the idea is to use the 
context (namely the equality `false = true` in `bool`) to 
construct an identification between `False` and the 
proposition called `True`, which is defined inductively by a 
single atomic constructor. *)

Check True.
 (* True : Prop *)
Print True.
  (* Inductive True : Prop :=   I : True. *)

(* Alternatively, we could construct an identification between 
`Empty_set` and the singleton set `unit`, also defined 
inductively by a single atomic constructor. *)

Check unit.
  (* unit : Set *)
Print unit.
  (* Inductive unit : Set :=    tt : unit. *)

(* Let us do it with propositions and leave the analogous 
proof with sets as an exercise. So the goal is to show that 
`false = true` implies `False`. The first step is to construct 
a function `bool → Prop` which sends `false` to `False` and 
`true` to `True`. *)

Definition boolToProp : bool → Prop :=
  fun b => match b with
  | false => False
  | true  => True
  end.

(* Thanks to the function `boolToProp`, we can deduce from 
`true = false` that `True = False`, and since we have an 
element in `True` (i.e. a proof of `True`), we can use the 
identification `True = False` to construct an element of 
`False`. *)

Goal (false = true → False).
Proof.
  intro eq.
  assert (eqProp : False = True).
   (* The `assert` tactic is a local declaration: we add a 
   new term to the context by constructing it, which creates 
   a new subgoal, that we must close before we go on with the 
   proof *)
  + apply (f_equal boolToProp eq).
    (* this uses the congruence property `x = y → f x = f y`,
    which can sometimes be automated via the 
    `f_equal` tactic *)
    (* f_equal. *)
  + rewrite eqProp.
      (* since we have a proof that `False = True`, we can 
      substitute `False` by `True` in the goal, which we can 
      then close *)
    exact I.
    (* this term can also be found automatically *)
    (* constructor. *)
Qed.
