(* --------------------------------------------------------||
||                                                         ||
||          BOOLEAN VALUES AND PATTERN MATCHING            ||
||                                                         ||
||              Logic and Functional Programming           ||
||                  Florent Schaffhauser                   ||
||                                                         ||
||                  Heidelberg University                  ||
||                      (Summer 2026)                      ||
||                                                         ||
||-------------------------------------------------------- *)


(* ---------------------||
||  BOOLEANS IN ROCQ'S  ||
||    CORE LIBRARY      ||
||--------------------- *)

(* Boolean values are available without any imports in Rocq. 
We have two canonical Boolean values, called `true` and 
`false`. *)

Check true.
Check false.

(* The type of Booleans is called `bool` and is recognised as 
something called `Set` in Rocq. *)

Check bool.
About bool.
Check Set.
Check Type.

(* Certain pre-defined functions are also available out of 
the box and can be used to compute expressions. *)

Check negb.
About negb.

Check negb false.
Compute negb false.

(* A function of two variables like `orb` are written in 
**curried notation**. This means that the value or `orb` on a 
pair `such as ( true , false )` is written `orb true false`, 
not `orb ( true , false )`. In turn, the expression 
`orb true`, for instance, denotes a *function* from `bool` 
to `bool`. *)

Check orb true false.
Check orb.
Check bool -> (bool -> bool).
Check orb true.

(* We can compute using this syntax. *)

Compute negb (orb true false).

(* In the rest of the file, we construct basic functions from 
`bool` to `bool`. Most of them, if not all, are contained in 
Rocq's core library, but we do this to learn how to use 
**pattern matching** in order to construct functions.*)


(* ---------------------||
||   BASIC PATTERN      ||
||     MATCHING         ||
||--------------------- *)

(* To avoid conflicts with Rocq's core library, we wrap 
everything in a module that we choose to call `BooleanValues`. 
This is optional here, since we do not intend to use the 
current file anywhere else later on. *)

Module BooleanValues.

(* -------------------- BOOLEAN NOT -------------------- *)

(* Let us start with the definition of the `negb` function, 
which sends `true` to `false` and vice versa. We define it by 
pattern matching on Boolean values. Note that we can use the 
same name and that this does not cause any conflict with the 
existing Rocq `negb` function. *)

Definition negb (b : bool) : bool :=
  match b with
  | true  => false
  | false => true
  end.

Check negb.

(* From now on, when we write `negb`, it will refer to the 
`negb` function defined above. You can check this by modifying 
the definition (sending everything to `false`, for instance, 
and computing a few values. *)

About negb.
Compute negb false.

(* We can chain also give expressions a name to manipulate 
them in computations. *)

Compute negb (negb false).

Definition example_bool := negb false.

Compute negb example_bool.

(* -------------------- BOOLEAN AND -------------------- *)

(* Now we want to define an `andb` function, that takes two 
Booleans `b, b'` and returns `andb b b'`. The value of 
`andb b b'` a priori depends on the values of `b` and `b'`, 
so we have four cases to consider when pattern matching. *)

Definition andb (b b' : bool) : bool :=
  match b, b' with
  | true,  true  => true
  | true,  false => false
  | false, true  => false
  | false, false => false
  end.

(* In fact, some simplifications are possible. *)

  (* match b, b' with
  | true,  b' => b'
  | false, _ => false
  end. *)

(* Another way of doing the pattern matching, that you may 
want to avoid, is pattern matching first on `b`, then on `b'`,
which results in a nested program. It typechecks, though. Note 
that the only the final `end` has a period following it. *)

  (* match b with
  | true => 
    match b' with 
    | true  => true 
    | false => false 
    end
  | false => 
    match b' with
    | true  => false
    | false => false
    end
   end. *) 
   
(* As with `negb`, we can use `andb` to compute using Boolean 
values. *)

Compute andb true false.
Compute andb true (negb example_bool).

(* Recall that `andb` is a function of two variables, but it 
is written in **curried notation**, and that you can check 
that as follows: if you pass `Check andb.`, the elaborator 
returns `andb : bool -> bool -> bool`, not 
`andb : bool × bool -> bool`. This means that an expression 
like `andb true`, for instance, is a *function* from `bool` 
to `bool`. *)

Check andb.
Check andb true.
Compute andb true.

(* We see in particular, that arrow types associate to the 
right: 

 (bool -> bool -> bool) = (bool -> (bool -> bool))

which *forces* the following expression to be parsed as 
follows:

 andb b b' = (andb b) b'

In contrast, the arrow type `(bool -> bool) -> bool` takes a 
function `f : bool -> bool` and returns a `bool`. We can 
define an example of a function 
with type signature `(bool -> bool) -> bool` by evaluating 
`f : bool -> bool` at a given Boolean value.` *)

Definition eval_at_true : (bool -> bool) -> bool :=
  fun f => f true.

Compute eval_at_true negb.
Compute eval_at_true (andb true).

Definition eval_at (b : bool) : (bool -> bool) -> bool :=
  fun f => f b.

Compute eval_at false negb.
Compute eval_at false (andb true).

(* -------------------- BOOLEAN OR -------------------- *)

(* Let us define an `orb` function on Booleans. *)

Definition orb (b b' : bool) : bool :=
  match b, b' with
  | true,  _  => true
  | false, b' => b'
  end.

(* In fact, we are not using `b'` as a pattern, so we can 
also write the following. *)

  (* match b with
  | true  => true
  | false => b'
  end. *)

Compute orb false false.
Compute orb false (negb false).

(* -------------------- BOOLEAN IMPLICATION -------------------- *)

(* Let us define a function called implication (between two 
Boolean values). For this one, we will use Rocq's if-then-else 
function, which uses pattern matching behind the scenes. Note 
the syntax using mixfix notation.*)

Definition implb (b b':bool) : bool := 
  if b then b' else true.

(* EXERCISE. Implement the function `implb` using pattern 
matching. The result of the following computation should be 
the Boolean `true`. *)

Compute implb false true.

(* As one more exercise, implement the Boolean if-then-else 
function as a function with type signature 
`bool -> bool -> bool`. *)


(* ---------------------||
||  THEOREM PROVING     ||
||--------------------- *)

(* Next, we start using Rocq as a means to prove certain 
properties of the function we have defined. The syntax looks 
a bit different at first, but in fact we will see in the 
course that stating a theorem is not that different from 
declaring a function. *)

(* ---------------- NEGATION IS INVOLUTIVE ---------------- *)

(* The first property that we will prove is that, for all 
Boolean value `b`, we have an equality `negb (negb b) = b'. 
Let us start with some special cases, in which we prove our 
equality by a direct computation. Note the interactive 
**tactic state** on the right-hand-side of the editor, which 
guides us in our proof. *)

Theorem negb_negb_true_eq_true : negb (negb true) = true.
Proof.
  simpl.
    (* The `simpl` tactic simplifies the terms for you,
    essentially by computation. *)
  reflexivity.
    (* You can always use `reflexivity` to *test* whether the 
    equality follows from a direct computation. *)
Qed.

(* If you are just getting started with theorem provers, you 
should focus here on the block that starts with `Proof` and 
ends with `Qed`. This is a Rocq program, like the one defining 
the `negb` or `andb` functions`, but *written in a different 
language*, namely the tactic language `ltac`, which gets 
superposed onto the basic Rocq language, called *Gallina*. 

If you try to prove something incorrect, the prover will let 
you know. *)

Theorem negb_negb_false_eq_false : negb (negb false) = false.
Proof.
  reflexivity.
Qed.

(* Here is the same program, written in Gallina. Note that it 
requires changing `Theorem` to `Definition`. *)

Definition negb_negb_false_eq_false' : 
    negb (negb false) = false :=
  eq_refl.

(* You can check that this is indeed the same program using 
the `Print` command. *)

Print negb_negb_false_eq_false.
Print negb_negb_false_eq_false'.

(* If you try to prove something incorrect, the prover will 
let you know. *)

Theorem fail_to_unify : negb (negb false) = true.
Proof.
  Fail reflexivity.
Admitted.

(* Now let us see how to use pattern matching in proofs. The 
`destruct` tactic plays the same role as the `match` keyword 
in Gallina. After that, there are two so-called **subgoals** 
to close and we can isolate each one by using a focusing dash 
(or plus sign). The `Qed` keyword is optional and lets you 
visually check that your proof is complete. *)

Theorem negb_inv (b : bool) : negb (negb b) = b.
Proof.
  destruct b.
  (* Note that the goal has been modified: in the first case,
  `b` has been replaced by `true`, and in the second case `b` 
  has been replaced by `false`. *)
  - simpl. reflexivity.
  (* - reflexivity. *) 
  (* Note that the `simpl` tactic is not actually needed to 
  test the equality. *)

  (* You can also call on previous proofs, using the `exact` 
  tactic. Try it by commenting out the `reflexivity` tactic 
  above. *)  
  - exact negb_negb_false_eq_false.

Qed.

(* One may observe that, in this formalism, the expression 
`negb_inv true` is a proof of the equality 
`negb (negb true) = true`, and `negb_inv` is a proof of the 
proposition `∀ b : bool, negb (negb b) =b`. *)

Check negb_inv true.
Check negb_inv.

(* -------- EQUIVALENT DEFINITIONS OF IMPLICATION -------- *)

(* Recall the formulas 

  (P ⇒ Q) ⇔ ¬P ∨ Q

and

  (P ⇒ Q) ⇔ ¬(P ∧ ¬Q)

from classical logic. The first is in fact often taken as a 
definition of implication in classical logic. We will further 
comment on this later in the course.

In what follows, we interpret `⇒` as `implb`, `¬` as `negb`, 
`∨` as `orb`, `∧` as `andb` and `⇔` as Rocq's equality `=` to 
prove that we can define `implb` in two more ways, equivalent 
to the choice we made in the sense that the resulting function 
of two variables takes the same value as `implb` on all 
`b b' : bool`. 

This exercise also shows how we can structure a proof with 
pattern matching on several variables in it. First, we present 
a nested version: we first pattern match on `b` and then we 
pattern match on `b'` in each branch. This results in two 
cases (or branches, corresponding to the possible values of 
`b`) with two sub-cases each. (corresponding to the possible 
values of `b'`).

Here is the formalisation and proof of `(P ⇒ Q) ⇔ ¬P ∨ Q` 
using Booleans. In the second branch, we close all goals in 
one move. *)

Theorem implb_eq_orb_negb (b b' : bool) : 
    implb b b' = orb (negb b) b'.
Proof.
  destruct b.
  - destruct b'.
    + reflexivity.
    + reflexivity.
  - destruct b'.
    all: reflexivity.
Qed.

(* And here is the formalisation and proof of 
`(P ⇒ Q) ⇔ ¬(P ∧ ¬Q)`. Here, we are *not* nesting the proof: 
we are pattern matching on `b` and `b'` simultaneously, right 
from the start, much like we did for the definition of `andb`, 
for instance. This immediately creates four cases, without any 
sub-cases. It so happens here, that we can close them all by 
reflexivity. *)

Theorem implb_eq_negb_andb_negb {b b' : bool} : 
    implb b b' = negb (andb b (negb b')).
Proof.
  destruct b, b'.
  all: reflexivity.
Qed.

End BooleanValues.
