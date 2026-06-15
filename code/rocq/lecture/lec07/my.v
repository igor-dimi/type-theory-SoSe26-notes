(* interpreation of wffs *)


Check Prop.
Check Set.


Inductive Wff {atom : Set} :=
| P     : atom -> Wff
| Neg   : Wff -> Wff
| Conj  : Wff -> Wff -> Wff
| Disj  : Wff -> Wff -> Wff
| Impl  : Wff -> Wff -> Wff
| Equiv : Wff -> Wff -> Wff.

Check @Wff nat.

Check @P.
Check @P nat.

Check P 3.

Check @Conj.
Check @Conj nat.


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




(* Additional notation for boolea operators *)

Notation "! b" := (negb b) 
  (at level 75, right associativity, format "! b").
Notation "b && b'" :=
  (andb b b') (at level 40, left associativity).
Notation "b || b'" :=
  (orb b b') (at level 50, left associativity).
Notation "b -> b'" := 
    (implb b b') (at level 99, right associativity).

Definition eqb : bool -> bool -> bool :=
fun b b' =>
match b, b' with
| true, _   => b'
| false, _  => ! b'
end.

Compute eqb false false.
Compute eqb false true.
Compute eqb true false.
Compute eqb true true.

Notation "b == b'" := 
    (eqb b b') (at level 95, no associativity).

Infix "::" := 
  cons (at level 60, right associativity).

Notation "[ ]" := nil (format "[ ]") : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := 
  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ; '/' y ; '/' .. ; '/' z ']' ]") : list_scope.

Fixpoint eval {atoms : Set} (v : atoms -> bool) (F : Wff) : bool
:= 
match F with
| P i       => v i
| ¬ F       => !(eval v F)
| F ∧ F'    => (eval v F) && (eval v F')
| F ∨ F'    => (eval v F) || (eval v F')
| F ⇒ F'    => (eval v F) -> (eval v F') 
| F ⇔ F'    => (eval v F) == (eval v F')
end.

Compute false -> false.
Compute false -> true.
Compute true -> false.
Compute true -> true.

Check @eval.

Check @eval nat. 

Inductive twoAtoms :=
| A 
| B.

Check twoAtoms.

Check P A.

Check @Wff twoAtoms.

Check A.


