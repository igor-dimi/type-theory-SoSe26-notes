Inductive Wff {atom : Set} :=
| P : atom -> Wff.

Check @P nat.
Check P 3.
Check 3.
Check P true.

Check P.
Check @P.


(*  *)