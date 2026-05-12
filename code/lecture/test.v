Check nat.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
    intro n.
    induction n as [| n IH].
    - reflexivity.
    - simpl.
    rewrite IH.
    reflexivity.
Qed.
