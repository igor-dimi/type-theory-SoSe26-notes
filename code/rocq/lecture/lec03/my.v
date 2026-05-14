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









