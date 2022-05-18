Module UnaryOperations.


Inductive nat : Type :=
    | u0
    | S (n: nat).

(* Thus 3 will be represented using S (S (S (u0))) *)

Fixpoint add (n: nat) (m: nat) : nat :=
    match n with
    | u0 => m
    | S n' => S (add n' m)
    end.

End UnaryOperations.