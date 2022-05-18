Require Export Adder.
Require Export Unary.

Fixpoint bin_to_nat (n : bin) : nat := 
    match n with
    | s => u0
    | b0 (x) => add (bin_to_nat x) (bin_to_nat x)
    | b1 (x) => S (add (bin_to_nat x) (bin_to_nat x))
    end.

Fixpoint incr (n : bin) : bin :=
    match n with
    | s => b1 s
    | b0 (n) => b1 (n)
    | b1 (n) => b0 (incr n)
    end.

Fixpoint nat_to_bin (n : nat) : bin :=
    match n with
    | u0 => s 
    | S n => incr (nat_to_bin n)
    end.

Lemma add_dist : forall x y: nat, add x (S y) = S (add x y).
Proof.
    intros.
    induction x as [|x'].
    - simpl. reflexivity.
    - simpl. rewrite <- IHx'. reflexivity. 
Qed.


Lemma bin_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
    intros b.
    induction b as [|b'|b'].
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. rewrite IHb'. simpl.  rewrite -> add_dist. reflexivity.
Qed.

Theorem nat_bin_nat : forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
    intros. induction n as [|n'].
    - simpl. reflexivity.
    -simpl. rewrite -> bin_incr. rewrite -> IHn'. reflexivity.
Qed.

Theorem bin_nat_bin : forall b : bin, nat_to_bin (bin_to_nat b) = b.
Proof.
    Admitted.

