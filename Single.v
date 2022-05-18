Inductive bin : Type :=
    | s
    | b0 (n : bin)
    | b1 (n : bin).

Definition and (a: bin) (b: bin) : bin := 
    match a, b with
    | b1 (s), b0 (s) => b0 (s)
    | b0 (s), b1 (s) => b0 (s)
    | b0 (s), b0 (s) => b0 (s)
    | b1 (s), b1 (s) => b1 (s)
    | _, _ => s
    end.

Notation "x * y" := (and x y).

Definition or (a: bin) (b: bin) : bin := 
    match a, b with
    | b1 (s), b0 (s) => b1 (s)
    | b0 (s), b1 (s) => b1 (s)
    | b0 (s), b0 (s) => b0 (s)
    | b1 (s), b1 (s) => b1 (s)
    | _, _ => s
    end.

Notation "x + y" := (or x y).

Definition xor (a: bin) (b: bin) : bin := 
    match a, b with
    | b1 (s), b1 (s) => b0 (s)
    | b0 (s), b1 (s) => b1 (s)
    | b1 (s), b0 (s) => b1 (s)
    | b0 (s), b0 (s) => b0 (s)
    | _, _       => s
    end.

Notation "x ^ y" := (xor x y).

Definition fulladder (a: bin) (b: bin) (c: bin): bin * bin := 
    (a * b + c * (a + b), a ^ b ^ c).

Fixpoint nBitAdder (a : bin) (b : bin) (c :  bin) : bin :=
    match a, b, c with 
    | b0 (s), b1 (s), b0 (s) => b1 (b0 (s))
    | b1 (s), b0 (s), b0 (s) => b1 (b0 (s))
    | b1 (s), b1 (s), b0 (s) => b0 (b1 (s))
    | b0 (s), b0 (s), b0 (s) => b0 (b0 (s))
    | b0 (s), b1 (s), b1 (s) => b0 (b1 (s))
    | b1 (s), b0 (s), b1 (s) => b0 (b1 (s))
    | b1 (s), b1 (s), b1 (s) => b1 (b1 (s))
    | b0 (s), b0 (s), b1 (s) => b1 (b0 (s))
    | b0 (x), b1 (y), b0 (s) => b1 ( nBitAdder x y (b0 (s)))
    | b1 (x), b0 (y), b0 (s) => b1 ( nBitAdder x y (b0 (s)))
    | b1 (x), b1 (y), b0 (s) => b0 ( nBitAdder x y (b1 (s)))
    | b0 (x), b0 (y), b0 (s) => b0 ( nBitAdder x y (b0 (s)))
    | b0 (x), b1 (y), b1 (s) => b0 ( nBitAdder x y (b1 (s)))
    | b1 (x), b0 (y), b1 (s) => b0 ( nBitAdder x y (b1 (s)))
    | b1 (x), b1 (y), b1 (s) => b1 ( nBitAdder x y (b1 (s)))
    | b0 (x), b0 (y), b1 (s) => b1 ( nBitAdder x y (b0 (s)))
    | _, _, _ => s
    end.

Compute (nBitAdder (b1 (b1 (s))) (b1 (b1 (s))) (b0 (s))).

Inductive nat : Type :=
    | u0
    | S (n: nat).

(* Thus 3 will be represented using S (S (S (u0))) *)

Fixpoint add (n: nat) (m: nat) : nat :=
    match n with
    | u0 => m
    | S n' => S (add n' m)
    end.

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

Theorem triv1 : b0 (b0 s) = s.
Proof.
    Admitted.

Lemma incr_nbit : forall x : bin, nBitAdder x x (b1 s) = incr (nBitAdder x x (b0 s)).
Proof.
    Admitted.

Lemma add_expansion_btn : forall x : bin, bin_to_nat (b0 x) = add (bin_to_nat x) (bin_to_nat x).
Proof.
    intros.
    simpl.
    reflexivity.
Qed.

Lemma adder_apply_bin_nat_bin : forall x : bin, add (bin_to_nat x) (bin_to_nat x) = bin_to_nat (nat_to_bin (add (bin_to_nat x) (bin_to_nat x))).
Proof.
    intros.
    simpl.
    rewrite -> nat_bin_nat.
    reflexivity.
Qed.

Lemma one_one_bin_to_nat : forall x y: bin, bin_to_nat x = bin_to_nat y -> x = y.
Proof.
    Admitted.

Lemma add_to_b0_sub : forall x : nat, bin_to_nat (nat_to_bin (add x x)) = bin_to_nat (b0 (nat_to_bin x)).
Proof.
    intros.
    simpl.
    rewrite -> nat_bin_nat.
    rewrite -> nat_bin_nat.
    reflexivity.
Qed.
    
Lemma add_to_b0 : forall x: nat, nat_to_bin (add x x) = b0 (nat_to_bin x).
Proof.
    intros.
    apply one_one_bin_to_nat.
    rewrite -> add_to_b0_sub.
    reflexivity.
Qed.

Lemma nBitAdder_def1 : forall x : bin, nBitAdder (b0 x) (b0 x) (b0 s) = b0 (nBitAdder (x) (x) (b0 s)).
Proof.
    Admitted.

Lemma nBitAdder_def2 : forall x : bin, nBitAdder (b1 x) (b1 x) (b0 s) = b0 (nBitAdder x x (b1 s)).
Proof.
    Admitted.

Lemma add_to_b1 : forall x : bin, bin_to_nat (b1 x) = S (add (bin_to_nat x) (bin_to_nat x)).
Proof.
    intros.
    simpl.
    reflexivity.
Qed.

Lemma one_one_nat_to_bin : forall x y: nat, nat_to_bin x = nat_to_bin y -> x = y.
Proof.
    Admitted.

Lemma  incr_btn_nbit : forall x : bin, S (bin_to_nat (nBitAdder x x (b0 s))) = bin_to_nat ((nBitAdder x x (b1 s))).
Proof.
    intros.
    rewrite -> incr_nbit.
    apply one_one_nat_to_bin.
    simpl.
    rewrite -> bin_nat_bin.
    rewrite -> bin_nat_bin.
    reflexivity.    
Qed.

Theorem adder_equal : forall x: bin, nBitAdder (x) (x) (b0 s) = nat_to_bin (add (bin_to_nat (x)) (bin_to_nat (x))).
Proof.
    intros.
    induction x as [|x'|x'].
    - simpl. reflexivity.
    - rewrite -> add_expansion_btn.
      rewrite -> adder_apply_bin_nat_bin.
      rewrite <- IHx'.
      rewrite -> add_to_b0.
      rewrite -> bin_nat_bin.
      rewrite -> nBitAdder_def1.
      reflexivity.
    - rewrite -> add_to_b1.
      rewrite -> adder_apply_bin_nat_bin.
      rewrite <- IHx'.
      rewrite -> add_to_b0.
      rewrite -> incr_btn_nbit.
      rewrite -> bin_nat_bin.
      rewrite -> nBitAdder_def2.
      reflexivity.
Qed.
