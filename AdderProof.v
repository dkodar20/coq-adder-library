Require Export Adder.
Require Export Unary.
Require Export UnaryBinaryConversions.

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

Lemma nBitAdder_def2 : forall x : bin, nBitAdder (b1 x) (b1 x) (b0 s) = b0 (nBitAdder x x (b1 s)).
Proof.
    Admitted.

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
