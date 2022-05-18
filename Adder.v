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