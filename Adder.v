Module RippleCarryAdder.

Inductive bool : Type :=
    | zero
    | one.

Inductive result_datatype : Type := 
    | Some (a : bool) (b: list bool)
    | None.

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition and (a: bool) (b: bool) : bool := 
    match a with
    | one => b
    | zero => zero
    end.

Notation "x * y" := (and x y).

Definition or (a: bool) (b: bool) : bool := 
    match a with
    | one => one
    | zero => b
    end.

Notation "x + y" := (or x y).

Definition xor (a: bool) (b: bool) : bool := 
    match a, b with
    | one, one => zero
    | zero, one => one
    | one, zero => one
    | zero, zero => zero
    end.

Notation "x ^ y" := (xor x y).

Definition eq (a: bool) (b: bool) : Datatypes.bool :=
    match a, b with 
    | zero, zero => true
    | one, one => true
    | zero, one => false
    | one, zero => false
    end.

Notation "x = y" := (eq x y).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Fixpoint verify_eq (a: list bool) (b: list bool) : Datatypes.bool :=
    match a, b with
    | nil, nil => true
    | nil, _ => false
    | _, nil => false
    | x :: xs, y::ys => (x = y) && (verify_eq xs ys) 
    end.

Notation "x = y" := (verify_eq x y).

Fixpoint calc_len (a: list bool) : list bool :=
    match a with 
    | nil => nil
    | x :: xs => one :: (calc_len xs)
    end.

Definition fulladder (a: bool) (b: bool) (c: bool): bool * bool := 
    (a ^ b ^ c, a * b + c * (a + b)).
    (* Sum, CarryOut *)

Definition _first_arg (x:bool * bool) : bool:= 
let (a, b) := x in a.

Definition _second_arg (x:bool * bool) : bool:= 
let (a, b) := x in b.

Definition carryBit (a : result_datatype) :=
    match a with
    | None => zero
    | Some x y => x
    end.

Definition remSum (a : result_datatype) :=
    match a with
    | None => nil
    | Some x y => y
    end.

Fixpoint nBitAdder (a : list bool) (b : list bool) : result_datatype :=
    if (calc_len a) = (calc_len b) then
        match a, b with
        | nil, nil => Some zero nil
        | _, nil => None
        | nil, _ => None
        | x :: xs, y :: ys =>
            let inter := fulladder x y (carryBit (nBitAdder xs ys)) in
                Some (_second_arg inter) (_first_arg inter :: remSum (nBitAdder xs ys))
        end
    else
        None.

Compute (nBitAdder [one, zero, one, one] [one, one, zero, one]).

End RippleCarryAdder.
