Inductive Nat : Type :=
  | O
  | S (n : Nat).

Fixpoint soma (n m : Nat) : Nat :=
  match m with
  | O    => n
  | S m' => S(n + m')
  end
where "x + y" := (soma x y) (at level 10, left associativity) : Nat_scope.

Fixpoint mult (n m : Nat) : Nat :=
  match m with
  | O    => O
  | S m' => soma n (mult n m')
  end.

Fixpoint exp (n m : Nat) : Nat :=
  match m with
  | O    => S O
  | S m' => mult n (exp n m')
  end.

Notation "x + y" := (soma x y)
                    (at level 10, left associativity).

Notation "x * y" := (mult x y)
                    (at level 20, left associativity).

Notation "x ^ y" := (exp x y)
                    (at level 30, left associativity).

