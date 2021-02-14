Inductive Nat : Type :=
  | O
  | S (n : Nat).

Fixpoint soma (n m : Nat) : Nat :=
  match m with
  | O    => n
  | S m' => S(soma n m')
  end.

Fixpoint mult (n m : Nat) : Nat :=
  match m with
  | O    => O
  | S m' => soma (mult n m') n
  end.

Fixpoint exp (n m : Nat) : Nat :=
  match m with
  | O    => S O
  | S m' => mult (exp n m') n
  end.

Notation "x + y" := (soma x y)
                    (at level 50, left associativity).

Notation "x * y" := (mult x y)
                    (at level 40, left associativity).

Notation "x ^ y" := (exp x y)
                    (at level 30, right associativity).

(** Associatividade da soma **)
Theorem associatividade_soma : forall (n m k : Nat), n + (m + k) = (n + m) + k.
Proof.
  intros n m k. induction k as [|k' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. reflexivity.
Qed.


(** Comutatividade da soma **)

Lemma soma_Sn_m : forall (n m : Nat), (S n) + m = n + (S m).
Proof.
  intros n m. induction m as [| m' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. simpl. reflexivity.
Qed.

Theorem comutatividade_soma : forall (n m : Nat), n + m = m + n.
Proof.
  intros n m. induction n as [|n' HIn'].
  - simpl. induction m as [|m' HIm'].
    + simpl. reflexivity.
    + simpl. rewrite -> HIm'. reflexivity.
  - rewrite -> (soma_Sn_m n' m). simpl. rewrite -> HIn'. reflexivity.
Qed.


(** Distributividade **)

Theorem distributividade : forall (x y z : Nat), x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  induction z as [| z' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite -> (associatividade_soma (x * y) (x * z') x).
    reflexivity.
Qed.  


(** Associatividade da multiplicação **)

Theorem associatividade_multiplicacao : forall (n m k : Nat), (n * m) * k = n * (m * k).
Proof.
  intros n m k. induction k as [| k' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite <- (distributividade n (m * k') m). reflexivity.
Qed.


(** Comutatividade da multiplicação **)

Lemma mult_Sn_m : forall (n m : Nat), (S n) * m = n * m + m.
Proof.
  intros n m. induction m as [|m' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite <- (associatividade_soma (n * m') m' n).
    rewrite -> (comutatividade_soma m' n).
    rewrite <- (associatividade_soma (n * m') n m').
    reflexivity.
Qed.

Theorem comutatividade_multiplicacao : forall (n m : Nat), n * m = m * n.
Proof.
  intros n m.
  induction n as [| n' HIn'].
  - simpl. induction m as [| m' HIm'].
    + simpl. reflexivity.
    + simpl. rewrite -> HIm'. simpl. reflexivity.
  - simpl. rewrite <- HIn'.  
    rewrite <- (mult_Sn_m n' m).
    reflexivity.
Qed.


(** Identidade da multiplicação **)

Theorem identidade_multiplicação : forall (n : Nat), n = (S O) * n.
Proof.
  intros n.
  rewrite -> (comutatividade_multiplicacao (S O) n).
  simpl.
  rewrite -> (comutatividade_soma O n).
  simpl.
  reflexivity.
Qed.


(** Lei da exponciação 1 **)

Theorem lei_exponenciacao_1 : forall (x a b : Nat), x^(a + b) = (x^a) * (x^b).
Proof.
  intros x a b. induction b as [| b' HI].
  - simpl. rewrite -> (comutatividade_soma O (x^a)). 
    simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite -> (associatividade_multiplicacao (x^a) (x^b') x). 
    reflexivity.
Qed.


(** Lei da exponciação 2 **)

Theorem lei_exponenciacao_2 : forall (a b c : Nat), a^(b * c) = (a^b)^c.
Proof.
  intros a b c. induction c as [| c' HI].
  - simpl. reflexivity.
  - simpl. rewrite <- HI.
    rewrite -> (lei_exponenciacao_1 a (b * c') b).
    reflexivity.
Qed.


(** Lei da exponciação 3 **)

Theorem lei_exponenciacao_3 : forall (n : Nat), (S O)^n = S O.
Proof.
  intros n. induction n as [| n' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. simpl. reflexivity.
Qed.





