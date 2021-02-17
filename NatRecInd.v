From LF Require Export LeisLogica.

Inductive Nat : Type :=
  | O
  | S (n : Nat).

Fixpoint sum (n m : Nat) : Nat :=
  match m with
  | O    => n
  | S m' => S(sum n m')
  end.

Fixpoint mult (n m : Nat) : Nat :=
  match m with
  | O    => O
  | S m' => sum (mult n m') n
  end.

Fixpoint exp (n m : Nat) : Nat :=
  match m with
  | O    => S O
  | S m' => mult (exp n m') n
  end.

Notation "x + y" := (sum x y)
                    (at level 50, left associativity).

Notation "x * y" := (mult x y)
                    (at level 40, left associativity).

Notation "x ^ y" := (exp x y)
                    (at level 30, right associativity).

(** Associatividade da sum **)
Theorem sum_associativity : forall (n m k : Nat), n + (m + k) = (n + m) + k.
Proof.
  intros n m k. induction k as [|k' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. reflexivity.
Qed.


(** Comutatividade da sum **)

Lemma sum_Sn_m : forall (n m : Nat), (S n) + m = n + (S m).
Proof.
  intros n m. induction m as [| m' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. simpl. reflexivity.
Qed.

Theorem sum_commutativity : forall (n m : Nat), n + m = m + n.
Proof.
  intros n m. induction n as [|n' HIn'].
  - simpl. induction m as [|m' HIm'].
    + simpl. reflexivity.
    + simpl. rewrite -> HIm'. reflexivity.
  - rewrite -> (sum_Sn_m n' m). simpl. rewrite -> HIn'. reflexivity.
Qed.


(** Distributividade **)

Theorem distributivity : forall (x y z : Nat), x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  induction z as [| z' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite -> (sum_associativity (x * y) (x * z') x).
    reflexivity.
Qed.


(** Associatividade da multiplicação **)

Theorem mult_associativity : forall (n m k : Nat), (n * m) * k = n * (m * k).
Proof.
  intros n m k. induction k as [| k' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite <- (distributivity n (m * k') m). reflexivity.
Qed.


(** Comutatividade da multiplicação **)

Lemma mult_Sn_m : forall (n m : Nat), (S n) * m = n * m + m.
Proof.
  intros n m. induction m as [|m' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite <- (sum_associativity (n * m') m' n).
    rewrite -> (sum_commutativity m' n).
    rewrite <- (sum_associativity (n * m') n m').
    reflexivity.
Qed.

Theorem mult_commutativity : forall (n m : Nat), n * m = m * n.
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

Theorem mult_identity : forall (n : Nat), n = (S O) * n.
Proof.
  intros n.
  rewrite -> (mult_commutativity (S O) n).
  simpl.
  rewrite -> (sum_commutativity O n).
  simpl.
  reflexivity.
Qed.


(** Lei da exponciação 1 **)

Theorem exp_law_1 : forall (x a b : Nat), x^(a + b) = (x^a) * (x^b).
Proof.
  intros x a b. induction b as [| b' HI].
  - simpl. rewrite -> (sum_commutativity O (x^a)). 
    simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite -> (mult_associativity (x^a) (x^b') x). 
    reflexivity.
Qed.


(** Lei da exponciação 2 **)

Theorem exp_law_2 : forall (a b c : Nat), a^(b * c) = (a^b)^c.
Proof.
  intros a b c. induction c as [| c' HI].
  - simpl. reflexivity.
  - simpl. rewrite <- HI.
    rewrite -> (exp_law_1 a (b * c') b).
    reflexivity.
Qed.


(** Lei da exponciação 3 **)

Theorem exp_law_3 : forall (n : Nat), (S O)^n = S O.
Proof.
  intros n. induction n as [| n' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. simpl. reflexivity.
Qed.


(** Ordem dos naturais **)

Definition lte (n m : Nat) : Prop := exists (k : Nat), n + k = m.
Notation "n <= m" := (lte n m).

Definition lt (n m : Nat) : Prop := (n <= m) /\ (n <> m).
Notation "n < m" := (lt n m).

Definition gte (n m : Nat) : Prop := m <= n.
Notation "n >= m" := (gte n m).

Definition gt (n m : Nat) : Prop := m < n.
Notation "n > m" := (gt n m).

Theorem n_lte_Sm : forall (n m : Nat), n <= (S m) <-> (n <= m) \/ (n = (S m)). 
Proof.
  intros n m. split.
  - intros Hn_lte_Sm. destruct Hn_lte_Sm as (k, Hn_plus_k).
    destruct k as [| k'] eqn:Ek.
    + right. simpl in Hn_plus_k. exact Hn_plus_k.
    + left. simpl in Hn_plus_k. exists k'.
      inversion Hn_plus_k as [Hn_plus_k'].
      reflexivity.
  - intros Hn_leq_m__or__n_eq_Sm.
    destruct Hn_leq_m__or__n_eq_Sm as [Hn_leq_m | Hn_eq_Sm].
    + destruct Hn_leq_m as (k, Hn_plus_k).
      exists (S k). simpl.
      rewrite -> Hn_plus_k.
      reflexivity.
    + exists O. simpl.
      assumption.
Qed.

Theorem lte_reflexity : forall (x : Nat), x <= x.
Proof.
  intros x. exists O. simpl. reflexivity.
Qed.

Lemma succ_lte_O : forall (x : Nat), ~(S x <= O).
Proof.
  intros x HSx_lte_O.
  destruct HSx_lte_O as (k, HSx_plus_k).
  rewrite -> (sum_commutativity (S x) k) in HSx_plus_k.
  simpl in HSx_plus_k. inversion HSx_plus_k.
Qed.

Lemma lte_succ : forall (x y : Nat), S x <= S y -> x <= y.
Proof.
  intros x y HSx_lqe_Sy.
  destruct HSx_lqe_Sy as (k, HSx_plus_k).
  rewrite -> (sum_commutativity (S x) k) in HSx_plus_k.
  simpl in HSx_plus_k.
  inversion HSx_plus_k as [Hk_plus_x].
  rewrite -> (sum_commutativity k x).
  exists k.
  reflexivity.
Qed.

Theorem lte_antisymmetry : forall (x y : Nat), x <= y /\ y <= x -> x = y.
Proof.
  intros x.
  induction x as [| x' HI].
  - intros y HO_lte_y__and__y_lte_O. destruct y as [| y'] eqn:Ey.
    + reflexivity.
    + destruct HO_lte_y__and__y_lte_O as (HO_lte_Sy', HSy'_lte_O).
      apply (succ_lte_O y') in HSy'_lte_O as Hbot.
      contradiction.
  - intros y HSx'_lte_y__and__y_lte_Sx'.
    destruct HSx'_lte_y__and__y_lte_Sx' as (HSx'_lte_y, Hy_lte_Sx').
    destruct y as [| y'] eqn:Ey.
    + apply (succ_lte_O x') in HSx'_lte_y as Hbot.
      contradiction.
    + apply (lte_succ x' y') in HSx'_lte_y as Hx'_lte_y'.
      apply (lte_succ y' x') in Hy_lte_Sx' as Hy'_lte_x'.
      assert (Hx'_leq_y'__and__y'_leq_x': x' <= y' /\ y' <= x').
        { split.
          - exact Hx'_lte_y'.
          - exact Hy'_lte_x'. }
      apply (HI y') in Hx'_leq_y'__and__y'_leq_x' as Hx'_eq_y'.
      rewrite <- Hx'_eq_y'.
      reflexivity.
Qed.

Theorem lte_transitivity : forall (x y z : Nat), x <= y /\ y <= z -> x <= z.
Proof.
  intros x y z Hx_lte_y__and__y_lte_z.
  destruct Hx_lte_y__and__y_lte_z as (Hx_lte_y, Hy_lte_z).
  destruct Hx_lte_y as (a, Hx_sum_a).
  destruct Hy_lte_z as (b, Hy_sum_b).
  rewrite <- Hx_sum_a in Hy_sum_b.
  rewrite <- (sum_associativity x a b) in Hy_sum_b.
  exists (a + b).
  assumption.
Qed.

Lemma O_leq_x : forall (x : Nat), O <= x.
Proof.
  intros x. exists x.
  rewrite -> (sum_commutativity O x).
  simpl. reflexivity.
Qed.

Lemma leq_succ_inverse : forall (x y : Nat), x <= y -> S x <= S y.
Proof.
  intros x y Hx_leq_y.
  destruct Hx_leq_y as (k, Hy_plus_k).
  exists k.
  rewrite -> (sum_commutativity (S x) k). 
  simpl.
  rewrite -> (sum_commutativity k x). 
  rewrite -> Hy_plus_k.
  reflexivity.
Qed.

Theorem lte_total : forall (x y : Nat), x <= y \/ y <= x.
Proof.
  intros x.
  induction x as [| x' HI].
  - intros y. left. exact (O_leq_x y).
  - intros y.
    destruct y as [| y'].
    + right. exact (O_leq_x (S x')).
    + destruct (HI y') as [Hx'_leq_y' | Hy'_leq_x'].
      * left. exact (leq_succ_inverse x' y' Hx'_leq_y').
      * right. exact (leq_succ_inverse y' x' Hy'_leq_x').
Qed.

(** Problema Π4.1 **)

Fixpoint tetracao (n m : Nat) : Nat :=
  match m with
  | O    => S O
  | S m' => n ^ (tetracao n m')
  end.

Notation "n ♢ m" := (tetracao n m) 
                    (at level 20).



