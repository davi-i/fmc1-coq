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
Notation "n < m" := (gt n m).


Theorem n_lte_Sm : forall (n m : Nat), n <= (S m) <-> (n <= m) \/ (n = (S m)). 
Proof.
  intros n m. split.
  - intros Hn_lte_Sm. destruct Hn_lte_Sm as (k, Hn_plus_k).
    destruct k as [| k'] eqn:Ek.
    + right. simpl in Hn_plus_k. assumption.
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


Theorem lte_antisymmetry : forall (x y : Nat), x <= y /\ y <= x -> x = y.
Proof.
  (** intros x y Hx_leq_y__and__y_leq_x.
  destruct Hx_leq_y__and__y_leq_x as (Hx_leq_y, Hy_leq_x).
  destruct Hx_leq_y as (a, Hx_plus_a).
  destruct Hy_leq_x as (b, Hy_plus_b).
  destruct a as [| a'] eqn:Ea.
  - simpl in Hx_plus_a. assumption.
  - destruct b as [| b'] eqn:Eb.
    + simpl in Hy_plus_b. rewrite -> Hy_plus_b. reflexivity.
    + simpl in Hx_plus_a. simpl in Hy_plus_b. **)

  intros x y Hx_lte_y__and__y_lte_x.
  induction x as [| x' HIx'].
  - destruct Hx_lte_y__and__y_lte_x as (HO_lte_y, Hy_lte_O).
    destruct Hy_lte_O as (k, Hy_plus_k).
    destruct y as [| y'].
    + reflexivity.
    + rewrite -> (sum_commutativity (S y') k) in Hy_plus_k.
      simpl in Hy_plus_k. inversion Hy_plus_k.
  - destruct y as [| y'].
    + destruct Hx_lte_y__and__y_lte_x as (HSx'_lte_O, HO_lte_Sx').
      destruct HSx'_lte_O as (k, HSx'_plus_k).
      rewrite -> (sum_commutativity (S x') k) in HSx'_plus_k.
      simpl in HSx'_plus_k. inversion HSx'_plus_k.
    + destruct Hx_lte_y__and__y_lte_x as (HSx'_lte_Sy', HSy'_lte_Sx').
      destruct (n_lte_Sm (S y') x') as [].
      destruct (H HSy'_lte_Sx') as [HSx'_lte_y' | HSx'_eq_Sy'].
      * destruct HSx'_lte_Sy' as (a, HSx'_plus_a).
        destruct HSy'_lte_Sx' as (b, HSy'_plus_b).












induction x as [| x' HI].
  - intros HO_leq_y__and__y_leq_O.
    destruct HO_leq_y__and__y_leq_O as (HO_leq_y, Hy_leq_O).
    destruct Hy_leq_O as (k, Hy_plus_k).
    destruct k as [| k'].
    + simpl in Hy_plus_k.
      rewrite <- Hy_plus_k. reflexivity.
    + simpl in Hy_plus_k. inversion Hy_plus_k.
  - intros HSx'_leq_y__and__y_leq_Sx'.
    destruct HSx'_leq_y__and__y_leq_Sx' as (HSx'_leq_y, Hy_leq_Sx').
    destruct (n_lte_Sm y x') as [Hy_leq_Sx'__imp__y_leq_x'_or_y_eq_Sx'].
    destruct (Hy_leq_Sx'__imp__y_leq_x'_or_y_eq_Sx' Hy_leq_Sx') as [Hy_leq_x' | Hy_eq_Sx'].
    + destruct Hy_leq_x' as (a, Hx'_plus_a).
      destruct HSx'_leq_y as (b, HSx'_plus_b).
      rewrite <- HSx'_plus_b in Hx'_plus_a.
      rewrite <- (sum_associativity (S x') b a) in Hx'_plus_a.
      assert (HSx'_lte_x': S x' <= x').
        { exists (b + a). assumption. }
      destruct HSx'_lte_x' as (k, Hx'_plus_k).
      destruct k as [| k'] eqn:Ek.
      * 
    + rewrite <- Hy_eq_Sx'. reflexivity. 
    destruct HSx'_leq_y as (a, HSx'_plus_a).
    destruct Hy_leq_Sx' as (b, Hy_plus_b).
    destruct b as [| b'] eqn:Eb.
    + simpl in Hy_plus_b. rewrite -> Hy_plus_b. reflexivity.
    + simpl in Hy_plus_b. (** inversion Hy_plus_b as [Hy_plus_b']. **)
      destruct a as [| a'] eqn:Ea.
      * simpl in HSx'_plus_a. assumption.
      * simpl in HSx'_plus_a. 
    rewrite <- HSx'_plus_a in Hy_plus_b.
  
  destruct Hx_leq_y as (a, Hx_plus_a).
  destruct Hy_leq_x as (b, Hy_plus_b).
  rewrite <- Hx_plus_a.
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

Theorem lte_total_with_lem : lem -> forall (x y : Nat), x <= y \/ y <= x.
Proof.
  intros Hlem x y.
  destruct (Hlem (x <= y)) as [Hx_lte_y | Hn_x_lte_y].
  - left. assumption.
  - 
Abort.

Example exercicio_x4_25 : forall (n : Nat), (n >= S (S (S (S (S O))))) -> ((n ^ S(S O)) < ((S (S O)) ^ n)).




