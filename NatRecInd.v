Require Import Setoid.

From LF Require Export LeisLogica.

Fixpoint sum (n m : nat) : nat :=
  match m with
  | O    => n
  | S m' => S(sum n m')
  end.

Fixpoint mult (n m : nat) : nat :=
  match m with
  | O    => O
  | S m' => sum (mult n m') n
  end.

Fixpoint exp (n m : nat) : nat :=
  match m with
  | O    => S O
  | S m' => mult (exp n m') n
  end.

Notation "x + y" := (sum x y)
                    (at level 50, left associativity)
                    : nat_scope.

Notation "x * y" := (mult x y)
                    (at level 40, left associativity)
                    : nat_scope.

Notation "x ^ y" := (exp x y)
                    (at level 30, right associativity)
                    : nat_scope.

(** Associatividade da soma **)
Theorem sum_associativity : forall (n m k : nat), n + (m + k) = (n + m) + k.
Proof.
  intros n m k. induction k as [|k' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. reflexivity.
Qed.


(** Comutatividade da soma **)

Lemma sum_Sn_m : forall (n m : nat), (S n) + m = n + (S m).
Proof.
  intros n m. induction m as [| m' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. simpl. reflexivity.
Qed.

Theorem sum_commutativity : forall (n m : nat), n + m = m + n.
Proof.
  intros n m. induction n as [|n' HIn'].
  - simpl. induction m as [|m' HIm'].
    + simpl. reflexivity.
    + simpl. rewrite -> HIm'. reflexivity.
  - rewrite -> (sum_Sn_m n' m). simpl. rewrite -> HIn'. reflexivity.
Qed.

(** Identidade da soma **)
Theorem sum_identity : forall (n : nat), O + n = n.
Proof.
  intros n.
  rewrite -> sum_commutativity.
  simpl. reflexivity.
Qed.


(** Distributividade **)

Theorem distributivity : forall (x y z : nat), x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z.
  induction z as [| z' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite -> (sum_associativity (x * y) (x * z') x).
    reflexivity.
Qed.


(** Associatividade da multiplicação **)

Theorem mult_associativity : forall (n m k : nat), (n * m) * k = n * (m * k).
Proof.
  intros n m k. induction k as [| k' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite <- (distributivity n (m * k') m). reflexivity.
Qed.


(** Comutatividade da multiplicação **)

Lemma mult_Sn_m : forall (n m : nat), (S n) * m = n * m + m.
Proof.
  intros n m. induction m as [|m' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite <- (sum_associativity (n * m') m' n).
    rewrite -> (sum_commutativity m' n).
    rewrite <- (sum_associativity (n * m') n m').
    reflexivity.
Qed.

Theorem mult_commutativity : forall (n m : nat), n * m = m * n.
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

Theorem mult_identity1 : forall (n : nat), n * (S O) = n.
Proof.
  intros n.
  simpl.
  rewrite -> (sum_commutativity O n).
  simpl.
  reflexivity.
Qed.

Theorem mult_identity : forall (n : nat), (S O) * n = n.
Proof.
  intros n.
  rewrite -> (mult_commutativity (S O) n).
  exact (mult_identity1 n).
Qed.


(** Lei da exponciação 1 **)

Theorem exp_law_1 : forall (x a b : nat), x^(a + b) = (x^a) * (x^b).
Proof.
  intros x a b. induction b as [| b' HI].
  - simpl. rewrite -> (sum_commutativity O (x^a)). 
    simpl. reflexivity.
  - simpl. rewrite -> HI.
    rewrite -> (mult_associativity (x^a) (x^b') x). 
    reflexivity.
Qed.


(** Lei da exponciação 2 **)

Theorem exp_law_2 : forall (a b c : nat), a^(b * c) = (a^b)^c.
Proof.
  intros a b c. induction c as [| c' HI].
  - simpl. reflexivity.
  - simpl. rewrite <- HI.
    rewrite -> (exp_law_1 a (b * c') b).
    reflexivity.
Qed.


(** Lei da exponciação 3 **)

Theorem exp_law_3 : forall (n : nat), (S O)^n = S O.
Proof.
  intros n. induction n as [| n' HI].
  - simpl. reflexivity.
  - simpl. rewrite -> HI. simpl. reflexivity.
Qed.

Theorem exp_identity : forall (n : nat), n^(S O) = n.
Proof.
  intros n.
  simpl.
  rewrite -> (mult_identity n).
  reflexivity.
Qed.


(** Ordem dos naturais **)

Definition leq (n m : nat) : Prop := exists (k : nat), n + k = m.
Notation "n <= m" := (leq n m).

Definition lt (n m : nat) : Prop := exists (k : nat), n + S k = m.
Notation "n < m" := (lt n m).

Definition geq (n m : nat) : Prop := m <= n.
Notation "n >= m" := (geq n m).

Definition gt (n m : nat) : Prop := m < n.
Notation "n > m" := (gt n m).

Theorem n_leq_Sm : forall (n m : nat), n <= (S m) -> (n <= m) \/ (n = (S m)).
Proof.
  intros n m Hn_leq_Sm.
  destruct Hn_leq_Sm as (k, Hn_plus_k).
  destruct k as [| k'] eqn:Ek.
  - right. simpl in Hn_plus_k. exact Hn_plus_k.
  - left. simpl in Hn_plus_k. exists k'.
    inversion Hn_plus_k as [Hn_plus_k'].
    reflexivity.
Qed.

Theorem n_leq_Sm_inverse : forall (n m : nat), (n <= m) \/ (n = (S m)) -> n <= (S m).
Proof.
  intros n m Hn_leq_m__or__n_eq_inverse_Sm.
  destruct Hn_leq_m__or__n_eq_inverse_Sm as [Hn_leq_m | Hn_eq_inverse_Sm].
  - destruct Hn_leq_m as (k, Hn_plus_k).
    exists (S k). simpl.
    rewrite -> Hn_plus_k.
    reflexivity.
  - exists O. simpl.
    assumption.
Qed.

Theorem leq_reflexivity : forall (x : nat), x <= x.
Proof.
  intros x. exists O. simpl. reflexivity.
Qed.

Lemma not_succ_leq_O : forall (x : nat), ~(S x <= O).
Proof.
  intros x HSx_leq_O.
  destruct HSx_leq_O as (k, HSx_plus_k).
  rewrite -> (sum_commutativity (S x) k) in HSx_plus_k.
  simpl in HSx_plus_k. inversion HSx_plus_k.
Qed.

Lemma succ_leq_succ : forall (x y : nat), S x <= S y -> x <= y.
Proof.
  intros x y HSx_lqe_Sy.
  destruct HSx_lqe_Sy as (k, HSx_plus_k).
  exists k.
  rewrite -> (sum_commutativity x k).
  rewrite -> (sum_commutativity (S x) k) in HSx_plus_k.
  simpl in HSx_plus_k.
  inversion HSx_plus_k as [Hk_plus_x].
  reflexivity.
Qed.

Theorem leq_antisymmetry : forall (x y : nat), x <= y /\ y <= x -> x = y.
Proof.
  intros x.
  induction x as [| x' HI ].
  - intros y HO_leq_y__and__y_leq_O. destruct y as [| y'] eqn:Ey.
    + reflexivity.
    + destruct HO_leq_y__and__y_leq_O as (HO_leq_Sy', HSy'_leq_O).
      apply (not_succ_leq_O y') in HSy'_leq_O as Hbot.
      contradiction.
  - intros y HSx'_leq_y__and__y_leq_Sx'.
    destruct HSx'_leq_y__and__y_leq_Sx' as (HSx'_leq_y, Hy_leq_Sx').
    destruct y as [| y'] eqn:Ey.
    + apply (not_succ_leq_O x') in HSx'_leq_y as Hbot.
      contradiction.
    + apply (succ_leq_succ x' y') in HSx'_leq_y as Hx'_leq_y'.
      apply (succ_leq_succ y' x') in Hy_leq_Sx' as Hy'_leq_x'.
      assert (Hx'_leq_y'__and__y'_leq_x': x' <= y' /\ y' <= x').
        { split.
          - exact Hx'_leq_y'.
          - exact Hy'_leq_x'. }
      apply (HI y') in Hx'_leq_y'__and__y'_leq_x' as Hx'_eq_inverse_y'.
      rewrite <- Hx'_eq_inverse_y'.
      reflexivity.
Qed.

Theorem leq_transitivity : forall (x y z : nat), x <= y /\ y <= z -> x <= z.
Proof.
  intros x y z Hx_leq_y__and__y_leq_z.
  destruct Hx_leq_y__and__y_leq_z as (Hx_leq_y, Hy_leq_z).
  destruct Hx_leq_y as (a, Hx_sum_a).
  destruct Hy_leq_z as (b, Hy_sum_b).
  exists (a + b).
  rewrite -> (sum_associativity x a b).
  rewrite -> Hx_sum_a.
  exact Hy_sum_b.
Qed.

Lemma O_leq_x : forall (x : nat), O <= x.
Proof.
  intros x. exists x.
  rewrite -> (sum_commutativity O x).
  simpl. reflexivity.
Qed.

Lemma succ_leq_succ_inverse : forall (x y : nat), x <= y -> S x <= S y.
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

Theorem leq_total : forall (x y : nat), x <= y \/ y <= x.
Proof.
  intros x.
  induction x as [| x' HI].
  - intros y. left. exact (O_leq_x y).
  - intros y.
    destruct y as [| y'].
    + right. exact (O_leq_x (S x')).
    + destruct (HI y') as [Hx'_leq_y' | Hy'_leq_x'].
      * left. exact (succ_leq_succ_inverse x' y' Hx'_leq_y').
      * right. exact (succ_leq_succ_inverse y' x' Hy'_leq_x').
Qed.

Lemma x_plus_Sy : forall (x y : nat), x + S y <> x.
Proof.
  intros x y.
  induction x as [| x' HI].
  - simpl. discriminate.
  - intros HSx'_plus_Sy.
    rewrite -> (sum_commutativity (S x') (S y)) in HSx'_plus_Sy.
    simpl in HSx'_plus_Sy.
    inversion HSx'_plus_Sy as [HSy_plus_x'].
    rewrite -> (sum_commutativity (S y) x') in HSy_plus_x'.
    apply HI in HSy_plus_x' as Hbot.
    exact Hbot.
Qed.

Theorem lt_or_eq : forall (x y : nat), x <= y -> x < y \/ x = y.
Proof.
  intros x y Hx_leq_y.
  destruct Hx_leq_y as (k, Hx_plus_k).
  destruct k as [| k'] eqn:Ek.
  - right.
    rewrite <- Hx_plus_k.
    simpl. reflexivity.
  - left. exists k'.
    exact Hx_plus_k.
Qed.

Theorem gt_or_eq : forall (x y : nat), x >= y -> x > y \/ x = y.
Proof.
  intros x y Hx_geq_y.
  apply (lt_or_eq y x) in Hx_geq_y as Hy_lt_x__or__y_eq_x.
  destruct Hy_lt_x__or__y_eq_x as [Hy_lt_x | Hy_eq_x].
  - left. exact Hy_lt_x.
  - right. rewrite <- Hy_eq_x. reflexivity.
Qed.

Theorem leq_or_gt : forall (x y : nat), x <= y \/ x > y.
Proof.
  intros x y.
  destruct (leq_total x y) as [Hx_leq_y | Hy_leq_x].
  - left. exact Hx_leq_y.
  - destruct (lt_or_eq y x Hy_leq_x) as [Hy_lt_x | Hy_eq_x].
    + right. exact Hy_lt_x.
    + left. rewrite <- Hy_eq_x.
      exact (leq_reflexivity y).
Qed.

Theorem geq_or_lt : forall (x y : nat), x >= y \/ x < y.
Proof.
  intros x y.
  exact (leq_or_gt y x).
Qed.

Theorem neg_leq : forall (x y : nat), ~(x <= y) -> x > y.
Proof.
  intros x y Hn_x_leq_y.
  destruct (leq_or_gt x y) as [Hx_leq_y | Hx_gt_y].
  - apply Hn_x_leq_y in Hx_leq_y as Hbot.
    contradiction.
  - exact Hx_gt_y.
Qed.

Theorem neg_geq : forall (x y : nat), ~(x >= y) -> x < y.
Proof.
  intros x y.
  exact (neg_leq y x).
Qed.

Theorem neg_leq_inverse : forall (x y : nat), x > y -> ~(x <= y).
Proof.
  intros x y Hx_gt_y Hx_leq_y.
  destruct Hx_gt_y as (a, Hy_Sa_eq_x).
  destruct Hx_leq_y as (b, Hx_b_eq_y).
  rewrite <- Hx_b_eq_y in Hy_Sa_eq_x.
  rewrite <- sum_associativity in Hy_Sa_eq_x.
  replace (b + S a) with (S(b + a)) in Hy_Sa_eq_x by reflexivity.
  apply x_plus_Sy in Hy_Sa_eq_x as Hbot.
  exact Hbot.
Qed.

Theorem neg_geq_inverse : forall (x y : nat),  x < y -> ~(x >= y).
Proof.
  intros x y.
  exact (neg_leq_inverse y x).
Qed.

Theorem neg_lt : forall (x y : nat), ~(x < y) -> x >= y.
Proof.
  intros x y Hn_x_lt_y.
  destruct (leq_total x y) as [Hx_leq_y | Hy_leq_x].
  - destruct Hx_leq_y as (k, Hx_plus_k).
    destruct k as [| k'].
    + exists 0.
      rewrite <- Hx_plus_k.
      simpl.
      reflexivity.
    + assert (Hbot : False).
        { apply Hn_x_lt_y.
          exists k'.
          exact Hx_plus_k. }
      contradiction.
  - exact Hy_leq_x.
Qed.

Theorem neg_gt : forall (x y : nat), ~(x > y) -> x <= y.
Proof.
  intros x y.
  exact (neg_lt y x).
Qed.

Theorem neg_lt_inverse : forall (x y : nat), x >= y -> ~(x < y).
Proof.
  intros x y Hx_geq_y Hx_lt_y.
  destruct Hx_lt_y as (a, Hx_Sa_eq_y).
  destruct Hx_geq_y as (b, Hy_b_eq_x).
  rewrite <- Hy_b_eq_x in Hx_Sa_eq_y.
  rewrite <- sum_associativity in Hx_Sa_eq_y.
  replace (b + S a) with (S(b + a)) in Hx_Sa_eq_y by reflexivity.
  apply x_plus_Sy in Hx_Sa_eq_y as Hbot.
  exact Hbot.
Qed.

Theorem neg_gt_inverse : forall (x y : nat),  x <= y -> ~(x > y).
Proof.
  intros x y.
  exact (neg_lt_inverse y x).
Qed.

Theorem succ_eq_sum1 : forall (n : nat), S n = n + 1.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem not_reflexivity_lt : forall (n : nat), ~(n < n).
Proof.
  intros n Hn_lt_n.
  destruct Hn_lt_n as (k, Hn_plus_Sk).
  apply (x_plus_Sy n k) in Hn_plus_Sk as Hbot.
  exact Hbot.
Qed.

Theorem not_reflexivity_gt : forall (n : nat), ~(n > n).
Proof.
  exact not_reflexivity_lt.
Qed.

Theorem lt_transitivity : forall (x y z : nat), x < y /\ y < z -> x < z.
Proof.
  intros x y z Hand.
  destruct Hand as (Hx_lt_y, Hy_lt_z).
  destruct Hx_lt_y as (a, Hx_sum_Sa).
  destruct Hy_lt_z as (b, Hy_sum_Sb).
  exists (S a + b).
  replace (S(S a + b)) with (S a + S b) by reflexivity.
  rewrite -> sum_associativity.
  rewrite -> Hx_sum_Sa.
  rewrite -> Hy_sum_Sb.
  reflexivity.
Qed.

Theorem not_lt_0 : forall (n : nat), ~(n < 0).
Proof.
  intros n Hn_lt_0.
  destruct Hn_lt_0 as (k, Hn_plus_Sk).
  simpl in Hn_plus_Sk.
  discriminate.
Qed.

Theorem leq_0_implies_eq_0 : forall (x: nat), x <= 0 -> x = 0.
Proof.
  intros x Hx_leq_0.
  destruct (lt_or_eq x 0 Hx_leq_0) as [Hx_lt_0 | Hx_eq_0].
  - apply (not_lt_0 x) in Hx_lt_0 as Hbot. contradiction.
  - exact Hx_eq_0.
Qed.

Theorem leq_succ : forall (n : nat), n <= S n.
Proof.
  exists 1.
  exact (succ_eq_sum1 n).
Qed.

Theorem lt_succ : forall (n : nat), n < (S n).
Proof.
  intros n.
  exists 0.
  simpl.
  reflexivity.
Qed.

Theorem lt_implies_leq : forall (n m : nat), n < m -> n <= m.
Proof.
  intros n m Hn_lt_m.
  destruct Hn_lt_m as (k, Hn_plus_Sk).
  exists (S k).
  exact Hn_plus_Sk.
Qed.

(* Theorem n_lt_Sm : forall (n m : nat), n <= m -> n < S m.
Proof.
  intros n m Hn_leq_m HSm_leq_n.
  apply (lt_succ m).
  apply (leq_transitivity (S m) n m).
  split; assumption.
Qed. *)

Theorem n_lt_Sm: forall (n m : nat), n < S m -> n <= m.
Proof.
  intros n m Hn_lt_Sm.
  destruct Hn_lt_Sm as (k, Hn_plus_Sk).
  simpl in Hn_plus_Sk.
  inversion Hn_plus_Sk as [Hn_plus_k].
  exists k.
  reflexivity.
Qed.

Theorem lt_implies_succ_leq : forall (n m : nat), n < m -> S n <= m.
Proof.
  intros n m Hn_lt_m.
  destruct Hn_lt_m as (k, Hn_plus_Sk).
  exists k.
  rewrite <- Hn_plus_Sk.
  rewrite -> sum_commutativity.
  simpl.
  rewrite -> sum_commutativity.
  reflexivity.
Qed.

Theorem gt_implies_geq_succ : forall (n m : nat), n > m -> n >= S m.
Proof.
  intros n m.
  exact (lt_implies_succ_leq m n).
Qed.

Theorem sum_eq_0 : forall (a b : nat), a + b = 0 -> a = 0 /\ b = 0.
Proof.
  intros a b Ha_plus_b.
  destruct b as [| b'].
  - split.
    + simpl in Ha_plus_b.
      exact Ha_plus_b.
    + reflexivity.
  - simpl in Ha_plus_b.
    discriminate.
Qed.

Theorem mult_eq_0 : forall (a b : nat), a * b = 0 -> a = 0 \/ b = 0.
Proof.
  intros a b Hab_eq_0.
  destruct b as [| b'].
  - right. reflexivity.
  - left. simpl in Hab_eq_0.
    destruct (sum_eq_0 _ _ Hab_eq_0) as (Hab'_eq_0, Ha_eq_0).
    exact Ha_eq_0.
Qed.

Theorem exp_eq_0 : forall (a b : nat), a^b = 0 -> a = 0.
Proof.
  intros a b Ha_exp_b.
  induction b as [| b' HI].
  - simpl in Ha_exp_b.
    discriminate.
  - simpl in Ha_exp_b.
    destruct (mult_eq_0 _ _ Ha_exp_b) as [Ha_exp_b' | Ha_eq_0];
    try apply HI in Ha_exp_b' as Ha_eq_0;
    exact Ha_eq_0.
Qed.

Theorem sum_eq : forall (a b k : nat), a = b -> k + a = k + b.
Proof.
  intros a b k Ha_eq_inverse_b.
  rewrite -> Ha_eq_inverse_b.
  reflexivity.
Qed.

Theorem sum_eq_inverse : forall (a b k : nat), k + a = k + b -> a = b.
Proof.
  intros a b. induction k as [| k' HI].
  - intro H0_plus_a.
    repeat rewrite -> sum_identity in H0_plus_a.
    exact H0_plus_a.
  - intro HSk'_plus_a.
    repeat rewrite -> (sum_commutativity (S k') _) in HSk'_plus_a.
    simpl in HSk'_plus_a.
    inversion HSk'_plus_a as [Ha_plus_k'].
    repeat rewrite -> (sum_commutativity _ k') in Ha_plus_k'.
    apply HI in Ha_plus_k' as Ha_eq_inverse_b.
    exact Ha_eq_inverse_b.
Qed.

Theorem sum_leq : forall (a b k : nat), a <= b -> k + a <= k + b.
Proof.
  intros a b k Ha_leq_b.
  destruct Ha_leq_b as (c, Ha_plus_c).
  exists c.
  rewrite <- sum_associativity.
  exact (sum_eq _ _ _ Ha_plus_c).
Qed.

Theorem sum_leq_inverse : forall (a b k : nat), k + a <= k + b -> a <= b.
Proof.
  intros a b k Hk_a_leq_k_b.
  destruct Hk_a_leq_k_b as (c, Hk_a_c).
  exists c.
  rewrite <- sum_associativity in Hk_a_c.
  exact (sum_eq_inverse _ _ _ Hk_a_c).
Qed.

Theorem sum_geq : forall (a b k : nat), a >= b -> k + a >= k + b.
Proof.
  intros a b k.
  exact (sum_leq b a k).
Qed.

Theorem sum_geq_inverse : forall (a b k : nat), k + a >= k + b -> a >= b.
Proof.
  intros a b k.
  exact (sum_leq_inverse b a k).
Qed.

Theorem sum_lt : forall (a b k : nat), a < b -> k + a < k + b.
Proof.
  intros a b k Ha_lt_b.
  destruct Ha_lt_b as (c, Ha_Sc).
  exists c.
  rewrite <- sum_associativity.
  rewrite -> Ha_Sc.
  reflexivity.
Qed.

Theorem sum_lt_inverse : forall (a b k : nat), k + a < k + b -> a < b.
Proof.
  intros a b k Ha_lt_b.
  destruct Ha_lt_b as (c, Hk_a_Sc).
  exists c.
  rewrite <- sum_associativity in Hk_a_Sc.
  exact (sum_eq_inverse _ _ _ Hk_a_Sc).
Qed.

Theorem sum_gt : forall (a b k : nat), a > b -> k + a > k + b.
Proof.
  intros a b k.
  exact (sum_lt b a k).
Qed.

Theorem sum_gt_inverse : forall (a b k : nat), k + a > k + b -> a > b.
Proof.
  intros a b k.
  exact (sum_lt_inverse b a k).
Qed.

Theorem mult_eq : forall (a b k : nat), a = b -> k * a = k * b.
Proof.
  intros a b k Ha_eq_inverse_b.
  rewrite -> Ha_eq_inverse_b.
  reflexivity.
Qed.

Theorem mult_eq_inverse : forall (a b k : nat), (S k) * a = (S k) * b -> a = b.
Proof.
  induction a as [| a' HI].
  - intros b k HSk0_eq_inverse_Skb.
    simpl in HSk0_eq_inverse_Skb.
    destruct b as [| b'].
    + reflexivity.
    + simpl in HSk0_eq_inverse_Skb.
      discriminate.
  - intros b k HSkSa'_eq_inverse_Skb.
    destruct b as [| b'].
    + simpl in HSkSa'_eq_inverse_Skb.
      discriminate.
    + simpl in HSkSa'_eq_inverse_Skb.
      inversion HSkSa'_eq_inverse_Skb as [HSka'_plus_k].
      repeat rewrite -> (sum_commutativity _ k) in HSka'_plus_k.
      apply sum_eq_inverse in HSka'_plus_k as HSka'_eq_inverse_Skb'.
      apply HI in HSka'_eq_inverse_Skb' as Ha'_eq_inverse_b.
      rewrite -> Ha'_eq_inverse_b.
      reflexivity.
Qed.

Theorem exp_eq : forall (a b k : nat), a = b -> a^k = b^k.
Proof.
  intros a b k Ha_eq_inverse_b.
  rewrite -> Ha_eq_inverse_b.
  reflexivity.
Qed.

Theorem exp_eq_inverse : forall (a b k : nat), a^(S k) = b^(S k) -> a = b.
Proof.
  intro a. induction b as [| b'].
  - intros k Ha_exp_Sk.
    replace (0 ^ S k) with 0 in Ha_exp_Sk by reflexivity.
    apply exp_eq_0 in Ha_exp_Sk as Ha_eq_0.
    exact Ha_eq_0.
  - intros k Ha_exp_Sk.
    destruct a as [| a'].
    + replace (0 ^ S k) with 0 in Ha_exp_Sk by reflexivity.
      symmetry in Ha_exp_Sk.
      apply exp_eq_0 in Ha_exp_Sk as HSb'_eq_0.
      symmetry.
      exact HSb'_eq_0.
    + destruct k as [| k'].
      * repeat rewrite -> exp_identity in Ha_exp_Sk.
        exact Ha_exp_Sk.
      * 
    simpl in Ha_exp_Sk.
Abort.

(** Somátório e produtório **)

Fixpoint leq_bool (n m : nat) : bool :=
match n, m with
| O, _       => true
| S _, O     => false
| S n', S m' => (leq_bool n' m')
end.

Notation "n <=? m" := (leq_bool n m) (at level 50).

Fixpoint summation (n : nat) (m : nat) (f : nat -> nat) : nat :=
match n, m with
| O,  O    => f (O)
| O,  S m' => O
| S n', _  => if (m <=? n)
              then (f n) + (summation n' m f)
              else 0
end.

Notation "∑( m 'to' n )[ i |-> f  ]" := (summation n m (fun i : nat => f)).
Notation "∑( n )[ i |-> f  ]" := (summation n 1 (fun i : nat => f)).

Compute ∑(0 to 3)[a |-> a^2 + 1].

Theorem square_of_sum : forall (a b : nat), (a + b)^2 = a^2 + 2 * (a * b) + b^2.
Proof.
  intros a b.
  rewrite -> mult_commutativity.
  replace (a * b * 2) with (0 + a * b + a * b) by reflexivity.
  replace (a^2) with (1 * a * a) by reflexivity.
  replace (b^2) with (1 * b * b) by reflexivity.
  rewrite -> sum_identity.
  repeat rewrite -> mult_identity.
  rewrite -> (mult_commutativity a b) at 2.
  rewrite <- sum_associativity.
  rewrite <- sum_associativity.
  rewrite -> sum_associativity.
  repeat rewrite <- distributivity.
  repeat rewrite -> (mult_commutativity _ (a + b)).
  rewrite <- distributivity.
  simpl.
  rewrite -> mult_identity.
  reflexivity.
Qed.

Theorem cube_of_sum : forall (a b : nat), (a + b)^3 = a^3 + 3 * (a^2 * b) + 3 * (a * b^2) + b^3.
Proof.
  intros a b.
  repeat rewrite -> (mult_commutativity 3 _).
  replace (a^2 * b * 3) with (a^2 * b * 2 + a^2 * b) by reflexivity.
  replace (a * b^2 * 3) with (a * b^2 * 2 + a * b^2) by reflexivity.
  replace (a^2) with (1 * a * a) at 1 by reflexivity.
  replace (b^2) with (1 * b * b) at 1 by reflexivity.
  repeat rewrite -> mult_identity.
  rewrite -> (mult_associativity a a b) at 1.
  rewrite -> (mult_commutativity (a^2) b).
  rewrite <- (mult_associativity a b b) at 1.
  rewrite -> (mult_commutativity (a * b) b).
  repeat rewrite -> (mult_associativity _ (_ * _) 2).
  repeat rewrite -> (mult_commutativity _ 2).
  rewrite -> (sum_commutativity (b * _) _ ).
  rewrite -> (sum_associativity (a^3) _ _).
  rewrite <- (sum_associativity (a^3 + _) _ _).
  rewrite -> (sum_associativity (b * _) _ _).
  rewrite -> (sum_commutativity (b * _) _ ).
  rewrite <- (sum_associativity (a * _) _ _).
  rewrite -> (sum_associativity (a^3 + _) _ _).
  rewrite <- (sum_associativity _ _ (b^3)).
  replace (a^3) with (a^2 * a) by reflexivity.
  replace (b^3) with (b^2 * b) by reflexivity.
  repeat rewrite -> (mult_commutativity (_^2) _).
  repeat rewrite <- distributivity.
  repeat rewrite <- square_of_sum.
  repeat rewrite -> (mult_commutativity _ (_^2)).
  rewrite <- distributivity.
  reflexivity.
Qed.

Example x4_26 :
  forall (n : nat), (∑(n)[i |-> 4 * i^3]) = n^2 * (n + 1)^2.
Proof.
  intros n. induction n as [| n' HI].
  - simpl. reflexivity.
  - replace (∑(_)[i |-> _]) with (4 * S n'^3 + ∑(n')[i |-> 4 * i^3]) by reflexivity.
    rewrite -> HI.
    replace (n' + 1) with (S n') by reflexivity.
    rewrite -> mult_commutativity.
    replace (S n' ^ 3) with (S n' ^2 * S n') by reflexivity.
    rewrite -> (mult_commutativity _ (S n' ^ 2)).
    rewrite -> mult_associativity.
    rewrite <- distributivity.
    apply mult_eq.
    replace (S n' * 4) with ((n' + 1) * 4) by reflexivity.
    rewrite -> mult_commutativity.
    rewrite -> distributivity.
    rewrite -> (sum_commutativity (4 * n') _).
    replace (4 * 1) with (2^2) by reflexivity.
    replace (4 * n') with ((2 * 2) * n') by reflexivity.
    rewrite -> mult_associativity.
    rewrite <- square_of_sum.
    rewrite -> sum_commutativity.
    apply exp_eq.
    simpl.
    reflexivity.
Qed.

Theorem distributivity_summation :
  forall (n m : nat) (f : nat -> nat), ∑(n)[i |-> m * (f i)] = m * ∑(n)[i |-> (f i)].
Proof.
  intros n. induction n as [| n' HI].
  - intros m f. simpl. reflexivity.
  - intros m f.
    replace (∑(_)[i |-> _]) with (m * (f (S n')) + ∑(n')[i |-> m * f i]) by reflexivity.
    replace (∑(S n')[i |-> _]) with ((f (S n')) + ∑(n')[i |-> f i]) by reflexivity.
    rewrite -> (HI m f).
    rewrite -> distributivity.
    reflexivity.
Qed.

Example x4_29 :  forall (n : nat), 6 * ∑(n)[i |-> i^2] = 2 * n^3 + 3 * n^2 + n.
Proof.
  induction n as [| n' HI].
  - simpl. reflexivity.
  - replace (∑(_)[i |-> _]) with ((S n' ^ 2) + ∑(n')[i |-> i^2]) by reflexivity.
    rewrite -> distributivity.
    rewrite -> HI.
    rewrite -> (succ_eq_sum1 n') at 1.
    rewrite -> square_of_sum.
    repeat rewrite -> distributivity.
    rewrite -> exp_law_3.
    repeat rewrite -> mult_identity1.
    rewrite <- (mult_associativity 6 _ _).
    rewrite -> (mult_commutativity _ n').
    replace (6 * 2) with (2*3 + 3*2) by reflexivity.
    replace 6 with (2 + 3 + 1) at 2 by reflexivity.
    rewrite -> distributivity.
    rewrite <- (sum_associativity _ (2 + 3 + 1) (_ + _ + _)).
    rewrite <- (sum_associativity _ 1 (_ + _ + _)).
    rewrite -> (sum_commutativity 1 _).
    rewrite <- (sum_associativity _ _ 1).
    rewrite -> (sum_associativity _ _ (_ + 1)).
    rewrite <- (sum_associativity 2 _ _).
    rewrite -> (sum_commutativity 3 _).
    rewrite -> (sum_associativity 2 _ _).
    rewrite -> (sum_associativity 2 _ _).
    rewrite -> (sum_commutativity 2 _).
    rewrite -> (sum_associativity _ _ (n' + 1)).
    rewrite -> (sum_associativity _ _ 3).
    rewrite -> (sum_associativity _ _ (n' * _)).
    rewrite <- (sum_associativity _ (n' * _) _).
    rewrite -> (sum_associativity (n' * _) _ _).
    rewrite -> (sum_commutativity (n' * _) _).
    rewrite <- (sum_associativity _ (n' * _) (3 * n'^2)).
    rewrite -> (sum_commutativity (n' * _) _).
    rewrite -> (sum_associativity _ _ (_ + n' * _)).
    rewrite -> (sum_associativity _ _ 2).
    rewrite -> (sum_commutativity _ (2 * n'^3)).
    rewrite <- (sum_associativity _ _ 3).
    rewrite -> (sum_associativity _ _ (n' * _)).
    repeat rewrite -> (mult_commutativity n' _).
    repeat rewrite -> (mult_associativity _ _ n').
    replace 6 with (2 * 3) by reflexivity.
    repeat rewrite -> (mult_associativity _ _ (n'^2)).
    replace 2 with (2 * 1) at 8 by reflexivity.
    replace 3 with (3 * 1) at 6 by reflexivity.
    repeat rewrite <- distributivity.
    rewrite <- (mult_identity1 (n' ^ 2)) at 1.
    rewrite <- (mult_identity1 (n')) at 3 5.
    replace (n' * 1) with (n' * 1^2) at 1 by reflexivity.
    rewrite <- cube_of_sum.
    rewrite <- square_of_sum.
    rewrite <- succ_eq_sum1.
    reflexivity.
Qed.

Example x4_30 : forall (n : nat), ∑(n)[i |-> i^3] = (∑(n)[i |-> i])^2.
Proof.
  induction n as [| n' HI].
  - simpl. reflexivity.
  - (* unfold summation. fold summation.
    rewrite -> HI.
    rewrite -> square_of_sum.
    replace (S n' ^ 2 + 2 * (S n' * _)) with (S n' ^ 3).
      { reflexivity. } *)
Abort.

Theorem indution_starting_in :
  forall (b : nat) (phi : nat -> Prop),
    (phi b) /\ (forall k : nat, k >= b -> ((phi k) -> (phi (S k))))
    -> forall (n : nat), (n >= b -> (phi n)).
Proof.
  intros b phi Hind.
  destruct Hind as (Hbase, Hstep).
  induction n as [| n' HI].
  - intros H0_geq_b.
    assert (Hb_eq_0: b = 0).
      { apply (leq_antisymmetry b 0). split.
        - exact H0_geq_b.
        - exact (O_leq_x b). }
    rewrite <- Hb_eq_0.
    exact Hbase.
  - intros HSn'_geq_b.
    destruct (n_leq_Sm b n' HSn'_geq_b) as [Hb_leq_n' | Hb_eq_inverse_Sn'].
    + apply HI in Hb_leq_n' as Hpn'.
      apply (Hstep n' Hb_leq_n') in Hpn' as HpSn'.
      exact HpSn'.
    + rewrite <- Hb_eq_inverse_Sn'.
      exact Hbase.
Qed.

Theorem induction_two_bases : forall (phi : nat -> Prop),
  ((phi 0) /\ (phi 1)) /\ (forall (k : nat), (phi k) /\ (phi (S k)) -> (phi (S(S k))))
  -> forall (n : nat), (phi n).
Proof.
  intros phi Hind.
  destruct Hind as (Hbase, Hstep).
  assert (Hpn_and_pSn: forall n : nat, (phi n) /\ (phi (S n))).
    { induction n as [| n' HI].
      - exact Hbase.
      - apply (Hstep n') in HI as HpSSn'.
        destruct HI as (Hpn', HpSn').
        split.
        + exact HpSn'.
        + exact HpSSn'. }
  intros n.
  destruct (Hpn_and_pSn n) as (Hpn, HpSn).
  exact Hpn.
Qed.

Theorem induction_three_bases : forall (phi : nat -> Prop),
  ((phi 0) /\ (phi 1) /\ (phi 2)) /\ (forall (k : nat), (phi k) /\ (phi (S k)) /\ (phi (S(S k))) -> (phi (S(S(S k)))))
  -> forall (n : nat), (phi n).
Proof.
  intros phi Hind.
  destruct Hind as (Hbase, Hstep).
  assert (HphinSnSSn: forall n : nat, (phi n) /\ (phi (S n) /\ (phi (S(S n))))).
    { induction n as [| n' HI].
      - exact Hbase.
      - apply (Hstep n') in HI as HpSSSn'.
        destruct HI as (Hpn', H).
        destruct H as (HpSn', HpSSn').
        repeat split; assumption || split. }
  intros n.
  destruct (HphinSnSSn n) as (Hpn, HpSnSSn).
  exact Hpn.
Qed.

Theorem induction_three_bases_startin_in : forall (b : nat) (phi : nat -> Prop),
  ((phi b) /\ (phi (S b)) /\ (phi (S(S b)))) /\
  (forall (k : nat), (k >= b) -> (phi k) /\ (phi (S k)) /\ (phi (S(S k))) -> (phi (S(S(S k)))))
  -> forall (n : nat), n >= b -> (phi n).
Proof.
  intros b phi Hind.
  destruct Hind as (Hbase, Hstep).
  assert (Hphi: forall n : nat, n >= b -> (phi n) /\ (phi (S n) /\ (phi (S(S n))))).
    { apply (indution_starting_in b). split.
      - exact Hbase.
      - intros k Hk_geq_b HI.
        apply (Hstep k Hk_geq_b) in HI as HpSSSSk.
        destruct HI as (Hpk, H).
        destruct H as (HpSk, HpSSk).
        repeat split; assumption || split. }
  intros n Hn_geq_b.
  destruct (Hphi n Hn_geq_b) as (Hpn, H).
  exact Hpn.
Qed.

Lemma succ_eq : forall (n m : nat), n = m -> S n = S m.
Proof.
  intros n m Hn_eq_m.
  rewrite -> Hn_eq_m.
  reflexivity.
Qed.

Example x4_31 : forall (n : nat), n >= 8 -> exists (a b : nat), n = 3 * a + 5 * b.
Proof.
  apply (induction_three_bases_startin_in 8).
  split.
  - split.
    + exists 1. exists 1.
    simpl. reflexivity.
    + split.
      * exists 3. exists 0.
        simpl. reflexivity.
      * exists 0. exists 2.
        simpl. reflexivity.
  - intros k Hk_gte_8 HI.
    repeat destruct HI as (HI1, HI).
    destruct HI1 as (a', Ha').
    destruct Ha' as (b', Hab').
    exists (S a'). exists b'.
    replace (3 * S a') with (3 * a' + 3) by reflexivity.
    rewrite <- sum_associativity.
    rewrite -> (sum_commutativity 3 _).
    rewrite -> sum_associativity.
    rewrite <- Hab'.
    simpl.
    reflexivity.
Qed.

Module x4_32.
  Definition phi (n : nat) := 8 * ∑(n)[i |-> i] = (2 * n + 1)^2.

  Theorem x4_32i : forall (n : nat), (phi n) -> (phi (S n)).
  Proof.
    intros n.
    unfold phi.
    intros Hpn.
    replace (∑(_)[i |-> _]) with (S n + ∑(n)[i |-> i]) by reflexivity.
    rewrite -> distributivity.
    rewrite -> Hpn.
    replace (2 * S n + 1) with (2 * n + 1 + 2) by reflexivity.
    rewrite -> (square_of_sum (2 * n + 1) 2).
    rewrite -> sum_commutativity.
    rewrite <- sum_associativity.
    apply sum_eq.
    repeat rewrite -> (mult_commutativity 2 _).
    rewrite -> mult_associativity.
    replace (2^2) with (4 * 1) by reflexivity.
    replace (2 * 2) with 4 by reflexivity.
    replace 8 with (4 * 2) by reflexivity.
    rewrite -> (mult_commutativity _ 4).
    rewrite <- distributivity.
    rewrite -> mult_associativity.
    apply mult_eq.
    rewrite -> mult_commutativity.
    simpl.
    rewrite -> sum_commutativity.
    repeat rewrite -> sum_identity.
    simpl.
    reflexivity.
  Qed.

  Definition phi2 (n : nat) := ∑(n)[i |-> 8 * i] = 4 * n * (n + 1).

  Theorem x4_32_alt : forall (n : nat), (phi2 n).
  Proof.
    induction n as [| n' HI].
    - unfold phi2. simpl. reflexivity.
    - unfold phi2.
      unfold phi2 in HI.
    replace (∑(_)[i |-> _]) with (8 * S n' + ∑(n')[i |-> 8 * i]) by reflexivity.
      rewrite -> HI.
      rewrite <- succ_eq_sum1.
      replace 8 with (4 * 2) by reflexivity.
      repeat rewrite -> (mult_associativity 4 _).
      repeat rewrite -> (mult_commutativity _ (S n')).
      repeat rewrite <- distributivity.
      repeat apply mult_eq.
      rewrite -> sum_commutativity.
      simpl.
      reflexivity.
  Qed.

  Definition psi (n : nat) := 8 * ∑(n)[i |-> i] < (2 * n + 1)^2.

  Theorem x4_32_iii : forall (n : nat), (psi n).
  Proof.
    induction n as [| n' HI].
    - unfold psi. 
      exists 0.
      simpl.
      reflexivity.
    - unfold psi.
      unfold psi in HI.
      rewrite -> (succ_eq_sum1 n') at 2.
      rewrite -> square_of_sum.
      rewrite -> distributivity.
      repeat rewrite -> mult_identity1.
      rewrite -> distributivity.
      rewrite -> square_of_sum.
      repeat rewrite <- (sum_associativity (_^2) _ _).
      rewrite -> (sum_commutativity _ (1^2)).
      rewrite <- (sum_associativity _ (2^2) _).
      rewrite -> (sum_commutativity (2^2) _).
      rewrite -> (sum_commutativity (2 * _) _).
      repeat rewrite -> (sum_associativity (1^2) _ _).
      rewrite -> (sum_commutativity (1^2) _).
      repeat rewrite -> (sum_associativity (_^2) _ _).
      rewrite <- (mult_identity1 (2 * n')) at 2.
      rewrite <- square_of_sum.
      rewrite <- (sum_associativity (_^2) _ _).
      replace (2 * 2 + 2 ^ 2) with (8 * 1) by reflexivity.
      rewrite -> (mult_associativity 2 n' _).
      rewrite -> (mult_commutativity n' _).
      rewrite <- (mult_associativity 2 _ _).
      rewrite <- (mult_associativity _ 2 _).
      replace (2 * 2 * 2) with 8 by reflexivity.
      rewrite <- sum_associativity.
      rewrite -> (sum_commutativity (8 * 1) _).
      rewrite <- distributivity.
      rewrite <- (succ_eq_sum1 n').
      rewrite -> (sum_commutativity _ (8 * _)).
      replace (∑(_)[i |-> _]) with (S n' + ∑(n')[i |-> i]) by reflexivity.
      rewrite -> distributivity.
      apply sum_lt.
      exact HI.
  Qed.
End x4_32.

Fixpoint fibonacci (n : nat) :=
match n with
| O               => O
| S O             => S O
| S (S n'' as n') => (fibonacci n') + (fibonacci n'')
end.

Notation "F( n  )" := (fibonacci n).

Example x4_33 : forall (n : nat), ∑(0 to n)[i |-> F(i)] + 1 = F(n + 2).
Proof.
  induction n as [| n' HI].
  - simpl. reflexivity.
  - replace (∑(_ to _)[i |-> _]) with (F(S n') + ∑(0 to n')[i |-> F(i)]) by reflexivity.
    rewrite <- sum_associativity.
    rewrite -> HI.
    replace (n' + 2) with (S(S n')) by reflexivity.
    rewrite -> sum_commutativity.
    replace (F(_) + F(_)) with (F(S(S(S n')))) by reflexivity.
    replace (S n' + 2) with (S(S(S n'))) by reflexivity.
    reflexivity.
Qed.


Example x4_34 : forall (n : nat), ∑(n)[i |-> (F(i))^2] = F(n) * F(n + 1).
Proof.
  induction n as [| n' HI].
  - simpl. reflexivity.
  - replace (∑(_)[_ |-> _]) with (F(S n')^2 + ∑(n')[i |-> F(i)^2]) by reflexivity.
    rewrite -> HI.
    repeat rewrite <- succ_eq_sum1.
    unfold exp.
    rewrite -> mult_identity.
    rewrite -> (mult_commutativity F(n') _).
    rewrite <- distributivity.
    replace (F(S n') + F(n')) with (F(S(S n'))) by reflexivity.
    reflexivity.
Qed.


Fixpoint product (n m : nat)(f : nat -> nat) : nat :=
match n, m with
| O, O    => f(O)
| O, S _  => S O
| S n', _ => if (m <=? n)
             then (f n) * (product n' m f)
             else (S O)
end.

Notation "∏( m 'to' n )[ i |-> f ]" := (product n m (fun i : nat => f)).
Notation "∏( n )[ i |-> f ]" := (product n 1 (fun i : nat => f)).

(** Intervalo de problemas **)

Fixpoint tetracao (n m : nat) : nat :=
match m with
| O    => S O
| S m' => n ^ (tetracao n m')
end.

Fixpoint t (n : nat)(h : nat -> nat) :=
match n with
| O    => S O
| S n' => (t n' h) * (h n')
end.

Fixpoint T (n m : nat)(h : nat -> nat) :=
match n, m with
| O, _    => S O
| S n', _ => (T n' m h) * (h (m + n'))
end.

(* PIF -> PIFF *)
Theorem strong_induction : forall (phi : nat -> Prop),
  (forall k, (forall i, i < k -> (phi i)) -> (phi k)) -> forall n, (phi n).
Proof.
  intros phi Hstrind n.
  assert (H: forall k i, i < k -> phi i).
    { induction k as [| k' HIk'].
      - intros i Hi_lt_0.
        apply (not_lt_0 i) in Hi_lt_0 as Hbot.
        contradiction.
      - intros i Hi_lt_Sk'.
        apply (n_lt_Sm i k') in Hi_lt_Sk' as Hi_leq_k'.
        destruct (lt_or_eq i k' Hi_leq_k') as [Hi_lt_k' | Hi_eq_k'].
        + apply (HIk' i) in Hi_lt_k' as Hpi.
          exact Hpi.
        + apply (Hstrind k') in HIk' as Hpk'.
          rewrite -> Hi_eq_k'.
          exact Hpk'. }
  apply (Hstrind n) in H as Hpn.
  exact Hpn.
Qed.

Theorem piff_implies_pif : forall (phi : nat -> Prop),
  ((forall k, (forall i, i < k -> phi i) -> phi k) -> forall n, phi n)
  -> ((phi 0 /\ forall k, phi k -> phi (S k)) -> forall n, phi n).
Proof.
  intros phi Hpiff Hind.
  destruct Hind as (Hbase, Hstep).
  apply Hpiff.
  intros k Hfi_lt_k__pi.
  destruct k as [| k'].
  - exact Hbase.
  - apply Hstep.
    apply (Hfi_lt_k__pi k').
    exact (lt_succ k').
Qed.

Definition is_min (m : nat)(phi : nat -> Prop) : Prop :=
  phi m /\ forall k, phi k -> m <= k.

Notation "m = min( phi  )" := (is_min m phi)(at level 50).

Theorem well_ordering : lem -> forall (phi : nat -> Prop),
  (exists n, phi n) -> exists m, m = min(phi).
Proof.
  intros Hlem.
  assert (forall u (psi: nat -> Prop), (exists v, (psi v /\ v <= u)) -> (exists m, m = min(psi))).
    { induction u as [| u' HI].
      - intros psi H.
        destruct H as (v, H).
        destruct H as (Hpv, Hv_leq_0).
        apply (leq_0_implies_eq_0 v) in Hv_leq_0 as Hv_eq_0.
        rewrite -> Hv_eq_0 in Hpv.
        exists 0. split.
        + exact Hpv.
        + intros k Hpk.
          exact (O_leq_x k).
      - intros psi H.
        destruct H as (v, H).
        destruct H as (Hpv, Hv_leq_u).
        destruct (n_leq_Sm v u' Hv_leq_u) as [Hv_leq_u' | Hv_eq_u].
        + apply HI.
          exists v. split.
          * exact Hpv.
          * exact Hv_leq_u'.
        + destruct (Hlem (exists x : nat, psi x /\ x <= u')) as [Hex_px_and_x_leq_u' | Hnex_px_and_x_leq_u'].
          * apply HI.
            exact Hex_px_and_x_leq_u'.
          * exists v. split.
            -- exact Hpv.
            -- intros k Hpk.
               assert (Hfx_px_imp_x_gt_u: forall x, psi x -> ~(x <= u')).
                 { apply neg_exists2. exact Hnex_px_and_x_leq_u'. }
               apply (Hfx_px_imp_x_gt_u k) in Hpk as Hn_k_leq_u'.
               apply (neg_leq k u') in Hn_k_leq_u' as Hk_gt_u'.
               apply (gt_implies_geq_succ k u') in Hk_gt_u' as Hk_geq_Su'.
               rewrite -> Hv_eq_u.
               exact Hk_geq_Su'. }
  intros phi Hen_pn.
  destruct Hen_pn as (n, Hpn).
  apply (H (S n)).
  exists n. split.
  - exact Hpn.
  - exact (leq_succ n).
Qed.

Theorem pbo_implies_pif :
  raa -> (forall (phi : nat -> Prop), (exists n, phi n) -> exists a, phi a /\ forall b, (phi b -> a <= b))
  -> (forall (phi : nat -> Prop), (phi 0 /\ forall k, (phi k -> phi (S k))) -> forall n, phi n).
Proof.
  intros Hraa Hpbo phi Hind.
  destruct Hind as (Hbase, Hstep).
  intros n.
  apply Hraa. intros Hnpn.
  assert (Hen_npn: exists n, ~phi n).
    { exists n. exact Hnpn. }
  destruct (Hpbo _ Hen_npn) as (m, H).
  destruct H as (Hnpm, Hfb_npb_imp_m_leq_b).
  destruct m as [| m'].
  - apply Hnpm in Hbase as Hbot.
    exact Hbot.
  - assert (Hnpm': ~phi m').
      { intros Hpm'.
        apply (Hstep m') in Hpm' as Hpm.
        apply Hnpm in Hpm as Hbot.
        exact Hbot. }
    apply (Hfb_npb_imp_m_leq_b m') in Hnpm' as Hm_leq_m'.
    apply (neg_lt_inverse m' (S m') Hm_leq_m').
    apply (lt_succ m').
Qed.

Definition odd (n : nat) : Prop := exists k, n = 2 * k + 1.

Example power_odd : forall n a, odd a -> odd (a^n).
Proof.
  induction n as [| n' HI].
  - intros a Hodd_a.
    simpl.
    exists 0.
    simpl.
    reflexivity.
  - intros a Hodd_a.
    simpl.
    apply (HI a) in Hodd_a as Hodd_a_exp_n'.
    destruct Hodd_a as (u, Ha_eq).
    destruct Hodd_a_exp_n' as (v, Ha_exp_n'_eq).
    exists (2 * u * v + u + v).
    repeat rewrite -> distributivity.
    rewrite -> (mult_commutativity _ u) at 1.
    repeat rewrite <- (mult_associativity 2 _ _).
    rewrite -> (mult_associativity _ _ v).
    rewrite <- (mult_identity1 (2 * u)) at 2.
    rewrite <- distributivity.
    rewrite -> (mult_commutativity (2 * u) _).
    rewrite <- sum_associativity.
    rewrite <- (mult_identity1 (2 * v + 1)) at 2.
    rewrite <- distributivity.
    rewrite <- Ha_exp_n'_eq.
    rewrite <- Ha_eq.
    reflexivity.
Qed.

Theorem lt_leq : forall (a b c : nat), a < b /\ b <= c -> a < c.
Proof.
  intros a b c Ha_lt_b__and__b_leq_c.
  destruct Ha_lt_b__and__b_leq_c as (Ha_lt_b, Hb_leq_c).
  destruct (lt_or_eq b c Hb_leq_c) as [Hb_lt_c | Hb_eq_c].
  - apply (lt_transitivity a b c).
    split; assumption.
  - rewrite <- Hb_eq_c.
    exact Ha_lt_b.
Qed.

