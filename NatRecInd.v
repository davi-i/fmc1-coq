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

Theorem mult_identity : forall (n : nat), (S O) * n = n.
Proof.
  intros n.
  rewrite -> (mult_commutativity (S O) n).
  simpl.
  rewrite -> (sum_commutativity O n).
  simpl.
  reflexivity.
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

Definition gt (n m : nat) : Prop := ~(n <= m).
Notation "n > m" := (gt n m).

Definition geq (n m : nat) : Prop := m <= n.
Notation "n >= m" := (geq n m).

Definition lt (n m : nat) : Prop := m > n.
Notation "n < m" := (lt n m).

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
  intros n m Hn_leq_m__or__n_eq_Sm.
  destruct Hn_leq_m__or__n_eq_Sm as [Hn_leq_m | Hn_eq_Sm].
  - destruct Hn_leq_m as (k, Hn_plus_k).
    exists (S k). simpl.
    rewrite -> Hn_plus_k.
    reflexivity.
  - exists O. simpl.
    assumption.
Qed.

Theorem leq_reflexity : forall (x : nat), x <= x.
Proof.
  intros x. exists O. simpl. reflexivity.
Qed.

Lemma succ_leq_O : forall (x : nat), ~(S x <= O).
Proof.
  intros x HSx_leq_O.
  destruct HSx_leq_O as (k, HSx_plus_k).
  rewrite -> (sum_commutativity (S x) k) in HSx_plus_k.
  simpl in HSx_plus_k. inversion HSx_plus_k.
Qed.

Lemma leq_succ : forall (x y : nat), S x <= S y -> x <= y.
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
      apply (succ_leq_O y') in HSy'_leq_O as Hbot.
      contradiction.
  - intros y HSx'_leq_y__and__y_leq_Sx'.
    destruct HSx'_leq_y__and__y_leq_Sx' as (HSx'_leq_y, Hy_leq_Sx').
    destruct y as [| y'] eqn:Ey.
    + apply (succ_leq_O x') in HSx'_leq_y as Hbot.
      contradiction.
    + apply (leq_succ x' y') in HSx'_leq_y as Hx'_leq_y'.
      apply (leq_succ y' x') in Hy_leq_Sx' as Hy'_leq_x'.
      assert (Hx'_leq_y'__and__y'_leq_x': x' <= y' /\ y' <= x').
        { split.
          - exact Hx'_leq_y'.
          - exact Hy'_leq_x'. }
      apply (HI y') in Hx'_leq_y'__and__y'_leq_x' as Hx'_eq_y'.
      rewrite <- Hx'_eq_y'.
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

Lemma leq_succ_inverse : forall (x y : nat), x <= y -> S x <= S y.
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
      * left. exact (leq_succ_inverse x' y' Hx'_leq_y').
      * right. exact (leq_succ_inverse y' x' Hy'_leq_x').
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
  - left. intros Hy_leq_x.
    assert (Hx_eq_y : x = y).
      { apply (leq_antisymmetry x y).
        split.
        - rewrite <- Hx_plus_k.
          exists (S k').
          reflexivity.
        - exact Hy_leq_x. }
    rewrite -> Hx_eq_y in Hx_plus_k.
    apply (x_plus_Sy y k') in Hx_plus_k as Hbot.
    exact Hbot.
Qed.

Theorem gt_or_eq : forall (x y : nat), x >= y -> x > y \/ x = y.
Proof.
  intros x y Hx_geq_y.
  apply (lt_or_eq y x) in Hx_geq_y as Hy_lt_x__or__y_eq_x.
  destruct Hy_lt_x__or__y_eq_x as [Hy_lt_x | Hy_eq_x].
  - left. unfold lt in Hy_lt_x. exact Hy_lt_x.
  - right. rewrite <- Hy_eq_x. reflexivity.
Qed.

(** Problema Π4.1 **)

Fixpoint tetracao (n m : nat) : nat :=
  match m with
  | O    => S O
  | S m' => n ^ (tetracao n m')
  end.

Notation "n ♢ m" := (tetracao n m) 
                    (at level 20).


(** Low level para high level **)

Theorem succ_eq_sum1 : forall (n : nat), S n = n + 1.
Proof.
  intros n. simpl. reflexivity.
Qed.

(** Somátório e produtório **)

Fixpoint summation (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O    => O
  | S n' => (f n) + (summation n' f)
  end.

(** Fixpoint summation2 (n : nat) (m : nat) (f : nat -> nat) : nat :=
  match m with
  | n => (f n)
  | S m' => (f m) + (summation2 n (S m) f)
  end. **)

Notation "∑( n )[ f  ]" := (summation n f).


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

Theorem sum_eq : forall (a b k : nat), k + a = k + b -> a = b.
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
    apply HI in Ha_plus_k' as Ha_eq_b.
    exact Ha_eq_b.
Qed.

Theorem sum_eq_inverse : forall (a b k : nat), a = b -> k + a = k + b.
Proof.
  intros a b k Ha_eq_b.
  rewrite -> Ha_eq_b.
  reflexivity.
Qed.

Theorem mult_eq : forall (a b k : nat), (S k) * a = (S k) * b -> a = b.
Proof.
  induction a as [| a' HI].
  - intros b k HSk0_eq_Skb.
    simpl in HSk0_eq_Skb.
    destruct b as [| b'].
    + reflexivity.
    + simpl in HSk0_eq_Skb.
      discriminate.
  - intros b k HSkSa'_eq_Skb.
    destruct b as [| b'].
    + simpl in HSkSa'_eq_Skb.
      discriminate.
    + simpl in HSkSa'_eq_Skb.
      inversion HSkSa'_eq_Skb as [HSka'_plus_k].
      repeat rewrite -> (sum_commutativity _ k) in HSka'_plus_k.
      apply sum_eq in HSka'_plus_k as HSka'_eq_Skb'.
      apply HI in HSka'_eq_Skb' as Ha'_eq_b.
      rewrite -> Ha'_eq_b.
      reflexivity.
Qed.

Theorem mult_eq_inverse : forall (a b k : nat), a = b -> k * a = k * b.
Proof.
  intros a b k Ha_eq_b.
  rewrite -> Ha_eq_b.
  reflexivity.
Qed.

Theorem exp_eq : forall (a b k : nat), a^(S k) = b^(S k) -> a = b.
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

Theorem exp_eq_inverse : forall (a b k : nat), a = b -> a^k = b^k.
Proof.
  intros a b k Ha_eq_b.
  rewrite -> Ha_eq_b.
  reflexivity.
Qed.

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

Theorem cube_of_sum : forall (a b : nat), (a + b)^3 = a^3 + 3 * a^2 * b + 3 * a * b^2 + b^3.
Proof.
  intros a b.
  repeat rewrite -> (mult_associativity 3 _ _).
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
  forall (n : nat), (∑(n)[fun i => 4 * i^3]) = n^2 * (n + 1)^2.
Proof.
  intros n. induction n as [| n' HI].
  - simpl. reflexivity.
  - unfold summation. fold summation.
    rewrite -> HI.
    replace (n' + 1) with (S n') by reflexivity.
    rewrite -> mult_commutativity.
    replace (S n' ^ 3) with (S n' ^2 * S n') by reflexivity.
    rewrite -> (mult_commutativity _ (S n' ^ 2)).
    rewrite -> mult_associativity.
    rewrite <- distributivity.
    apply mult_eq_inverse.
    replace (S n' * 4) with ((n' + 1) * 4) by reflexivity.
    rewrite -> mult_commutativity.
    rewrite -> distributivity.
    rewrite -> (sum_commutativity (4 * n') _).
    replace (4 * 1) with (2^2) by reflexivity.
    replace (4 * n') with ((2 * 2) * n') by reflexivity.
    rewrite -> mult_associativity.
    rewrite <- square_of_sum.
    rewrite -> sum_commutativity.
    apply exp_eq_inverse.
    simpl.
    reflexivity.
Qed.

Theorem distributivity_summation :
  forall (n m : nat)(f : nat -> nat), ∑(n)[fun i => m * (f i)] = m * ∑(n)[f].
Proof.
  intros n. induction n as [| n' HI].
  - intros m f. simpl. reflexivity.
  - intros m f. unfold summation. fold summation.
    rewrite -> (HI m f).
    rewrite -> distributivity.
    reflexivity.
Qed.

Example x4_29 :  forall (n : nat), 6 * ∑(n)[fun i => i^2] = 2 * n^3 + 3 * n^2 + n.
Proof.
  induction n as [| n' HI].
  - simpl. reflexivity.
  - unfold summation. fold summation.
    rewrite -> distributivity.
    rewrite -> HI.
    rewrite -> (succ_eq_sum1 n').
    rewrite -> square_of_sum.
    rewrite -> cube_of_sum.
    repeat rewrite -> distributivity.
Abort.

Example x4_30 : forall (n : nat), ∑(n)[fun i => i^3] = (∑(n)[fun i => i])^2.
Proof.
  induction n as [| n' HI].
  - simpl. reflexivity.
  - unfold summation. fold summation.
    rewrite -> HI.
    rewrite -> square_of_sum.
    replace (S n' ^ 2 + 2 * (S n' * _)) with (S n' ^ 3).
      { reflexivity. }
Abort.

Theorem indution_starting_in_b :
  forall (b : nat)(phi : nat -> Prop),
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
    destruct (n_leq_Sm b n' HSn'_geq_b) as [Hb_leq_n' | Hb_eq_Sn'].
    + apply HI in Hb_leq_n' as Hpn'.
      apply (Hstep n' Hb_leq_n') in Hpn' as HpSn'.
      exact HpSn'.
    + rewrite <- Hb_eq_Sn'.
      exact Hbase.
Qed.

Lemma x4_31_lemma1 : forall (a b : nat), a >= 8 -> a = ∑(b)[fun _ => 3] -> 3 <= b.
Proof.
  intros a b Ha_gte_8 Ha_eq_sum_b_3.
  destruct Ha_gte_8 as (k, H8_plus_k).
  rewrite -> sum_commutativity in H8_plus_k.
  simpl in H8_plus_k.
  rewrite -> Ha_eq_sum_b_3 in H8_plus_k.
  destruct b as [| b'].
  - simpl in H8_plus_k. discriminate.
  - destruct b' as [| b''].
    + simpl in H8_plus_k. discriminate.
    + destruct b'' as [| b'''].
      * simpl in H8_plus_k. discriminate.
      * exists b'''.
        rewrite -> sum_commutativity.
        simpl. reflexivity.
Qed.


Example x4_31 : forall (n : nat), n >= 8 -> exists (a b : nat), n = ∑(a)[fun _ => 3] + ∑(b)[fun _ => 5].
Proof.
  apply (indution_starting_in_b 8).
  split.
  - exists 1. exists 1.
    simpl. reflexivity.
  - intros k Hk_gte_8 HI.
    destruct HI as (x, Heb).
    destruct Heb as (y, Hk_eq).
    destruct y as [| y'].
    + simpl in Hk_eq.
      destruct (x4_31_lemma1 k x Hk_gte_8 Hk_eq) as (x', H3_plus_k).
      exists x'. exists 2.
      unfold summation at 2.
      unfold sum at 3 2.
      replace 10 with (3 + 3 + 3 + 1) by reflexivity.
      rewrite -> sum_associativity.
      rewrite -> (sum_commutativity _ (_ + _)).
      rewrite <- (sum_associativity 3 3 _).
      rewrite <- (sum_associativity 3 _ _).
      rewrite <- (sum_associativity 3 3 _).
      replace (3 + ∑( _ )[ _ ]) with (∑( S x' )[ fun _ : nat => 3 ]) by reflexivity.
      replace (3 + ∑( _ )[ _ ]) with (∑( S(S x') )[ fun _ : nat => 3 ]) by reflexivity.
      replace (3 + ∑( _ )[ _ ]) with (∑( S(S(S x')) )[ fun _ : nat => 3 ]) by reflexivity.
      replace (S (S (S x'))) with (x' + 3) by reflexivity.
      rewrite -> (sum_commutativity x' 3).
      rewrite -> H3_plus_k.
      rewrite <- Hk_eq.
      simpl.
      reflexivity.
    + exists (S(S x)).
      exists y'.
      unfold summation at 1. fold summation.
      rewrite -> sum_associativity.
      replace (3 + 3) with (1 + 5) by reflexivity.
      rewrite <- (sum_associativity 1 _ _).
      rewrite -> (sum_commutativity 5 _).
      rewrite -> sum_associativity.
      rewrite <- sum_associativity.
      replace (5 + _) with (∑( S y' )[ fun _ : nat => 5 ]) by reflexivity.
      rewrite <- sum_associativity.
      rewrite <- Hk_eq.
      rewrite -> sum_commutativity.
      simpl.
      reflexivity.
Qed.

Theorem inducao_duas_bases : forall (phi : nat -> Prop),
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


Definition phi (n : nat) := ∑(n)[mult 8] = (2 * n + 1)^2.

Theorem x4_32i : forall (n : nat), (phi n) -> (phi (S n)).
Proof.
  intros n.
  unfold phi.
  intros Hpn.
  unfold summation. fold summation.
  rewrite -> Hpn.
  replace (2 * S n + 1) with (2 * n + 1 + 2) by reflexivity.
  rewrite -> (square_of_sum (2 * n + 1) 2).
  rewrite -> sum_commutativity.
  rewrite <- sum_associativity.
  apply sum_eq_inverse.
  repeat rewrite -> (mult_commutativity 2 _).
  rewrite -> mult_associativity.
  replace (2^2) with (4 * 1) by reflexivity.
  replace (2 * 2) with 4 by reflexivity.
  replace 8 with (4 * 2) by reflexivity.
  rewrite -> (mult_commutativity _ 4).
  rewrite <- distributivity.
  rewrite -> mult_associativity.
  apply mult_eq_inverse.
  rewrite -> mult_commutativity.
  simpl.
  rewrite -> sum_commutativity.
  repeat rewrite -> sum_identity.
  simpl.
  reflexivity.
Abort.

Definition phi2 (n : nat) := ∑(n)[mult 8] = 4 * n * (n + 1).

Theorem x4_32_alt : forall (n : nat), (phi2 n).
Proof.
  induction n as [| n' HI].
  - unfold phi2. simpl. reflexivity.
  - unfold phi2.
    unfold phi2 in HI.
    unfold summation. fold summation.
    rewrite -> HI.
    rewrite <- succ_eq_sum1.
    replace 8 with (4 * 2) by reflexivity.
    repeat rewrite -> (mult_associativity 4 _).
    repeat rewrite -> (mult_commutativity _ (S n')).
    repeat rewrite <- distributivity.
    repeat apply mult_eq_inverse.
    rewrite -> sum_commutativity.
    simpl.
    reflexivity.
Qed.



