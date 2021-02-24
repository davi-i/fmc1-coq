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

Theorem mult_identity : forall (n : nat), n = (S O) * n.
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
  rewrite <- (mult_identity n).
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

Example x4_26 :
  forall (n : nat), (∑(n)[fun i => 4 * i^3]) = n^2 * (n + 1)^2.
Proof.
  intros n. induction n as [| n' HI].
  - simpl. reflexivity.
  - unfold summation. fold summation.
    rewrite -> HI.
    rewrite -> (mult_commutativity 4 (S n'^3)).
    replace (S n' ^ 3) with ((n' + 1)^2 * S n').
    rewrite -> (mult_commutativity (n'^2) ((n' + 1)^2)).
    rewrite -> (mult_associativity ((n' + 1) ^ 2) (S n') 4).
    rewrite <- (distributivity ((n' + 1) ^ 2) (S n' * 4) (n' ^ 2)).
    replace (S n' * 4 + n' ^ 2) with (S (S n') ^ 2).
    simpl. reflexivity.
    rewrite -> (sum_commutativity (S n' * 4) (n' ^ 2)).
    simpl.
    rewrite <- (mult_identity n').
    rewrite -> (sum_commutativity 0 n').
    rewrite -> (mult_commutativity (S (S n')) n').
    rewrite -> (sum_commutativity (S (S (n' * S (S n') + n'))) n').
    rewrite -> (sum_commutativity (n' * S (S n')) n').
    rewrite -> (sum_commutativity (S (n' + 0)) n').
    rewrite -> (sum_commutativity (S (n' + S (n' + 0))) n').
    rewrite -> (sum_commutativity (S (n' + S (n' + S (n' + 0)))) n').
    simpl.
    rewrite -> (sum_associativity (n' * n') n' (n' + (n' + n'))).
    rewrite -> (sum_commutativity (n' * n') n').
    rewrite <- (sum_associativity n' (n' * n') (n' + (n' + n'))).
    rewrite -> (sum_associativity (n' * n') n' (n' + n')).
    rewrite -> (sum_commutativity (n' * n') n').
    rewrite <- (sum_associativity n' (n' * n') (n' + n')).
    rewrite -> (sum_associativity (n' * n') n' n').
    rewrite -> (sum_commutativity (n' * n') n').
    reflexivity.
    simpl. reflexivity.
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

Lemma square_of_sum : forall (a b : nat), (a + b)^2 = a^2 + 2 * a * b + b^2.
Proof.
  intros a b. simpl.
  repeat rewrite <- mult_identity.
  rewrite -> distributivity.
  rewrite -> (mult_commutativity (a + b) a).
  rewrite -> (mult_commutativity (a + b) b).
  rewrite -> distributivity.
  rewrite -> distributivity.
  rewrite -> (mult_associativity 2 a b).
  rewrite -> (mult_commutativity 2 (a * b)).
  simpl.
  rewrite -> sum_identity.
  rewrite -> (mult_commutativity b a).
  rewrite <- sum_associativity.
  rewrite -> (sum_associativity (a * b) (a * b) (b * b)).
  rewrite -> sum_associativity.
  reflexivity.
Qed.

Lemma cube_of_sum : forall (a b : nat), (a + b)^3 = a^3 + 3 * a^2 * b + 3 * a * b^2 + b^3.
Proof.
  intros a b. simpl.
  repeat rewrite <- mult_identity.
  rewrite -> mult_associativity.
  replace ((a + b) * (a + b)) with ((a + b)^2).
  rewrite -> square_of_sum.
  simpl.
  repeat rewrite <- mult_identity.
  repeat rewrite -> distributivity.
  rewrite -> (mult_commutativity (a + b) (a * a)).
  rewrite -> (mult_commutativity (a + b) (2 * a * b)).
  rewrite -> (mult_commutativity (a + b) (b * b)).
  repeat rewrite -> distributivity.
  rewrite -> (mult_associativity 3 (a * a) b).
  rewrite -> (mult_commutativity 3 ((a * a) * b)).
  rewrite -> (mult_associativity 3 a (b * b)).
  rewrite -> (mult_commutativity 3 (a * (b * b))).
  simpl.
  repeat rewrite -> sum_identity.
  rewrite -> (mult_associativity (2 * a) b a).
  rewrite -> (mult_associativity 2 a (b * a)).
  rewrite -> (mult_commutativity 2 (a * (b * a))).
  rewrite -> (mult_associativity (2 * a) b b).
  rewrite -> (mult_associativity 2 a (b * b)).
  rewrite -> (mult_commutativity 2 (a * (b * b))).
  simpl.
  repeat rewrite -> sum_identity.
  repeat rewrite -> (mult_commutativity b a).
  repeat rewrite <- (mult_associativity a a b).
  rewrite -> sum_associativity.
  rewrite <- (sum_associativity (a * a * a) (a * a * b) (a * a * b + a * a * b + (a * (b * b) + a * (b * b)))).
  rewrite -> (sum_associativity (a * a * b) (a * a * b + a * a * b) (a * (b * b) + a * (b * b))).
  rewrite -> (sum_associativity (a * a * b) (a * a * b) (a * a * b)).
  rewrite -> (sum_associativity (a * a * a) (a * a * b + a * a * b + a * a * b) (a * (b * b) + a * (b * b))).
  rewrite -> (mult_commutativity (b * b) a).
  rewrite <- (sum_associativity (a * a * a + (a * a * b + a * a * b + a * a * b)) (a * (b * b) + a * (b * b)) (a * (b * b))).
  reflexivity.
  { simpl. rewrite <- mult_identity. reflexivity. }
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
    replace (S n' ^ 2 + 2 * S n' * ∑( n' )[ fun i : nat => i ]) with (S n' ^ 3).
      { reflexivity. }
Abort.

Theorem indution_starting_in_b :
  forall (phi : nat -> Prop)(b : nat), b <> 0 ->
    (phi b) /\ (forall k : nat, k >= b -> ((phi k) -> (phi (S k))))
    -> forall (n : nat), (n >= b -> (phi n)).
Proof.
  intros phi b Hb_neq_0 Hind.
  destruct Hind as (Hbase, Hstep).
  induction n as [| n' HI].
  - intros H0_geq_b.
    assert (Hb_leq_0__and__0_leq_b: b <= 0 /\ 0 <= b).
      { split.
        - exact H0_geq_b.
        - exact (O_leq_x b). }
    apply (leq_antisymmetry b 0) in Hb_leq_0__and__0_leq_b as Hb_eq_0.
    apply Hb_neq_0 in Hb_eq_0 as Hbot.
    contradiction.
  - intros HSn'_geq_b.
    destruct (n_leq_Sm b n' HSn'_geq_b) as [Hb_leq_n' | Hb_eq_Sn'].
    + apply HI in Hb_leq_n' as Hpn'.
      apply (Hstep n') in Hb_leq_n' as HpSn'.
      exact HpSn'.
      exact Hpn'.
    + rewrite <- Hb_eq_Sn'.
      exact Hbase.
Qed.

Example x4_31 : forall (n : nat), n >= 8 -> exists (a b : nat), n = 3 * a + 5 * b.
Proof.
  intros n Hn_geq_8.
  assert (H8_neq_0: 8 <> 0).
    { discriminate. }
  apply (indution_starting_in_b (fun i => i = 3 * a + 5 * b)



