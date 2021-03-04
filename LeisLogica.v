(** Feitiços **)
Definition lem : Prop := forall (P: Prop), P \/ (~ P).
Definition raa : Prop := forall (P : Prop), (~P -> False) -> P.

Theorem lem_implies_raa : lem -> raa.
Proof.
  intros Hlem P HnP_imp_F.
  destruct (Hlem P) as [HP | HnP].
  - exact HP.
  - apply HnP_imp_F in HnP as Hbot.
    contradiction.
Qed.

Theorem raa_implies_lem : raa -> lem.
Proof.
  intros Hraa P.
  apply Hraa.
  intros HnP.
Abort.


(** 1. Proposições de dupla negação **)

Theorem doubleneg_intro : forall (p : Prop), p -> ~ ~ p.
Proof.
  intros p.
  unfold not.
  intros Hp.
  intros p_implies_f.
  apply (p_implies_f Hp).
Qed.

Theorem doubleneg_elim_with_raa : raa -> forall (p: Prop), ~ ~ p -> p.
Proof.
  intros Hraa p HnnP.
  apply Hraa.
  exact HnnP.
Qed.


(** 2. A irrefutabilidade do LEM **)

Theorem irrefutabilidade_lem_with_lem : lem -> forall (P : Prop), ~ ~(P \/ ~P).
Proof.
  intros Hlem P Hn_P_or_nP.
  apply Hn_P_or_nP in Hlem as Hfalse.
  assumption.
Qed.


(** 3. A lei de Peirce e sua versão "fraca" **)

Theorem lei_de_Peirce_with_raa : raa -> forall (P Q: Prop), ((P -> Q) -> P) -> P.
Proof.
  intros Hraa P Q HP_imp_Q__imp_P.
  apply Hraa.
  intros HnP.
  assert(HP_imp_Q: P -> Q).
    { intro HP. apply HnP in HP as Hbot. contradiction. }
  apply HP_imp_Q__imp_P in HP_imp_Q as HP.
  apply HnP in HP as Hbot.
  exact Hbot.
Qed.

Theorem lei_de_Peirce_fraca : forall (P Q : Prop), ((P -> Q) -> P) -> ~~P.
Proof.
  intros P Q HP_imp_Q__imp_P HnP.
  assert(HP_imp_Q: P -> Q).
  * intro HP. apply HnP in HP. contradiction.
  * apply HP_imp_Q__imp_P in HP_imp_Q as HP. apply HnP in HP. assumption.
Qed.


(** 4. Proposições de interdefinabilidade dos ⇒,∨: **)

Theorem interdefinabilidade_implica_ou1_with_lem : lem -> forall (P Q : Prop), (P -> Q) -> (~P \/ Q).
Proof.
  intros Hlem P Q HP_imp_Q.
  destruct (Hlem P) as [Hp | Hnp].
  - apply HP_imp_Q in Hp as HQ. right. assumption.
  - left. assumption.
Qed.

Theorem interdefinabilidade_implica_ou2 : forall (P Q : Prop), (~P \/ Q) -> (P -> Q).
Proof.
  intros P Q HnP_or_Q HP.
  destruct (HnP_or_Q) as [HnP | HQ].
  - apply HnP in HP as Hfalse. contradiction.
  - assumption.
Qed.

Theorem interdefinabilidade_implica_ou3 : forall (P Q : Prop), (P \/ Q) -> (~P -> Q).
Proof.
  intros P Q HP_or_Q HnP.
  destruct (HP_or_Q) as [HP | HQ].
  - apply HnP in HP as Hfalse. contradiction.
  - assumption.
Qed.

Theorem interdefinabilidade_implica_ou4_with_lem : lem -> forall (P Q : Prop), (~P -> Q) -> (P \/ Q).
Proof.
  intros Hlem P Q HnP_imp_Q.
  destruct (Hlem P) as [Hp | Hnp].
  - left. assumption.
  - apply HnP_imp_Q in Hnp as HQ. right. assumption.
Qed.


(** 5. Proposições de interdefinabilidade dos ∨,∧: **)

Theorem interdefinabilidade_e_ou1 : forall (P Q : Prop), P \/ Q -> ~(~P /\ ~Q).
Proof.
  intros P Q HP_or_Q HnP_and_nQ. destruct HnP_and_nQ as [HnP HnQ].
  destruct (HP_or_Q) as [HP | HQ].
  - apply HnP in HP as Hfalse. assumption.
  - apply HnQ in HQ as Hfalse. assumption.
Qed.

Theorem interdefinabilidade_e_ou2_with_lem : lem -> forall (P Q : Prop), ~(~P /\ ~Q) -> P \/ Q.
Proof.
  intros Hlem P Q Hn_nP_and_nQ.
  destruct (Hlem P) as [HP | HnP].
  - left. assumption.
  - destruct (Hlem Q) as [HQ | HnQ].
    * right. assumption.
    * assert(HnP_and_nQ: ~P /\ ~Q).
      + split.
        -- assumption.
        -- assumption.
      + apply Hn_nP_and_nQ in HnP_and_nQ. contradiction.
Qed.

Theorem interdefinabilidade_e_ou3 : forall (P Q : Prop), P /\ Q -> ~(~P \/ ~Q).
Proof.
  intros P Q HP_and_Q HnP_or_nQ. destruct HP_and_Q as [HP HQ].
  destruct (HnP_or_nQ) as [HnP | HnQ].
  - apply HnP in HP as Hfalse. assumption.
  - apply HnQ in HQ as Hfalse. assumption.
Qed.

Theorem interdefinabilidade_e_ou4_with_raa : raa -> forall (P Q : Prop), ~(~P \/ ~Q) -> P /\ Q.
Proof.
  intros Hraa P Q Hn_nP_or_nQ. split.
  - apply Hraa.
    intros HnP.
    assert(HnP_or_nQ: ~P \/ ~Q).
      { left. exact HnP. }
    apply Hn_nP_or_nQ in HnP_or_nQ. contradiction.
  - apply Hraa.
    intros HnQ.
    assert(HnP_or_nQ: ~P \/ ~Q).
      { right. exact HnQ. }
    apply Hn_nP_or_nQ in HnP_or_nQ. contradiction.
Qed.


(** 6. As leis de De Morgan **)

Theorem de_morgan1 : forall (P Q : Prop), ~(P \/ Q) -> (~P /\ ~Q).
Proof.
  intros P Q Hn_P_or_Q.
  split.
  - intro HP.
    assert(HP_or_Q: P \/ Q).
      { left. exact HP. }
    apply Hn_P_or_Q in HP_or_Q as Hbot.
    contradiction.
  - intro HQ.
    assert(HP_or_Q: P \/ Q).
      { right. exact HQ. }
    apply Hn_P_or_Q in HP_or_Q as Hbot.
    contradiction.
Qed.

Theorem de_morgan2 : forall (P Q : Prop), (~P /\ ~Q) -> ~(P \/ Q).
Proof.
  intros P Q HnP_and_nQ HP_or_Q. destruct HnP_and_nQ as [HnP HnQ].
  destruct HP_or_Q as [HP | HQ].
  - contradiction.
  - contradiction.
Qed.

Theorem de_morgan3_with_raa : raa -> forall (P Q : Prop), ~(P /\ Q) -> (~P \/ ~Q).
Proof.
  intros Hraa P Q Hn_P_and_Q.
  apply Hraa.
  intros Hn_nP_or_nQ.
  apply (de_morgan1 (~P) (~Q)) in Hn_nP_or_nQ as HnnP_and_nnQ.
  destruct HnnP_and_nnQ as (HnnP, HnnQ).
  assert(HP_or_Q: P /\ Q).
    { split.
      - exact (doubleneg_elim_with_raa Hraa P HnnP).
      - exact (doubleneg_elim_with_raa Hraa Q HnnQ). }
  apply Hn_P_and_Q in HP_or_Q as Hbot.
  contradiction.
Qed.

Theorem de_morgan4 : forall (P Q : Prop), (~P \/ ~Q) -> ~(P /\ Q).
Proof.
  intros P Q HnP_or_nQ HP_and_Q. destruct HP_and_Q as [HP HQ].
  destruct HnP_or_nQ as [HnP | HnQ].
  - contradiction.
  - contradiction.
Qed.


(** 7. Proposições de distributividade dos ∨,∧: **)

Theorem distributividade_e_ou1 : forall (P Q R : Prop), P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
  intros P Q R HP_and__Q_or_R. destruct HP_and__Q_or_R as [HP HQ_or_R].
  destruct HQ_or_R as [HQ | HR].
  - left. split.
    * assumption.
    * assumption.
  - right. split.
    * assumption.
    * assumption.
Qed.

Theorem distributividade_e_ou2 : forall (P Q R : Prop), (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R).
Proof.
  intros P Q R HP_and_Q__or__P_and_R.
  destruct HP_and_Q__or__P_and_R as [HP_and_Q | HP_and_R].
  - destruct HP_and_Q as [HP HQ]. split.
    * assumption.
    * left. assumption.
  - destruct HP_and_R as [HP HR]. split.
    * assumption.
    * right. assumption.
Qed.

Theorem distributividade_ou_e1 : forall (P Q R : Prop), P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R HP_or__Q_and_R.
  destruct HP_or__Q_and_R as [HP | HQ_and_R].
  - split.
    * left. assumption.
    * left. assumption.
  - destruct HQ_and_R as [HQ HR]. split.
    * right. assumption.
    * right. assumption.
Qed.

Theorem distributividade_ou_e2 : forall (P Q R : Prop), (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R HP_or_Q__and__P_or_R. destruct HP_or_Q__and__P_or_R as [HP_or_Q HP_or_R].
  destruct HP_or_Q as [HP | HQ].
  - left. assumption.
  - destruct HP_or_R as [HP | HR].
    * left. assumption.
    * right. split.
      + assumption.
      + assumption.
Qed.

(** 8. As leis de De Morgan para ∃,∀ **)

Theorem neg_forall1 :
  lem -> forall (A: Type)(a : A)(phi : A -> Prop), ~(forall ( x: A ), phi x) -> (exists (x : A), ~phi x).
Proof.
  intros Hlem A a phi Hnfx_px.
Abort.

Theorem neg_forall2 : forall (A : Type)(phi : A -> Prop), (exists (x : A), ~phi x) -> ~(forall ( x: A ), phi x).
Proof.
  intros A phi Hex_npx Hfx_px. destruct Hex_npx as (a, Hnpa).
  apply Hnpa in Hfx_px as Hfalse. assumption.
Qed.

Theorem neg_exists : forall (A : Type)(phi : A -> Prop), ~(exists ( x: A ), phi x) -> (forall (x : A), ~phi x).
Proof.
  intros A phi Hnex_px a Hpa.
  assert (Hex_px: exists (x : A), phi x).
  - exists a. assumption.
  - apply Hnex_px in Hex_px as Hfalse. assumption.
Qed.

Theorem neg_exists_inverse : forall (A : Type)(phi : A -> Prop), (forall (x : A), ~phi x) -> ~(exists ( x: A ), phi x).
Proof.
  intros A phi Hfx_npx Hex_px. destruct Hex_px as (a, Hpa).
  apply (Hfx_npx a) in Hpa as Hfalse. assumption.
Qed.



(** 9. Proposições de interdefinabilidade dos ∃,∀ **)

Theorem interdefinabilidade_existe_paratodo1 : forall (A : Type)(phi : A -> Prop), (exists ( x: A ), phi x) -> ~(forall (x : A), ~phi x).
Proof.
  intros A phi Hex_px Hfx_npx. destruct Hex_px as (a, Hpa).
  apply (Hfx_npx a) in Hpa as Hfalse. assumption.
Qed.

Theorem interdefinabilidade_existe_paratodo2_with_lem : lem -> forall (A : Type)(a : A)(phi : A -> Prop), ~(forall (x : A), ~phi x) -> (exists ( x: A ), phi x).
Proof.
  intros Hlem A a phi Hnfx_npx.
  destruct (Hlem (forall x, phi x)) as [Hfx_px | Hnfx_px].
  - exists a. exact (Hfx_px a).
  - destruct (Hlem (exists x, ~(phi x))) as [Hex_npx | Hnex_npx].
    + admit.
    +
  exists a.
Abort.

Theorem interdefinabilidade_existe_paratodo3 : forall (A : Type)(phi : A -> Prop), (forall ( x: A ), phi x) -> ~(exists (x : A), ~phi x).
Proof.
  intros A phi Hfx_px Hex_npx. destruct Hex_npx as (a, Hnpa).
  apply Hnpa in Hfx_px as Hfalse. assumption.
Qed.

Theorem interdefinabilidade_existe_paratodo4_with_lem : lem -> forall (A : Type)(phi : A -> Prop), ~(exists (x : A), ~phi x) -> (forall ( x: A ), phi x).
Proof.
  intros Hlem A phi Hnex_npx a. destruct (Hlem (phi a)) as [Hpa | Hnpa].
  - assumption.
  - assert (Hex_npx: exists (x : A), ~phi x).
    * exists a. assumption.
    * apply Hnex_npx in Hex_npx as Hfalse. contradiction.
Qed.


(** 10. Proposições de distributividade de quantificadores **)

Theorem distirbutividade_quantificadores1 : forall (A : Type)(phi psi : A -> Prop),
  (exists (x : A), phi x /\ psi x) -> (exists (x : A), phi x) /\ (exists (x : A), psi x).
Proof.
  intros A phi psi Hex__phx_and_psx. destruct Hex__phx_and_psx as (a, Hpha_and_psa).
  destruct Hpha_and_psa as (Hpha, Hpsa).
  split.
  - exists a. assumption.
  - exists a. assumption.
Qed.

Theorem distirbutividade_quantificadores3 : forall (A : Type)(phi psi : A -> Prop),
  (exists (x : A), phi x \/ psi x) -> (exists (x : A), phi x) \/ (exists (x : A), psi x).
Proof.
  intros A phi psi Hex_phx_or_psx.
  destruct Hex_phx_or_psx as (a, Hpha_or_psa).
  destruct Hpha_or_psa as [Hpha | Hpsa].
  - left. exists a. exact Hpha.
  - right. exists a. exact Hpsa.
Qed.

Theorem distirbutividade_quantificadores4 : forall (A : Type)(phi psi : A -> Prop),
  (exists (x : A), phi x) \/ (exists (x : A), psi x) -> (exists (x : A), phi x \/ psi x).
Proof.
  intros A phi psi Hex_phx__or__ex_psx.
  destruct Hex_phx__or__ex_psx as [Hex_phx | Hex_psx].
  - destruct Hex_phx as (a, Hpha).
    exists a. left. exact Hpha.
  - destruct Hex_psx as (a, Hpsa).
    exists a. right. exact Hpsa.
Qed.

Theorem distirbutividade_quantificadores5 : forall (A : Type)(phi psi : A -> Prop),
  (forall (x : A), phi x /\ psi x) -> (forall (x : A), phi x) /\ (forall (x : A), psi x).
Proof.
  intros A phi psi Hfx_phx_and_psix.
  split.
  - intros a. destruct (Hfx_phx_and_psix a) as (Hpha, Hpsa).
    exact Hpha.
  - intros a. destruct (Hfx_phx_and_psix a) as (Hpha, Hpsa).
    exact Hpsa.
Qed.

Theorem distirbutividade_quantificadores6 : forall (A : Type)(phi psi : A -> Prop),
  (forall (x : A), phi x) /\ (forall (x : A), psi x) -> (forall (x : A), phi x /\ psi x).
Proof.
  intros A phi psi Hfx_phx__and__fx_psx x.
  destruct Hfx_phx__and__fx_psx as (Hfx_phx, Hfx_psx).
  split.
  - exact (Hfx_phx x).
  - exact (Hfx_psx x).
Qed.

Theorem distirbutividade_quantificadores8 : forall (A : Type)(phi psi : A -> Prop),
  (forall (x : A), phi x) \/ (forall (x : A), psi x) -> (forall (x : A), phi x \/ psi x).
Proof.
  intros A phi psi Hfx_phx__or__fx_psx x.
  destruct Hfx_phx__or__fx_psx as [Hfx_phx | Hfx_psx].
  - left. exact (Hfx_phx x).
  - right. exact (Hfx_psx x).
Qed.

(** 1. (Cont) Proposições de contraposição **)

Theorem contraopositiva1 : forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HP_imp_Q HnQ HP. apply HP_imp_Q in HP as HQ.
  apply HnQ in HQ as Hfalse. assumption.
Qed.

Theorem contrapositiva2_with_lem : lem -> forall (P Q : Prop), (~Q -> ~P) -> (P -> Q).
Proof.
  intros Hlem P Q HnQ_imp_nP HP. apply (doubleneg_elim_with_lem Hlem Q).
  intros HnQ. apply HnQ_imp_nP in HnQ as HnP.
  apply HnP in HP as Hfalse. contradiction.
Qed.


