

Definition phi2 (x : Set) (y : Set) : Prop := False.

(**Theorem teste : (forall ( y: Set ), exists (x : Set), ~(phi2 x y)) <-> ~(exists (y : Set), forall (x : Set), phi2 x y).
Proof.
  unfold iff.
  split.
  - intros Hfy_ex_npxy. unfold not. intro Hey_fx_pxy. destruct Hey_fx_pxy as (y, Hfx_pxy).
    destruct (Hfx_pxy y).
  - intros Hey_fx_pxy_if y. unfold not in Hey_fx_pxy_if. intro Hex_pxy.
    assert(Hex_px: exists x: Set, phi x).
      * exists x. assumption.
      * apply Hex_px_if in Hex_px. contradiction.
Qed.**)

Theorem teste2 : (forall ( y: Set ), ~(forall (x : Set), phi2 x y)) <-> ~(exists (y : Set), forall (x : Set), phi2 x y).
Proof.
  unfold iff. split.
  - intros Hfy_nfx_pxy Hey_fx_pxy. destruct Hey_fx_pxy as (y, Hfx_pxy).
    destruct (Hfy_nfx_pxy y). intros x. destruct (Hfx_pxy x).
  - intros Hney_fx_pxy y Hfx_pxy. destruct Hney_fx_pxy. exists y. assumption.
Qed.
(**
Theorem teste3 : (forall ( y: Set ), ~(forall (x : Set), phi2 x y)) <-> (forall ( y: Set ), exists (x : Set), ~(phi2 x y)).
Proof.
  unfold iff. split.
  - intros Hfy_nfx_pxy y. destruct (Hfy_nfx_pxy y). intros x. 
    destruct (Hfy_nfx_pxy y). intros x. destruct (Hfx_pxy x).
  - intros Hney_fx_pxy y Hfx_pxy. destruct Hney_fx_pxy. exists y. assumption.
Qed. **)