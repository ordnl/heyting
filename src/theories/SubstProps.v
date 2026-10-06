(*# Substitution properties #*)
(*; Here we build prove some properties of De Bruijn indices ;*)
Require Import HA.Autosubst.core.
Require Import HA.Autosubst.unscoped.
Require Import HA.Autosubst.Formulas.
From Stdlib Require Import FinFun. (* Injectivity from FinFun *)

(** Our goal is to prove the Injectivity of (subst_form f)
    for various substitutions.

    In general, (Injective f) does not imply (Injective (subst_term f))

    e.g.:
        If (f 0) = const, then:
        - (subst_term f (var_term 0)) = const
        - (subst_term f const) = const

    Instead, we rely on the following property:

    Def: A substitution f is var-to-var when:
         ∀ n ∃ m ( (f n) = (var_term m) )

    Def: A substitution f is var-perm when:
         f is var-to-var AND injective.

    Thm: If f is var-perm,
         then (subst_term f) is injective
 **)

(*## Variable Permutations ##*)

Definition VtV (σ : nat -> term) :=
  forall n, exists m, (σ n) = (var_term m).
Transparent VtV.

Definition VPerm (σ : nat -> term) :=
  (Injective σ) /\ (VtV σ).
Transparent VPerm.

(** VPerm of shift_term **)
Definition shift_term := (funcomp (var_term) shift).

Lemma inj_shift_term : Injective shift_term.
Proof. unfold Injective; induction x,y; asimpl; intros; inversion H; easy. Qed.

Lemma vtv_shift_term : VtV shift_term.
Proof. unfold VtV; induction n; [ exists 1 | exists (S (S n)) ]; easy. Qed.

Corollary vperm_shift_term : VPerm shift_term.
Proof. exact (conj (inj_shift_term) (vtv_shift_term)). Qed.

(** VPerm implies Injective subst_term **)
Theorem vperm_is_inj_subst_term σ : VPerm σ -> Injective (subst_term σ).
Proof.
  intros [HInj HVtV].
  unfold Injective, VtV in *.
  induction x, y; intros H; inversion H; simpl in *;
    try (specialize (HVtV n); destruct HVtV as [n0 Heq];
         rewrite Heq in H; discriminate);
    try easy.
  - apply HInj in H; subst; easy.
  - apply IHx in H1; subst; easy.
  - apply IHx1 in H1; apply IHx2 in H2; subst; easy.
  - apply IHx1 in H1; apply IHx2 in H2; subst; easy.
Qed.

Corollary inj_subst_term_shift : Injective (subst_term shift_term).
Proof. apply (vperm_is_inj_subst_term shift_term vperm_shift_term). Qed.

(** VPerm of up_f **)
Fixpoint upN (n : nat) (σ : nat -> term) :=
  match n with
  | 0 => σ
  | S n => up_term_term (upN n σ)
  end.

Lemma vtv_up_f σ : VtV σ -> VtV (up_term_term σ).
Proof.
  intros HVf.
  unfold VtV.
  induction n.
  - exists 0; easy.
  - specialize (HVf n).
    destruct HVf.
    exists (S x).
    asimpl.
    change (funcomp (subst_term (funcomp var_term shift)) σ n)
      with (subst_term shift_term (σ n)).
    rewrite H.
    asimpl.
    easy.
Qed.

Lemma vtv_upN_f n σ : VtV σ -> VtV (upN n σ).
Proof.
  intros HVf.
  unfold VtV.
  induction n; intros; simpl.
  - apply HVf.
  - apply vtv_up_f; unfold VtV; exact IHn.
Qed.
    
Lemma var_0_neq_shift t : var_term 0 <> (subst_term shift_term t).
Proof. induction t; discriminate. Qed.

Lemma inj_upN_f n f : Injective f -> Injective (upN n f).
Proof.
  revert n f.
  induction n.
  - easy.
  - intros f HInj.
    unfold Injective.
    induction x, y; intros H; inversion H; asimpl.
    + easy.
    + apply var_0_neq_shift in H1; easy.
    + symmetry in H1; apply var_0_neq_shift in H1; easy.
    + apply inj_subst_term_shift,(IHn f HInj) in H1; subst; easy.
Qed.

Corollary vperm_upN_f n σ : VPerm σ -> VPerm (upN n σ).
Proof.
  intros HVP. destruct HVP as [HInj HVtV].
  apply (conj (inj_upN_f n σ HInj) (vtv_upN_f n σ HVtV)).
Qed.

(** VPerm implies Injective subst_form **)
Lemma vperm_is_inj_subst_form σ : VPerm σ -> Injective (subst_form σ).
Proof.
  intros HVp.
  unfold Injective.
  intros.
  revert x y σ HVp H.
  induction x, y; intros; inversion H; try easy.
  - apply (vperm_is_inj_subst_term σ HVp) in H1.
    apply (vperm_is_inj_subst_term σ HVp) in H2.
    subst; reflexivity.
  - apply IHx1 in H1; apply IHx2 in H2; subst; easy.
  - apply IHx1 in H1; apply IHx2 in H2; subst; easy.
  - apply IHx1 in H1; apply IHx2 in H2; subst; easy.
  - apply (IHx y (up_term) (vperm_upN_f 1 σ HVp)) in H1; subst; easy.
  - apply (IHx y (up_term) (vperm_upN_f 1 σ HVp)) in H1; subst; easy.
Qed.

Lemma inj_subst_form_shift : Injective (subst_form shift_term).
Proof. apply (vperm_is_inj_subst_form shift_term vperm_shift_term). Qed.

Lemma inj_subst_form_upN_shift n : Injective (subst_form (upN n shift_term)).
Proof. apply (vperm_is_inj_subst_form (upN n shift_term)).
       apply (vperm_upN_f n (shift_term) vperm_shift_term). Qed.

Lemma inj_subst_form_up_shift : Injective (subst_form (up_term_term shift_term)).
Proof. apply (inj_subst_form_upN_shift 1). Qed.

