module

public import Mathlib
public import Formalism.ThetaSupremumBounds.Bundle0001
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.ThetaSupremumBounds.DivIneqExplicit6
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DescendedNorm

@[expose] public section

open Finset NumberField
open scoped Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)

namespace CB

theorem card_sigma_le {AA : Type} [Fintype AA] (Cl : AA → Type) [∀ a, Fintype (Cl a)] (h : ℝ)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) :
    (Fintype.card (Σ a, Cl a) : ℝ) ≤ (Fintype.card AA : ℝ) * h := by
  rw [Fintype.card_sigma]
  push_cast
  calc (∑ a, (Fintype.card (Cl a) : ℝ)) ≤ ∑ _a : AA, h := Finset.sum_le_sum (fun a _ => hh a)
    _ = (Fintype.card AA : ℝ) * h := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem const_le {AA AA' : Type} [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (h h' t : ℝ) (ht : 0 ≤ t)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) (hh' : ∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') :
    ((Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ)) * t ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' t := by
  have h1 := card_sigma_le Cl h hh
  have h2 := card_sigma_le Cl' h' hh'
  have h3 : ((Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ)) ≤
      ((Fintype.card AA : ℝ) * h) * ((Fintype.card AA' : ℝ) * h') :=
    mul_le_mul h1 h2 (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) h1)
  have h4 := mul_le_mul_of_nonneg_right h3 ht
  unfold cbSq
  calc _ ≤ _ := h4
    _ = _ := by ring

theorem cbSq_nonneg {AA AA' : Type} [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (h h' t : ℝ) (ht : 0 ≤ t)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) (hh' : ∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') :
    0 ≤ cbSq (Fintype.card AA) (Fintype.card AA') h h' t :=
  le_trans (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ht)
    (const_le Cl Cl' h h' t ht hh hh')

theorem pos_pair {a b : ℝ} (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a ∧ 0 < b := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h' | h'
  · exact h'
  · exact absurd hb (not_le.mpr h'.2)

open Formalism.DivisionValues.OperatorNormFrames in
theorem nrm_le_sqrt {a b : ℕ} (X : Matrix (Fin a) (Fin a) ℂ) (X' : Matrix (Fin b) (Fin b) ℂ)
    (hX : IsUnit X.det) (M : Matrix (Fin b) (Fin a) ℂ) (Bd : ℝ) (hB : 0 ≤ Bd)
    (h : ∀ y, fnorm X' (M.mulVec y) ^ 2 ≤ Bd * fnorm X y ^ 2) :
    nrm (X'⁻¹ * M * X) ≤ Real.sqrt Bd := by
  unfold nrm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun z => ?_)
  have key : ∀ (A' : Matrix (Fin b) (Fin a) ℂ),
      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A')) z‖ =
        Formalism.HermitianLatticesTheory.cnorm (A'.mulVec (fun i => z i)) := by
    intro A'
    rw [EuclideanSpace.norm_eq]
    rfl
  have hz : ‖z‖ = Formalism.HermitianLatticesTheory.cnorm (fun i => z i) := by
    rw [EuclideanSpace.norm_eq]
    rfl
  rw [key, hz]
  have e1 : (X'⁻¹ * M * X).mulVec (fun i => z i) = X'⁻¹.mulVec (M.mulVec (X.mulVec (fun i => z i))) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have e2 : X⁻¹.mulVec (X.mulVec (fun i => z i)) = (fun i => z i) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul X hX, Matrix.one_mulVec]
  have hy := h (X.mulVec (fun i => z i))
  unfold Formalism.DivisionValues.fnorm at hy
  rw [e2, ← e1] at hy
  have c0 : 0 ≤ Formalism.HermitianLatticesTheory.cnorm ((X'⁻¹ * M * X).mulVec (fun i => z i)) := Real.sqrt_nonneg _
  have c1 : 0 ≤ Formalism.HermitianLatticesTheory.cnorm (fun i => z i) := Real.sqrt_nonneg _
  rw [← Real.sqrt_sq c0, ← Real.sqrt_sq c1, ← Real.sqrt_mul hB]
  exact Real.sqrt_le_sqrt hy

end CB

open CB

theorem sharp_norm : SharpNorm := by
  intro AA AA' _ _ Cl Cl' _ _ A B _ _ _ _ γ γ' ε T h h' tmax hγ hγ' hε hT ht hh hh'
  have hPQ : (Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ) * tmax ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax :=
    const_le Cl Cl' h h' tmax ht hh hh'
  have hcb0 : 0 ≤ cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax :=
    cbSq_nonneg Cl Cl' h h' tmax ht hh hh'
  have hsumγ : ∑ p, γ p ≤ (Fintype.card (Σ a, Cl a) : ℝ) := by
    calc ∑ p, γ p ≤ ∑ _p : (Σ a, Cl a), (1 : ℝ) := Finset.sum_le_sum (fun p _ => (hγ p).2)
      _ = (Fintype.card (Σ a, Cl a) : ℝ) := by simp
  have key : ∀ G : (Σ a, Cl a) → A, ∀ q, ‖liftOp γ ε T G q‖ ^ 2 ≤
      tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) := by
    intro G q
    have h1 : ‖liftOp γ ε T G q‖ ≤ ∑ p, γ p * (Real.sqrt tmax * ‖G p‖) := by
      unfold liftOp
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun p _ => ?_))
      rw [norm_smul, norm_mul, hε p q, mul_one, Complex.norm_real, Real.norm_of_nonneg (hγ p).1.le]
      refine mul_le_mul_of_nonneg_left ?_ (hγ p).1.le
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact le_of_eq_of_le (abs_of_nonneg (norm_nonneg _)).symm (Real.abs_le_sqrt (hT p q))
    have h2 : (∑ p, γ p * (Real.sqrt tmax * ‖G p‖)) = Real.sqrt tmax * ∑ p, γ p * ‖G p‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    have h3 : (∑ p, γ p * ‖G p‖) ^ 2 ≤ (∑ p, γ p) * ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _ (fun p _ => (hγ p).1.le)
        (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _)) (fun p _ => by ring)
    have hS : 0 ≤ ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _))
    rw [h2] at h1
    calc ‖liftOp γ ε T G q‖ ^ 2 ≤ (Real.sqrt tmax * ∑ p, γ p * ‖G p‖) ^ 2 :=
          sq_le_sq' (by linarith [norm_nonneg (liftOp γ ε T G q)]) h1
      _ = tmax * (∑ p, γ p * ‖G p‖) ^ 2 := by rw [mul_pow, Real.sq_sqrt ht]
      _ ≤ tmax * ((∑ p, γ p) * ∑ p, γ p * ‖G p‖ ^ 2) := mul_le_mul_of_nonneg_left h3 ht
      _ ≤ tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsumγ hS) ht
  have bound : ∀ G : (Σ a, Cl a) → A, (∑ q, γ' q * ‖liftOp γ ε T G q‖ ^ 2) ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' tmax * ∑ p, γ p * ‖G p‖ ^ 2 := by
    intro G
    have hS : 0 ≤ ∑ p, γ p * ‖G p‖ ^ 2 :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (hγ p).1.le (sq_nonneg _))
    calc (∑ q, γ' q * ‖liftOp γ ε T G q‖ ^ 2)
        ≤ ∑ _q : (Σ b, Cl' b), tmax * ((Fintype.card (Σ a, Cl a) : ℝ) * ∑ p, γ p * ‖G p‖ ^ 2) :=
          Finset.sum_le_sum (fun q _ =>
            le_trans (mul_le_of_le_one_left (sq_nonneg _) (hγ' q).2) (key G q))
      _ = (Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ) * tmax *
            ∑ p, γ p * ‖G p‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hPQ hS
  refine ⟨bound, ?_⟩
  unfold liftNormSq
  exact csInf_le ⟨0, fun X hX => hX.1⟩ ⟨hcb0, bound⟩

open Formalism.DivisionValues.OperatorNormFrames in
theorem chain_coupled_bound : ChainCB := by
  intro K _ _ _ m c Xc Kj AA Cl _ _ W _ _ γ Φ ε T hcl tmax hyp kU hkU
  obtain ⟨hX, hγ, hΦ, hint, hε, hT, ht0, hh⟩ := hyp
  have hnn : ∀ j v, 0 ≤ cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v) := fun j v =>
    cbSq_nonneg (Cl j.castSucc) (Cl j.succ) _ _ _ (ht0 j v) (hh _) (hh _)
  have hop : ∀ j v, Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) ≤ kU j v := by
    intro j v
    rw [hkU, opNormAt_mulVecLin]
    refine nrm_le_sqrt _ _ (hX _ v) _ _ (hnn j v) fun y => ?_
    rw [← hΦ, ← hΦ, hint]
    exact (sharp_norm (AA j.castSucc) (AA j.succ) (Cl j.castSucc) (Cl j.succ) (W j.castSucc v)
      (W j.succ v) (γ j.castSucc) (γ j.succ) (ε j v) (T j v) (hcl j.castSucc) (hcl j.succ) (tmax j v)
      (hγ _) (hγ _) (hε j v) (hT j v) (ht0 j v) (hh _) (hh _)).1 _
  have hk2 : ∀ j v, kU j v ^ 2 = cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
      (hcl j.castSucc) (hcl j.succ) (tmax j v) := fun j v => by
    rw [hkU, Real.sq_sqrt (hnn j v)]
  refine ⟨hop, hk2, fun hne => ?_⟩
  have key := (Formalism.DivisionValues.composition_norm_at_place K m c Xc hX Kj).1
  have hpos : ∀ v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c 0))) (Xc 0)
      (Pi.basisFun K (Fin (c (Fin.last m)))) (Xc (Fin.last m)) v
        (Matrix.mulVecLin (chainMat Kj (Fin.last m))) := fun v =>
    Formalism.HN.PlaceOperatorNorms.opNormAt_pos _ _ _ _ (hX _) (hX _) v _ (mulVecLin_ne_zero _ hne)
  have hjpos : ∀ j v, 0 < Formalism.HN.opNormAt (Pi.basisFun K (Fin (c j.castSucc))) (Xc j.castSucc)
      (Pi.basisFun K (Fin (c j.succ))) (Xc j.succ) v (Matrix.mulVecLin (Kj j)) := by
    intro j v
    have hprod := (hpos v).trans_le (key v)
    exact lt_of_le_of_ne (opNormAt_nonneg _ _ _ _ _ _)
      (Finset.prod_ne_zero_iff.1 hprod.ne' j (Finset.mem_univ j)).symm
  have hfac : ∀ j v, 0 < (Fintype.card (AA j.castSucc) : ℝ) ∧ 0 < (Fintype.card (AA j.succ) : ℝ) ∧
      0 < hcl j.castSucc ∧ 0 < hcl j.succ ∧ 0 < tmax j v := by
    intro j v
    have h0 : 0 < cbSq (Fintype.card (AA j.castSucc)) (Fintype.card (AA j.succ))
        (hcl j.castSucc) (hcl j.succ) (tmax j v) := by
      rw [← hk2]; exact pow_pos ((hjpos j v).trans_le (hop j v)) 2
    rw [cbSq] at h0
    obtain ⟨h1, h2⟩ := pos_pair h0 (ht0 j v)
    rw [mul_comm] at h1
    obtain ⟨h3, h4⟩ := pos_pair h1 (by positivity)
    obtain ⟨h5, h6⟩ := pos_pair h4 (Nat.cast_nonneg _)
    obtain ⟨a⟩ := Fintype.card_pos_iff.1 (Nat.cast_pos.1 h6)
    obtain ⟨h7, h8⟩ := pos_pair h3 ((Nat.cast_nonneg _).trans (hh j.succ a))
    exact ⟨h5, h6, h7, h8, h2⟩
  refine ⟨hfac, fun j v => ?_, fun v => ?_, fun v => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hfac j v
    rw [hk2, cbSq, Real.log_mul (by positivity) h5.ne', Real.log_mul (by positivity) (by positivity),
      Real.log_mul h1.ne' h2.ne', Real.log_mul h3.ne' h4.ne']
    ring
  · rw [← Real.log_prod (fun j _ => pow_ne_zero 2 (hjpos j v).ne'), Finset.prod_pow]
    exact Real.log_le_log (pow_pos (hpos v) 2) (pow_le_pow_left₀ (hpos v).le (key v) 2)
  · exact Finset.sum_le_sum fun j _ =>
      Real.log_le_log (pow_pos (hjpos j v) 2) (pow_le_pow_left₀ (hjpos j v).le (hop j v) 2)
  · rw [Formalism.HN.htMap]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) (by positivity)
    refine le_trans ?_ (Finset.sum_le_sum fun j _ =>
      Real.log_le_log (pow_pos (hjpos j v) 2) (pow_le_pow_left₀ (hjpos j v).le (hop j v) 2))
    rw [← Real.log_prod (fun j _ => pow_ne_zero 2 (hjpos j v).ne'), Finset.prod_pow]
    exact Real.log_le_log (pow_pos (hpos v) 2) (pow_le_pow_left₀ (hpos v).le (key v) 2)

namespace CB

end CB

namespace CB

end CB

end Formalism.DimensionVariation
