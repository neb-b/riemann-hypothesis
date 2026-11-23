module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.EvalEqZeroOfCommonZero

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.TXgzChowMahlerE0reduce
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

theorem PositivityTheory.Xgn.t_xgz_chow_mahler_e0reduce : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S → IsSigmaCompact S →
  ∀ T : ℝ≥0∞ → ℝ≥0∞, Measurable T →
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  intro n e S hS hσ T hT
  have hG : Measurable fun π : Fin (e + 1) → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin (e + 1) → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hC : Measurable (fun p : (Fin (e + 1) → Fin n → ℂ) × EuclideanSpace ℂ (Fin (e + 1)) =>
      T (cntOver S p.1 p.2)) := hT.comp (_root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.measurable_cntOver n (e + 1) S hσ)
  have hF : Measurable (Function.uncurry fun (π : Fin (e + 1) → Fin n → ℂ)
      (w : EuclideanSpace ℂ (Fin (e + 1))) => matGauss π * T (cntOver S π w)) :=
    (hG.comp measurable_fst).mul hC
  have h1 : ∀ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1),
        matGauss π * T (cntOver S π w) := by
    intro π
    rw [lintegral_const_mul' _ _ (by unfold matGauss; exact ENNReal.ofReal_ne_top)]
  have h0 : ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)), w ≠ 0 := by
    rw [ae_iff]
    simp
  simp_rw [h1]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  rw [lintegral_congr_ae ((ae_restrict_of_ae h0).mono fun w hw => _root_.GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv.lintegral_matGauss_cntOver n e S hS w hw T),
    setLIntegral_const, mul_comm]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibrefactor
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor

theorem pair_eq {n : ℕ} (h : HermNorm n) (p : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, ((h.mat)⁻¹ *ᵥ p) j * h.pointOf y j = ∑ j, p j * y j := by
  have h1 : ((h.mat)⁻¹ *ᵥ p) ⬝ᵥ (h.matᵀ *ᵥ fun i => y i) = p ⬝ᵥ fun i => y i := by
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ h.isUnit_det, Matrix.one_mulVec, dotProduct_comm]
  exact h1

theorem pointOf_inj {n : ℕ} (h : HermNorm n) : Function.Injective h.pointOf := by
  intro y y' hy
  ext i
  have h1 := pair_eq h (Pi.single i 1) y
  have h2 := pair_eq h (Pi.single i 1) y'
  rw [hy, h2] at h1
  simpa [Pi.single_apply] using h1.symm

theorem row_zero {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} {π : Fin (e + 1) → Fin n → ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ fibrePts S π) : ∑ j, π 0 j * y j = 1 := by
  have h1 : linProj π y 0 = firstCoordVec (e + 1) 0 := by rw [hy.2]
  simpa [linProj, firstCoordVec] using h1

theorem row_succ {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} {π : Fin (e + 1) → Fin n → ℂ}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ fibrePts S π) (i : Fin e) :
    ∑ j, π i.succ j * y j = 0 := by
  have h1 : linProj π y i.succ = firstCoordVec (e + 1) i.succ := by rw [hy.2]
  simpa [linProj, firstCoordVec] using h1

end PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor

open PositivityTheory.Xgn.A_xgz_chow_mahler_fibrefactor in
theorem PositivityTheory.Xgn.t_xgz_chow_mahler_fibrefactor : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (π : Fin (e + 1) → Fin n → ℂ) (u₀ : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (fibrePts (coneSet h W) π).encard = δ →
  eval (consGroup u₀ (nrmGroups h e (coefRows h π))) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u (nrmGroups h e (coefRows h π))) g =
      c * ∏ᶠ y ∈ fibrePts (coneSet h W) π, ∑ j, u j * h.pointOf y j := by
  classical
  intro n e δ h W g π u₀ _ hch hmh hcard hne
  have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hcard
  have hc : hfin.toFinset.card = δ := by
    have h1 := hfin.encard_eq_coe_toFinset_card
    rw [hcard] at h1
    exact_mod_cast h1.symm
  have hone : ∀ y ∈ fibrePts (coneSet h W) π,
      ∑ j, ((h.mat)⁻¹ *ᵥ π 0) j * h.pointOf y j = 1 := fun y hy => by
    rw [pair_eq, row_zero hy]
  obtain ⟨c, hc0, hcu⟩ := _root_.ModelDimension.chow_form_product_formula n e δ W g (nrmGroups h e (coefRows h π))
    (hfin.toFinset.image h.pointOf) u₀ hch hmh
    (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      rw [Set.Finite.mem_toFinset] at hy
      refine ⟨fun h0 => ?_, hy.1, fun i => ?_⟩
      · have h1 := hone y hy
        rw [h0] at h1
        simp at h1
      · have h1 := pair_eq h (π i.succ) y
        rw [row_succ hy] at h1
        simp only [nrmGroups, coefRows, mul_assoc]
        rw [← Finset.mul_sum, h1, mul_zero])
    (by
      intro x hx x' hx' t ht
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hx'
      rw [Set.Finite.mem_toFinset] at hy hy'
      have h1 := hone y hy
      have h2 := hone y' hy'
      rw [ht] at h2
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ t] at h2
      rw [← Finset.mul_sum, h1, mul_one] at h2
      rw [ht, h2, one_smul])
    (by rw [Finset.card_image_of_injective _ (pointOf_inj h), hc]) hne
  refine ⟨c, hc0, fun u => ?_⟩
  rw [hcu u, Finset.prod_image (fun a _ b _ hab => pointOf_inj h hab),
    finprod_mem_eq_finite_toFinset_prod _ hfin]
end

