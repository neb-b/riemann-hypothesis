module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

@[expose] public section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

local notation "derivative" =>
  (fun (R : Type) [CommSemiring R] (f : R⟦X⟧) => PowerSeries.derivative f)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cpTransportedTaylorSeriesInChart_ringHom_laws : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧), constantCoeff ℓ = 0 → (∀ F G : ℂ → ℂ, AnalyticAt ℂ F 0 → AnalyticAt ℂ G 0 → hat ι ℓ (fun z => F z + G z) = hat ι ℓ F + hat ι ℓ G ∧ hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G ∧ ((∀ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z) → hat ι ℓ F = hat ι ℓ G) ∧ (coeff 1 ℓ ≠ 0 → hat ι ℓ F = hat ι ℓ G → F =ᶠ[𝓝 0] G)) ∧ (∀ c : ℂ, hat ι ℓ (fun _ => c) = C (ι c)) ∧ hat ι ℓ (fun z => z) = ℓ ∧ (∀ F : ℂ → ℂ, constantCoeff (hat ι ℓ F) = ι (F 0)) ∧ (∀ F : ℂ → ℂ, AnalyticAt ℂ F 0 → derivative ℂ_[q] (hat ι ℓ F) = derivative ℂ_[q] ℓ * hat ι ℓ (deriv F)) ∧ (∀ (F : ℂ → ℂ) (α : ℂ), AnalyticAt ℂ F 0 → hat ι ℓ (fun z => F (α * z)) = hat ι (C (ι α) * ℓ) F) ∧ ∀ (F : ℂ → ℂ) (h : ℂ_[q]⟦X⟧), constantCoeff h = 0 → (hat ι ℓ F).subst h = hat ι (ℓ.subst h) F := by
  intro q _ ι ℓ hℓ
  have hs : HasSubst ℓ := HasSubst.of_constantCoeff_zero' hℓ
  refine ⟨fun F G hF hG => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hat, TaylorRead.tay_add hF hG, map_add, subst_add hs]
  · simp only [hat, TaylorRead.tay_mul hF hG, map_mul, subst_mul hs]
  · intro h
    have hFG : F =ᶠ[𝓝 0] G := (hF.frequently_eq_iff_eventually_eq hG).mp h.frequently
    simp only [hat, TaylorRead.tay_congr hFG]
  · intro h1 h
    apply TaylorRead.eventuallyEq_of_tay_eq hF hG
    exact PowerSeries.map_injective (ι : ℂ →+* ℂ_[q]) ι.injective
      (TaylorRead.subst_injective_of hℓ h1 h)
  · intro c
    simp only [hat, TaylorRead.tay_const, map_C, subst_C]
    rfl
  · simp only [hat, TaylorRead.tay_id, map_X, subst_X hs]
  · intro F
    simp only [hat]
    rw [TaylorRead.constantCoeff_subst_of hℓ, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
    simp [tay]
  · intro F _
    have hderiv : PowerSeries.derivative (tay F) = tay (deriv F) := by
      ext n
      simp only [coeff_derivative, tay, coeff_mk, iteratedDeriv_succ', Nat.factorial_succ]
      push_cast
      field_simp [Nat.factorial_ne_zero]
    have hmap : PowerSeries.derivative (PowerSeries.map (ι : ℂ →+* ℂ_[q]) (tay F)) =
        PowerSeries.map (ι : ℂ →+* ℂ_[q]) (PowerSeries.derivative (tay F)) := by
      ext n
      simp [coeff_derivative]
    simp only [hat]
    rw [derivative_subst hs, hmap, hderiv, mul_comm]
  · intro F α _
    have hmap : PowerSeries.map (ι : ℂ →+* ℂ_[q]) (rescale α (tay F)) =
        rescale (ι α) (PowerSeries.map (ι : ℂ →+* ℂ_[q]) (tay F)) := by
      ext n
      simp [coeff_rescale]
    simp only [hat]
    rw [TaylorRead.tay_comp_mul, hmap, rescale_eq_subst,
      subst_comp_subst_apply (HasSubst.smul_X' _) hs, subst_smul hs, subst_X hs, smul_eq_C_mul]
  · intro F h hh
    simp only [hat]
    rw [subst_comp_subst_apply hs (HasSubst.of_constantCoeff_zero' hh)]
