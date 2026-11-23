module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdCore

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.WBL.NIS

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL PI.WBL.FSW

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp]

theorem hs_one {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN : Measure (Mt k r)} {σ : Mx k r → (H →L[ℂ] H)}
    (hGr : Cv.GrpF k r z) (hSg : Cv.SigU σ) (hPi : Cv.PiU z π) (hPs : Cv.PsiF k r z c) (hM : Cv.MeasF z π μW μN)
    {u v : H} (ξ : Wp) {x : Mx k r} (hx : x ∈ UH (Hpk k r))
    (hint : Integrable (beF z c π σ (σ x u) v) (μW.prod μN)) :
    Integrable (fun p => Fx z c π μW μN σ u v ξ (sM p * x)) (μW.prod μN) ∧
      ((‖Aop z c π μW μN σ u v x ξ‖ ^ 2 : ℝ) : ℂ) = ∫ p, Fx z c π μW μN σ u v ξ (sM p * x) ∂(μW.prod μN) := by
  set A : Wp →L[ℂ] Wp := Aop z c π μW μN σ u v x with hA
  have hiso : ∀ b ∈ UWset k r z, ∀ y y' : Wp, ⟪π b y, π b y'⟫_ℂ = ⟪y, y'⟫_ℂ := by
    intro b hb y y'
    let T : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (π b : Wp →ₗ[ℂ] Wp), norm_map' := hPi.2.2 b hb }
    exact T.inner_map_map y y'
  have hadj : ∀ b ∈ UWset k r z, ∀ y y' : Wp, ⟪π b y, y'⟫_ℂ = ⟪y, π b⁻¹ y'⟫_ℂ := by
    intro b hb y y'
    have hbinv : b⁻¹ ∈ UWset k r z := hGr.2.2.1 b hb
    have h1 : b * b⁻¹ = 1 := (hGr.2.1 b hb.1).1
    have h2 : π b (π b⁻¹ y') = y' := by
      have h3 := hPi.2.1 b hb b⁻¹ hbinv
      rw [h1, hPi.1] at h3
      have h4 := congrArg (fun T : Wp →L[ℂ] Wp => T y') h3
      simpa using h4.symm
    calc ⟪π b y, y'⟫_ℂ = ⟪π b y, π b (π b⁻¹ y')⟫_ℂ := by rw [h2]
      _ = ⟪y, π b⁻¹ y'⟫_ℂ := hiso b hb y _
  have hc : ∀ y y' : Wp, star ⟪y, y'⟫_ℂ = ⟪y', y⟫_ℂ := fun y y' => inner_conj_symm y' y
  have key : ∀ p : Mt k r × Mt k r, Matrix.of p.1 ∈ UWset k r z → Matrix.of p.2 ∈ Nset k r →
      Fx z c π μW μN σ u v ξ (sM p * x) = ⟪A ξ, beF z c π σ (σ x u) v p ξ⟫_ℂ := by
    intro p h1 h2
    have hmul : sM p ∈ UH (Hpk k r) := hGr.1 _ h1.1 _ h2.1
    have hσ' : σ (sM p * x) u = σ (Matrix.of p.1 * Matrix.of p.2) (σ x u) := by
      rw [hSg.2.1 _ hmul _ hx]; rfl
    have heq : Aop z c π μW μN σ u v (sM p * x) =
        (psi k r z c (Matrix.of p.2) • π (Matrix.of p.1)).comp A := by
      show be z c π μW μN σ (σ (sM p * x) u) v = _
      rw [hσ']
      exact be_equiv_of_int hGr hSg hPi hPs hM hint h1 h2
    rw [show Fx z c π μW μN σ u v ξ (sM p * x) =
        ⟪v, σ (sM p * x) u⟫_ℂ * star ⟪ξ, Aop z c π μW μN σ u v (sM p * x) ξ⟫_ℂ from rfl]
    rw [show beF z c π σ (σ x u) v p = (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) (σ x u)⟫_ℂ *
        star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ from rfl]
    rw [heq, hσ', ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, inner_smul_right, inner_smul_right, star_mul', hc,
      ← hadj _ h1]
    ring
  have hae : (fun p => Fx z c π μW μN σ u v ξ (sM p * x)) =ᵐ[μW.prod μN]
      fun p => ⟪A ξ, beF z c π σ (σ x u) v p ξ⟫_ℂ := by
    filter_upwards [hM.1] with p hp
    exact key p hp.1 hp.2
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ (A ξ)).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ T : Wp →L[ℂ] Wp, L T = ⟪A ξ, T ξ⟫_ℂ := fun T => by simp [L]
  have hLint : Integrable (fun p => L (beF z c π σ (σ x u) v p)) (μW.prod μN) := L.integrable_comp hint
  have hint2 : Integrable (fun p => ⟪A ξ, beF z c π σ (σ x u) v p ξ⟫_ℂ) (μW.prod μN) := by
    simpa only [hL] using hLint
  refine ⟨hint2.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae]
  have hI : ∫ p, ⟪A ξ, beF z c π σ (σ x u) v p ξ⟫_ℂ ∂(μW.prod μN) = ⟪A ξ, A ξ⟫_ℂ := by
    simp_rw [← hL]
    rw [L.integral_comp_comm hint, hL]
    rfl
  rw [hI, inner_self_eq_norm_sq_to_K]
  norm_num

end PI.WBL.NIS
