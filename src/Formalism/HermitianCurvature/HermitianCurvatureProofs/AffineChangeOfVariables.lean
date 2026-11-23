module

public import Formalism.HermitianCurvature.StatementG

@[expose] public section

open Formalism.FourierDecayAlt.G Matrix MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Formalism.FourierDecayAlt.P.G3

theorem map_mul_vol (α : ℂ) (hα : α ≠ 0) :
    Measure.map (fun ρ : ℂ => α * ρ) (volume : Measure ℂ) = ENNReal.ofReal ((‖α‖ ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ α) = ‖α‖ ^ 2 := by
    have h1 := Algebra.norm_complex_apply α
    rw [Algebra.norm_apply] at h1
    rw [← Complex.normSq_eq_norm_sq, ← h1]
    rfl
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ)
    (f := LinearMap.mulLeft ℝ α) (by rw [hdet]; positivity)
  rw [hdet, abs_of_nonneg (by positivity)] at h
  exact h

theorem wMat_mul_self (d : ℕ) : wMat d * wMat d = 1 := by
  ext i j
  have key : ∀ k : Fin d, (if k = i.rev then (1:ℂ) else 0) * (if j = k.rev then (1:ℂ) else 0) =
      if k = i.rev then (if i = j then 1 else 0) else 0 := by
    intro k
    by_cases hk : k = i.rev
    · simp [hk, eq_comm]
    · simp [hk]
  simp only [wMat, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply, key]
  simp

instance (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance

end Formalism.FourierDecayAlt.P.G3

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.G3

theorem affine_change_of_variables : Formalism.FourierDecayAlt.G.AffineChange := by
  intro β α γ hα
  have h1 : (fun ρ : ℂ => α * ρ + γ) = (fun x => x + γ) ∘ (fun ρ : ℂ => α * ρ) := rfl
  have hmul := measurable_const_mul α
  have hadd := measurable_add_const γ
  unfold mu
  rw [h1, Measure.map_smul _ (hadd.comp hmul).aemeasurable, ← Measure.map_map hadd hmul,
    map_mul_vol α hα, Measure.map_smul _ hadd.aemeasurable, map_add_right_eq_self]
  rw [smul_comm]
  congr 1

theorem scale_product_measure : Formalism.FourierDecayAlt.G.ScalePi := by
  intro β z ι _ hz
  unfold muPi
  have hA := affine_change_of_variables β z 0 hz
  simp only [add_zero] at hA
  have hfun : (fun v : ι → ℂ => z • v) = fun v i => z * v i := by
    ext v i; simp
  have hc : Real.toNNReal ((‖z‖ ^ (2 * Fintype.card ι))⁻¹) =
      (Real.toNNReal ((‖z‖ ^ 2)⁻¹)) ^ Fintype.card ι := by
    rw [← Real.toNNReal_pow (by positivity), inv_pow, pow_mul]
  have hsf : SigmaFinite (Measure.map (fun ρ : ℂ => z * ρ) (mu β)) := by
    rw [hA]; infer_instance
  rw [hfun, Measure.pi_map_pi (fun _ => (measurable_const_mul z).aemeasurable)]
  simp only [hA]
  refine Measure.pi_eq fun s hs => ?_
  rw [hc]
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

end Formalism.FourierDecayAlt.P
