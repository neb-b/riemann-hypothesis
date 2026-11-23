module

public import Mathlib
public import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.FiltrationCocycleLiftCriterion

@[expose] public section

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral
open scoped Matrix.Norms.L2Operator Real InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

theorem continuous_kMat : Continuous kMat := by
  have : kMat = fun θ : ℝ => hGL2.expG (θ • lW) := funext fun θ => (expG_lW θ).symm
  rw [this]
  exact hGL2.continuous_expG.comp (continuous_id.smul continuous_const)

theorem kMat_add_two_pi (θ : ℝ) : kMat (θ + 2 * π) = kMat θ := by
  rw [kMat_add, kMat_two_pi, mul_one]

noncomputable def chi (j : ℤ) (θ : ℝ) : ℂ := Complex.exp ((j : ℂ) * θ * I)

theorem chi_add (j : ℤ) (a b : ℝ) : chi j (a + b) = chi j a * chi j b := by
  simp only [chi, ofReal_add, ← Complex.exp_add]; ring_nf

theorem chi_neg (j : ℤ) (a : ℝ) : chi j (-a) = (chi j a)⁻¹ := by
  simp only [chi, ofReal_neg, ← Complex.exp_neg]; ring_nf

theorem chi_mul_chi_neg (j : ℤ) (a : ℝ) : chi j a * chi j (-a) = 1 := by
  rw [chi_neg, mul_inv_cancel₀ (by simp [chi, Complex.exp_ne_zero])]

theorem chi_two_pi (j : ℤ) : chi j (2 * π) = 1 := by
  simp only [chi]
  have := Complex.exp_int_mul_two_pi_mul_I j
  rw [← this]; congr 1; push_cast; ring

theorem continuous_chi (j : ℤ) : Continuous (chi j) := by
  unfold chi; fun_prop

theorem norm_chi (j : ℤ) (a : ℝ) : ‖chi j a‖ = 1 := by
  rw [chi, Complex.norm_exp]
  simp

theorem conj_chi (j : ℤ) (a : ℝ) : (starRingEnd ℂ) (chi j a) = chi j (-a) := by
  rw [chi, chi, ← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

def weightSpace (j : ℤ) : Submodule ℂ H where
  carrier := {v | ∀ θ : ℝ, σ (kMat θ) v = chi j θ • v}
  add_mem' {v w} hv hw θ := by simp [map_add (f := _), hv θ, hw θ, smul_add]
  zero_mem' θ := by simp
  smul_mem' c v hv θ := by simp [hv θ, smul_comm c]

noncomputable def wProj (j : ℤ) (x : H) : H :=
  ((2 * π : ℝ)⁻¹ : ℂ) • ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x

theorem continuous_orbit_kMat (x : H) : Continuous fun θ : ℝ => σ (kMat θ) x :=
  (σ.continuous_orbit x).comp continuous_kMat

theorem continuous_wIntegrand (j : ℤ) (x : H) :
    Continuous fun θ : ℝ => chi j (-θ) • σ (kMat θ) x :=
  ((continuous_chi j).comp continuous_neg).smul (continuous_orbit_kMat σ x)

theorem wProj_mem (j : ℤ) (x : H) : wProj σ j x ∈ weightSpace σ j := by
  intro φ
  have hper : Function.Periodic (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) (2 * π) := by
    intro θ
    simp only [kMat_add_two_pi, neg_add, chi_add, chi_neg j (2 * π), chi_two_pi, inv_one, mul_one]
  have hint := (continuous_wIntegrand σ j x).intervalIntegrable (μ := volume) 0 (2 * π)
  have h1 : σ (kMat φ) (∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x) =
      ∫ θ in (0 : ℝ)..(2 * π), chi j φ • (chi j (-(φ + θ)) • σ (kMat (φ + θ)) x) := by
    rw [← (σ (kMat φ)).intervalIntegral_comp_comm hint]
    congr 1; funext θ
    simp only [map_smul, ← UnitaryRep.map_mul_apply, ← kMat_add, smul_smul, neg_add, chi_add]
    congr 1
    rw [← mul_assoc, chi_mul_chi_neg, one_mul]
  have h2 : ∫ θ in (0 : ℝ)..(2 * π), (chi j (-(φ + θ)) • σ (kMat (φ + θ)) x) =
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x := by
    rw [intervalIntegral.integral_comp_add_left (fun θ : ℝ => chi j (-θ) • σ (kMat θ) x) φ, add_zero]
    have := hper.intervalIntegral_add_eq φ 0
    rw [zero_add] at this
    exact this
  unfold wProj
  rw [map_smul, h1, intervalIntegral.integral_smul, h2, smul_comm]

theorem inner_wProj (j : ℤ) (x y : H) :
    ⟪y, wProj σ j x⟫_ℂ = ((2 * π : ℝ)⁻¹ : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) * ⟪y, σ (kMat θ) x⟫_ℂ := by
  rw [wProj, inner_smul_right]
  congr 1
  have hint := (continuous_wIntegrand σ j x).intervalIntegrable (μ := volume) 0 (2 * π)
  have := (innerSL ℂ y).intervalIntegral_comp_comm hint
  simp only [innerSL_apply_apply, inner_smul_right] at this
  exact this.symm

theorem norm_wProj_le (j : ℤ) (x : H) : ‖wProj σ j x‖ ≤ ‖x‖ := by
  rw [wProj, norm_smul]
  have hb : ‖∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x‖ ≤ ‖x‖ * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_smul, norm_chi, one_mul, UnitaryRep.norm_map]
  rw [sub_zero, abs_of_pos (by positivity)] at hb
  have hn : ‖((2 * π : ℝ)⁻¹ : ℂ)‖ = (2 * π)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn]
  calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..(2 * π), chi j (-θ) • σ (kMat θ) x‖
      ≤ (2 * π)⁻¹ * (‖x‖ * (2 * π)) := by gcongr
    _ = ‖x‖ := by field_simp

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory intervalIntegral Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

end GroundTheory.Automorphic.ArchWhittaker
