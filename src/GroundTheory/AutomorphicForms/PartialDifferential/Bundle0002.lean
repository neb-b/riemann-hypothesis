module

public import Mathlib
public import GroundTheory.AutomorphicForms.PartialDifferential.EllipticDiffOp

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoBasic
section
namespace GroundTheory.Automorphic.Sobolev

open MeasureTheory
open scoped ContDiff

noncomputable section

variable {n : ℕ}

def dT {k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x ↦ iteratedFDeriv ℝ k f x v

def ev (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1

def pd (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℂ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x ↦ fderiv ℝ f x (ev i)

def pdT {k : ℕ} (J : Fin k → Fin n) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  dT (fun l ↦ ev (J l)) f

def hsD (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ J : Fin k → Fin n, ‖pdT J f x‖ ^ 2)

def l2n (g : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ := (eLpNorm g 2 volume).toReal

theorem dT_apply {k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    dT v f x = iteratedFDeriv ℝ k f x v := rfl

theorem pdT_apply {k : ℕ} (J : Fin k → Fin n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) :
    pdT J f x = iteratedFDeriv ℝ k f x (fun l ↦ ev (J l)) := rfl

theorem dT_zero (v : Fin 0 → EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    dT v f = f := by
  funext x
  simp [dT, iteratedFDeriv_zero_apply]

theorem pdT_zero (J : Fin 0 → Fin n) (f : EuclideanSpace ℝ (Fin n) → ℂ) : pdT J f = f :=
  dT_zero _ f

theorem pderiv_eq_dT (α : Fin n → ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : pderiv α f x = dT (mdir α) f x := rfl

theorem norm_ev (i : Fin n) : ‖ev i‖ = 1 := by
  simp [ev]

theorem hsD_nonneg (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ hsD k f x :=
  Real.sqrt_nonneg _

theorem hsD_sq (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    hsD k f x ^ 2 = ∑ J : Fin k → Fin n, ‖pdT J f x‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem hsD_zero (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) :
    hsD 0 f x = ‖f x‖ := by
  rw [hsD, Fintype.sum_unique, pdT_zero, Real.sqrt_sq (norm_nonneg _)]

theorem l2Norm_nonneg_alt (g : EuclideanSpace ℝ (Fin n) → ℝ) : 0 ≤ l2n g :=
  ENNReal.toReal_nonneg

end

end GroundTheory.Automorphic.Sobolev
end

-- bundled from GroundTheory.AutomorphicForms.PartialDifferential.EllipticSolutions
section
namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

variable {n : ℕ}

section Integrable

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Integrable

theorem integrable_smul_of_locallyIntegrableOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} {u : E → ℂ} (hu : LocallyIntegrableOn u Ω) {φ : 𝓢(E, ℂ)} (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) : Integrable (fun x ↦ φ x • u x) := by
  have hK := (hu.mono_set hφΩ).integrableOn_isCompact hφc.isCompact
  have hind := hK.integrable_indicator (isClosed_tsupport _).measurableSet
  have h := hind.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 φ) φ.continuous.aestronglyMeasurable
    (ae_of_all _ fun x ↦ SchwartzMap.norm_le_seminorm ℝ _ _)
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul]
  by_cases hx : x ∈ tsupport φ
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

end

end GroundTheory.Automorphic.Sobolev
end

