module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

variable {n d : ℕ}

def sliceIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ) (q : Fin n → ℂ) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  J ⊔ Ideal.span (Set.range fun i => linPoly L i - C ((L *ᵥ q) i))

def IsRadicalAt (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) : Prop :=
  ∀ f ∈ I.radical, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧ s * f ∈ I

theorem eval_linPoly (L : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly L i) = (L *ᵥ x) i := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem zeroSet_sliceIdeal (J : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) : zeroSet (sliceIdeal J L q) = zeroSet J ∩ {x | L *ᵥ x = L *ᵥ q} := by
  ext x
  simp only [zeroSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun f hf => h f (Ideal.mem_sup_left hf), funext fun i => ?_⟩
    have := h _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    rwa [map_sub, eval_linPoly, eval_C, sub_eq_zero] at this
  · rintro ⟨hJ, hL⟩ f hf
    have hle : sliceIdeal J L q ≤ RingHom.ker (eval x) := by
      refine sup_le (fun g hg => RingHom.mem_ker.2 (hJ g hg)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_linPoly, eval_C, hL, sub_self]
    exact RingHom.mem_ker.1 (hle hf)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetBallCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def SmallSetBallCover.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1, ∃ T : Finset (Fin n → ℂ),
        (↑T : Set (Fin n → ℂ)) ⊆ zeroSet I ∩ K ∧ zeroSet I ∩ K ⊆ ⋃ c ∈ T, Metric.ball c r ∧
          (T.card : ℝ) * r ^ (2 * d) ≤ C * r ^ 2

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetTubeVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def SmallSetTubeVolume.Statement : Prop :=
  ∀ (n d : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (K : Set (Fin n → ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) → IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (zeroSet I ∩ K)) ≤
          ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOffDiscriminant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def StokesOffDiscriminant.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (P : MvPolynomial (Fin (d + 1)) ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    P ≠ 0 → (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → ∃ s, IsSheetAt J A x s) →
    ∀ (F G : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
      SmoothNear (zeroSet J) F → SmoothNear (zeroSet J) G → (∀ i, SmoothNear (zeroSet J) (φ i)) →
      HasCompactSupport F →
      (∃ U : Set (Fin n → ℂ), IsOpen U ∧ {x | eval (A *ᵥ x) P = 0} ⊆ U ∧
        ∀ x ∈ U ∩ zeroSet J, F x = 0) →
        chartInt J A F (vecCons G φ) = chartInt J A G (vecCons F φ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StStokesOnChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def StokesOnChart.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (f g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    SmoothNear (zeroSet J) f → SmoothNear (zeroSet J) g → (∀ i, SmoothNear (zeroSet J) (φ i)) →
    (HasCompactSupport f ∨ HasCompactSupport g) →
      chartInt J A f (vecCons g φ) = chartInt J A g (vecCons f φ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVanishNearPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

noncomputable section

def VanishNearPoint.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ),
    J.IsPrime → x ∈ zeroLocus J → (∀ᶠ y in 𝓝 x, y ∈ zeroLocus J → eval y f = 0) → f ∈ J

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarIntAdd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def VarIntAdd.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (f g : (Fin n → ℂ) → ℝ)
    (φ : Fin k → (Fin n → ℂ) → ℝ),
    J.IsPrime → Continuous f → HasCompactSupport f → Continuous g → HasCompactSupport g →
    (∀ i, SmoothNear (zeroSet J) (φ i)) →
      varInt J k (f + g) φ = varInt J k f φ + varInt J k g φ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarMassNearSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def VarMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (W I : Ideal (MvPolynomial (Fin n) ℂ)) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    (∀ i, SmoothNear (zeroSet W) (φ i)) → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) →
    Continuous f → HasCompactSupport f →
      ∀ δ > 0, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
        ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
          |varInt W d (fun x => χ x * f x) φ| ≤ δ

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarWirtinger
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

def VarWirtinger.Statement : Prop :=
  ∀ d : ℕ, ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ),
      J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
      ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
        Integrable (chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
            (fun _ => euclPot)) ∧
          μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ B) =
            ENNReal.ofReal (c * ∫ y, chartDens J A (((fun x => WithLp.toLp 2 x) ⁻¹' B).indicator fun _ => 1)
              (fun _ => euclPot) y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyMassLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def VarietyMassLower.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → ∀ R : ℝ,
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R → ∀ ρ ∈ Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (c * ρ ^ (2 * d)) ≤
          μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZeroSetOpenMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory

noncomputable section

def ZeroSetOpenMass.Statement : Prop :=
  ∀ (n d : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    ∀ (x : Fin n → ℂ) (O : Set (Fin n → ℂ)), IsOpen O → x ∈ O →
      x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W →
        0 < μH[((2 * d : ℕ) : ℝ)] (GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsSheetMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

def SheetSumMeasurable.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (g : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A →
    Measurable g → (∀ k, SmoothNear (zeroSet J) (φ k)) →
      Measurable (chartDens J A g φ) ∧ Measurable (chartAbsDens J A g φ)

end

end GroundTheory.Heights₂.Heights
end

