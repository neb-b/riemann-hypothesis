module

public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CharId

@[expose] public section

-- bundled from Formalism.RealPlaceAnalysis.SmoothVectorGrowthBound
section
open MeasureTheory

noncomputable section

namespace Formalism.REAL

def hh {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.log (hs g)

def Eword {n : ℕ} (ε : Fin n → Bool) : List (Fin n × Fin n) →
    (Matrix (Fin n) (Fin n) ℂ → ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ)
  | [] => id
  | p :: w => fun f => Eab ε p.1 p.2 (Eword ε w f)

def CasF {n : ℕ} (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a, ∑ b, Eab ε a b (Eab ε b a f) g

abbrev toM {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

def HhLip : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    SmoothOnG ε (fun x => ((hh x : ℝ) : ℂ)) ∧
    ∀ (X g : Matrix (Fin n) (Fin n) ℂ), inG ε X → inUJ ε g →
      ‖Rd X (fun x => ((hh x : ℝ) : ℂ)) g‖ ≤ 2 * Real.sqrt (hs X)

def IntRdZero : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (φ : Matrix (Fin n) (Fin n) ℂ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ)
    (R : ℝ), SmoothOnG ε φ → inG ε X → (∀ g, inUJ ε g → R < hs g → φ g = 0) →
    ∫ g : UJ ε, Rd X φ (toM g) ∂(muG ε) = 0

def SmoothVectorGrowthBound : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)) (c : ℂ) (a : ℝ),
    FiniteDimensional ℂ W → 0 ≤ a →
    (∀ w ∈ W, SmoothOnG ε w) →
    (∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g) →
    (∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g) →
    (∀ w ∈ W, Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖w (toM g)‖ ^ 2) (muG ε)) →
    ∀ (w₁ w₂ : List (Fin n × Fin n)) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), f ∈ W → f' ∈ W →
      SmoothOnG ε (Eword ε w₁ f) ∧
      Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eword ε w₁ f (toM g)‖ ^ 2) (muG ε) ∧
      ∀ i j : Fin n,
        ∫ g : UJ ε, Eab ε i j (Eword ε w₁ f) (toM g) * starRingEnd ℂ (Eword ε w₂ f' (toM g)) ∂(muG ε) =
          (sgn ε i j : ℂ) *
            ∫ g : UJ ε, Eword ε w₁ f (toM g) * starRingEnd ℂ (Eab ε j i (Eword ε w₂ f') (toM g)) ∂(muG ε)

end Formalism.REAL
end
end

-- bundled from Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
section
namespace Formalism.REAL

theorem wdCas : WDCas := by
  intro V _ _ n ε E μ w hGl hU hKH
  have hK := compactCasimirOnHighestWeight_holds V n ε E μ w hGl hKH
  have hU' : IsUnitary ε (fun a b => if ε a = ε b then E a b else 0) := by
    intro a b x y
    by_cases h : ε a = ε b
    · simp only [if_pos h, if_pos h.symm]
      exact hU a b x y
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      simp only [if_neg h, if_neg h', LinearMap.zero_apply, inner_zero_left, inner_zero_right,
        mul_zero]
  have hCas' : Cas (fun a b => if ε a = ε b then E a b else 0) = CasK ε E := by
    unfold Cas CasK
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : ε a = ε b
    · simp only [if_pos h, if_pos h.symm]
    · have h' : ¬ ε b = ε a := fun e => h e.symm
      simp only [if_neg h, if_neg h', zero_mul]
  have hCasK' : CasK ε (fun a b => if ε a = ε b then E a b else 0) = CasK ε E := by
    unfold CasK
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h : ε a = ε b
    · simp only [if_pos h, if_pos h.symm]
    · simp only [if_neg h]
  have hS : (∑ a, ∑ b, ‖E a b w‖ ^ 2) =
      (∑ a, ∑ b, ‖(if ε a = ε b then E a b else 0) w‖ ^ 2) +
        ∑ a, ∑ b, (if ε a = ε b then 0 else ‖E a b w‖ ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h : ε a = ε b <;> simp [h]
  have hSc := congrArg (fun r : ℝ => (r : ℂ)) hS
  have h1 := sumOfSquaresIdentity_holds V n ε E w hU
  have h2 := sumOfSquaresIdentity_holds V n ε (fun a b => if ε a = ε b then E a b else 0) w hU'
  rw [hCas', hCasK'] at h2
  first | rw [two_nsmul] at h1 h2 | rw [two_smul] at h1 h2
  rw [add_sub_cancel_right, hK, inner_smul_right, inner_self_eq_norm_sq_to_K] at h2
  rw [LinearMap.sub_apply, LinearMap.add_apply, inner_sub_right, inner_add_right, hK,
    inner_smul_right, inner_self_eq_norm_sq_to_K] at h1
  push_cast at h1 h2 hSc ⊢
  linear_combination h1 - hSc - h2
theorem rhoStd : RhoStd := half_sum_roots_standard

theorem omEigen : OmEigen := omega_eigenvalue_holds
theorem uGap : UGap := unitary_spectral_gap
theorem growthIter : GrowthIter := iteratedGrowthBound_holds
theorem taylorRadius : TaylorRadius := taylorSummable_holds
theorem casCentral : CasCentral := casimir_central_holds

end Formalism.REAL

namespace Formalism.REAL
theorem epowCov : EpowCov := generatorPowCovariance_holds
theorem etrCentral : EtrCentral := generatorTraceCentral_holds
theorem diagChar : DiagChar := diagChar_of generatorPowDiagRecursion_holds
end Formalism.REAL

namespace Formalism.REAL
theorem charId : CharId := characteristicIdentity_holds
end Formalism.REAL

namespace Formalism.REAL
theorem qSkewRow : QSkewRow := quantumMinorRowSkew_holds
theorem qSkewCol : QSkewCol := quantumMinorColSkew_holds
theorem qDetHW : QDetHW := quantumDetHighestWeight_holds
theorem qDetCentral : QDetCentral := qDetCentral_of quantumMinorRowSkew_holds quantumMinorColSkew_holds
theorem qComatrix : QComatrix := qComatrix_of quantumMinorRowSkew_holds quantumMinorColSkew_holds
end Formalism.REAL
end

