module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocResidue.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (MRing ι F))
    [P.IsPrime] (W : Ideal (MRing ι F)) [W.IsPrime], P ≤ W →
    ∃ ρ : degZeroLoc P {W} →+* FractionRing (MRing ι F ⧸ W),
      (∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
        IsMultiHomog g b → g ∉ W →
        (x : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) →
        ρ x = algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W f) /
            algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W g)) ∧
      (∀ x : degZeroLoc P {W},
        ρ x = 0 ↔ ¬ ∃ y ∈ degZeroLoc P {W}, (x : FractionRing (MRing ι F ⧸ P)) * y = 1) ∧
      ∀ z : FractionRing (MRing ι F ⧸ W), z ∈ homFracDegZero W ↔ ∃ x, ρ x = z

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFunctionFieldFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FunctionFieldFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
      haveI := hP'.isPrime
      relDeg j P' ≠ 0

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalMaxIdeals
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

abbrev degZeroLoc.algebraOfSubset {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    Algebra (degZeroLoc P 𝒲₂) (degZeroLoc P 𝒲₁) :=
  (Subalgebra.inclusion (degZeroLoc_anti P h𝒲)).toRingHom.toAlgebra


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalMaxIdeals.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ (𝔪 : fibrePrimes j P' W → Ideal (degZeroLoc P' (fibrePrimes j P' W)))
        (h𝔪 : ∀ W', (𝔪 W').IsMaximal),
        Function.Injective 𝔪 ∧
        (∀ M : Ideal (degZeroLoc P' (fibrePrimes j P' W)), M.IsMaximal → ∃ W', M = 𝔪 W') ∧
        ∀ W' : fibrePrimes j P' W,
          (haveI := (h𝔪 W').isPrime
           letI := degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
           IsLocalization.AtPrime (degZeroLoc P' {W'.1}) (𝔪 W')) ∧
          haveI := W'.2.1.isPrime
          Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪 W') = (relDeg j W'.1 : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

