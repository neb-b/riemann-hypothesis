module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLoc

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeLocalLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeLocalLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W), P ≤ W →
    ∀ (c : K → ℕ) (a h : MRing ι F), IsMultiHomog a c → IsMultiHomog h c → h ∉ W →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ α : degZeroLoc P {W},
      (α : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P a) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P h) →
        multAt (P ⊔ Ideal.span {a}) W =
          Ring.ord (degZeroLoc P {W}) α

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocalRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocalRing.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)), IsMultiProjPrime W → P ≤ W →
    haveI := hP.isPrime
    (IsNoetherianRing (degZeroLoc P {W}) ∧ IsLocalRing (degZeroLoc P {W})) ∧
      ∀ n : ℕ, relDim P = (n + 1 : ℕ) → relDim W = (n : ℕ) → ringKrullDim (degZeroLoc P {W}) = 1

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDivCycleMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DivCycleMinimal.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), P.IsPrime →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ a : MRing ι F, a ∉ P →
    ∀ (W : Ideal (MRing ι F)) (hW : W.IsPrime), relDim W = (n : ℕ) → P ⊔ Ideal.span {a} ≤ W →
      haveI := hW
      W ∈ (P ⊔ Ideal.span {a}).minimalPrimes ∧ multAt (P ⊔ Ideal.span {a}) W ≠ ⊤

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFiniteRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def SemilocalFiniteRank.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      Module.Finite (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) ∧
        Module.IsTorsionFree (degZeroLoc (contractPrime j P') {W})
          (degZeroLoc P' (fibrePrimes j P' W)) ∧
        Module.finrank (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) =
          relDeg j P'

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a h : MRing (fun k => ι' (j k)) F), IsMultiHomog a c → IsMultiHomog h c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → h ∉ W →
    ∀ M : Ideal (MRing ι' F) → ℤ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        M W' = relDeg j W') →
      (∀ W', contractPrime j W' ≠ W → M W' = 0) →
      haveI := hP'.isPrime
      ∀ α : degZeroLoc (contractPrime j P') {W},
        (α : FractionRing (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P')) =
            algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') a) /
              algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') h) →
          ∃ N : ℕ, Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸
                LinearMap.range (LinearMap.lsmul (degZeroLoc (contractPrime j P') {W})
                  (degZeroLoc P' (fibrePrimes j P' W)) α)) = N ∧
            cycEval M (divCycle P' (rename (blockIncl j ι') a)) = N

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsValuativeCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ValuativeCentre.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P),
    haveI := hP.isPrime
    ∀ R : ValuationSubring (FractionRing (MRing ι F ⧸ P)),
      (∀ c : F, algebraMap F (FractionRing (MRing ι F ⧸ P)) c ∈ R) →
      ∃ y : Ideal (MRing ι F), IsMultiProjPrime y ∧ P ≤ y ∧
        ∀ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b → IsMultiHomog g b → g ∉ y →
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
              algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈ R ∧
            (f ∈ y ↔ algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
                (Ideal.Quotient.mk P f) / algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) ∈
              R.nonunits)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

