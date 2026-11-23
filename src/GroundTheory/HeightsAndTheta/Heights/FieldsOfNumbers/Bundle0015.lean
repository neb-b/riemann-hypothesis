module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreNonempty
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FibreNonempty.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
    (fibrePrimes j P' W).Nonempty

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreRelDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FibreRelDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → ∀ W' ∈ fibrePrimes j P' W, relDim W' = (n : ℕ)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsLocalIntegralClosureFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def LocalIntegralClosureFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ s : Finset (FractionRing (MRing ι' F ⧸ P')),
        (∀ e ∈ s, e ∈ homFracDegZero P' ∧
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) e) ∧
        ∀ x ∈ homFracDegZero P',
          IsIntegral ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P')) x →
          x ∈ Submodule.span ((degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P'))
            (s : Set (FractionRing (MRing ι' F ⧸ P')))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def SemilocalFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      Module.Finite (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def SemilocalIntegral.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      Algebra.IsIntegral (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalLengthSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem degZeroLoc_anti {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    degZeroLoc P 𝒲₂ ≤ degZeroLoc P 𝒲₁ := by
  unfold degZeroLoc
  apply Algebra.adjoin_mono
  rintro _ ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
  exact ⟨b, f, g, hf, hg, hgP, fun W hW => hgW W (h𝒲 hW), rfl⟩

section Fibre

variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}

theorem exists_fibreLift (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) (α : degZeroLoc (contractPrime j P') {W}) :
    ∃ β : (W' : Ideal (MRing ι' F)) → degZeroLoc P' {W'},
      ∀ W' ∈ fibrePrimes j P' W,
        (β W' : FractionRing (MRing ι' F ⧸ P')) = contractFracMap j P' (α : _) := by
  classical
  refine ⟨fun W' => if hm : contractFracMap j P' (α : _) ∈ degZeroLoc P' {W'} then ⟨_, hm⟩ else 0,
    fun W' hW' => ?_⟩
  have hm : contractFracMap j P' (α : _) ∈ degZeroLoc P' {W'} :=
    degZeroLoc_anti P' (Set.singleton_subset_iff.mpr hW')
      (map_degZeroLoc_le j P' W (Subalgebra.mem_map.mpr ⟨_, α.2, rfl⟩))
  simp only [dite_eq_left hm]

theorem exists_relDegFn :
    ∃ d : Ideal (MRing ι' F) → ℕ, ∀ W' (hW' : IsMultiProjPrime W'),
      d W' = (haveI : W'.IsPrime := hW'.isPrime; relDeg j W') := by
  classical
  exact ⟨fun W' => if hp : W'.IsPrime then haveI := hp; relDeg j W' else 0,
    fun W' hW' => dite_eq_left hW'.isPrime⟩

end Fibre


open scoped Classical in
set_option synthInstance.maxHeartbeats 100000 in
open Classical in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalLengthSum.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ (c : K → ℕ) (a h : MRing (fun k => ι' (j k)) F), IsMultiHomog a c → IsMultiHomog h c →
    a ∉ contractPrime j P' →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W → h ∉ W →
    ∀ d : Ideal (MRing ι' F) → ℕ,
      (∀ W' (hW' : IsMultiProjPrime W'), contractPrime j W' = W →
        haveI := hW'.isPrime
        d W' = relDeg j W') →
      haveI := hP'.isPrime
      ∀ α : degZeroLoc (contractPrime j P') {W},
        (α : FractionRing (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P')) =
            algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') a) /
              algebraMap (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') _
                (Ideal.Quotient.mk (contractPrime j P') h) →
      ∀ β : (W' : Ideal (MRing ι' F)) → degZeroLoc P' {W'},
        (∀ W' ∈ fibrePrimes j P' W,
          (β W' : FractionRing (MRing ι' F ⧸ P')) = contractFracMap j P' (α : _)) →
        ∃ hfin : (fibrePrimes j P' W).Finite,
          Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸
                LinearMap.range (LinearMap.lsmul (degZeroLoc (contractPrime j P') {W})
                  (degZeroLoc P' (fibrePrimes j P' W)) α)) =
            ∑ W' ∈ hfin.toFinset with rename (blockIncl j ι') a ∈ W',
              Ring.ord (degZeroLoc P' {W'}) (β W') * (d W' : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalResidueLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalResidueLength.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
    haveI := hP'.isPrime
    ∀ W' (hW' : W' ∈ fibrePrimes j P' W),
      haveI := hW'.1.isPrime
      ∃ 𝔪 : Ideal (degZeroLoc P' (fibrePrimes j P' W)),
        (∀ x : degZeroLoc P' (fibrePrimes j P' W),
          x ∈ 𝔪 ↔ ¬ ∃ y ∈ degZeroLoc P' {W'}, (x : FractionRing (MRing ι' F ⧸ P')) * y = 1) ∧
        Module.length (degZeroLoc (contractPrime j P') {W})
            (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪) = (relDeg j W' : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

