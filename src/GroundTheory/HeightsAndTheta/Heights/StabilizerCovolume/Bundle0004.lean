module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.LineField
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.GaussCM
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0019

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PVerticalGenericDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.LowerBoundFree
  GroundTheory.Heights₂.Heights.HilbertSamuel

namespace VerticalGenericDeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

variable {K : Type} {ι : K → Type}

theorem map_mem_map_iff {W : Ideal (MRing ι)} (hW : W.IsPrime) (hh : IsHorizontal W) (x : MRing ι) :
    MvPolynomial.map (Int.castRingHom ℚ) x ∈ W.map (MvPolynomial.map (Int.castRingHom ℚ)) ↔ x ∈ W := by
  classical
  let S : Submonoid (MRing ι) := (nonZeroDivisors ℤ).map (C (σ := Σ k, ι k))
  have : IsLocalization S (MRingOver ℚ ι) := MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  have hφ : algebraMap (MRing ι) (MRingOver ℚ ι) = MvPolynomial.map (Int.castRingHom ℚ) := by
    show MvPolynomial.map (algebraMap ℤ ℚ) = _
    rw [RingHom.ext_int (algebraMap ℤ ℚ) (Int.castRingHom ℚ)]
  have hdisj : Disjoint (S : Set (MRing ι)) W := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmW
    have h0 : m ∈ W.comap (C : ℤ →+* MRing ι) := hmW
    rw [hh, Ideal.mem_bot] at h0
    exact zero_notMem_nonZeroDivisors (h0 ▸ hm)
  have h := IsLocalization.under_map_of_isPrime_disjoint S (MRingOver ℚ ι) hW hdisj
  constructor
  · intro hx
    rw [← h]
    show algebraMap (MRing ι) (MRingOver ℚ ι) x ∈ Ideal.map (algebraMap (MRing ι) (MRingOver ℚ ι)) W
    rw [hφ]
    exact hx
  · intro hx
    exact Ideal.mem_map_of_mem _ hx

theorem isMultiHomog_map [DecidableEq K] {x : MRing ι} {e : K → ℕ} (h : NumbersDVR.IsMultiHomog x e) :
    NumbersDVR.IsMultiHomog (MvPolynomial.map (Int.castRingHom ℚ) x) e := by
  intro d hd
  apply h
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

end VerticalGenericDeg

end GroundTheory.Heights₂.Heights.NineStatements
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StMUcSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GroundTheory.Heights₂.Heights.LowerBoundFree
open ReciprocityTheory.AnForm (levi)

def MUcSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (M : XModel D)
    (w : ((Σ k, ι k) → ℂ) → ℝ) (S : BoundedRegularisationSetting M D.Xo H.aMu w) (B p q : ℕ) (t : ℝ),
    M.atlas.Smooth (S.bregWeight t) → IsSmoothHerm (MUc H S B p q t)

section Inhabitants

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {D : ComponentData II Ψ K ι Ω E} {H : HodgeData D} {M : XModel D}
  {w : ((Σ k, ι k) → ℂ) → ℝ}

end Inhabitants

end GroundTheory.Heights₂.Heights.NineStatements
end
end

