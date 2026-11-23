module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def SecEq.Statement : Prop := KH.SecEqStatement

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecMRankBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SecMRankBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (b : K → ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ k, 1 ≤ b k) →
    (∀ m : ℕ, Module.Finite ℤ (secM y (fun k => m * b k))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, (Module.finrank ℤ (secM y (fun k => m * b k)) : ℝ) ≤ C * ((m : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeronese
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SecondVeronese.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (κ : Type) (_ : Fintype κ) (d : HSMDatum D Ω κ),
      (∀ n : ℕ, resChi d n = chiP D (2 * n)) ∧
      (∀ I : AllFam, I.IsFamily → top I d.x d.m D = 2 ^ (D + 1) * hhOf I D) ∧
      genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 = 2 ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionProduct.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A B C : HermLine ι) (n j τ : ℕ) (s t : Ω),
    (τ : ℤ) • C.a = (n : ℤ) • A.a + (j : ℤ) • B.a →
    (∀ z ∈ mcPts (mCoordIdeal y), C.h z ^ τ = A.h z ^ n * B.h z ^ j) →
    s ∈ chartLat y A.a n → t ∈ chartLat y B.a 1 →
    s * t ^ j ∈ chartLat y C.a τ ∧
      ∀ c c' : ℝ, IsBoundedH (mCoordIdeal y) y A n c s → IsBoundedH (mCoordIdeal y) y B 1 c' t →
        IsBoundedH (mCoordIdeal y) y C τ (c * c' ^ j) (s * t ^ j)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionRingFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (r : ℕ) (d : Fin r → ℕ) (e : Fin r → Ω), (∀ i, e i ∈ chartLat y a (d i)) ∧
      ∀ n : ℕ, chartLat y a n ≤ AddSubgroup.closure
        {s | ∃ (i : Fin r) (μ : Fin q → ℕ), d i + ∑ j, μ j = n ∧ s = e i * ∏ j, w j ^ μ j}

def SectionBounded.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (q : ℕ) (w : Fin q → Ω),
    (∀ j, w j ∈ chartLat y A.a 1) → KH.GeneratesOn y A.a w → (∀ j, IsSmallH (mCoordIdeal y) y A 1 (w j)) →
    ∀ (n : ℕ) (s : Ω), s ∈ chartLat y A.a n → ∃ C : ℝ, IsBoundedH (mCoordIdeal y) y A n C s

def SectionBoundedMul.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n m : ℕ) (C C' : ℝ) (s t : Ω),
    s ∈ chartLat y A.a n → t ∈ chartLat y A.a m →
    IsBoundedH (mCoordIdeal y) y A n C s → IsBoundedH (mCoordIdeal y) y A m C' t →
    IsBoundedH (mCoordIdeal y) y A (n + m) (C * C') (s * t)

section Inhabitants

open ProjLine

theorem isBoundedH_one_of_isSmallH {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : HermLine ι} {τ : ℕ} {s : Ω}
    (h : IsSmallH P y A τ s) : IsBoundedH P y A τ 1 s := by
  intro dg dh g h' z hg hh hdeg he hz
  rw [one_mul]
  exact h dg dh g h' z hg hh hdeg he hz

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSupBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionSupBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (e : Ω),
    ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} → e ∈ chartLat y A.a τ →
    ∃ C : ℝ, 0 ≤ C ∧ IsBoundedH (mCoordIdeal y) y A τ (Real.exp C) e

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionsRank.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (n : ℕ),
    GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory κ)
        ((coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ))) (fun _ => (n : ℤ)) =
      (Module.finrank ℤ (sec ℤ x n) : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreArith
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def segreCoords {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [CommRing Ω] (y : (Σ k, ι k) → Ω) :
    Ix ((k : K) → ι k) → Ω :=
  fun p => ∏ k, y ⟨k, p.2 k⟩

def SegreArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) →
    IsArithVar (ι := GlobalTheory ((k : K) → ι k)) (coordIdeal ℤ (segreCoords y)) (D + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSeparatedSmallCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SeparatedSmallCount.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (τ : ℕ) (b : ℝ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → 0 ≤ b →
    (∀ s : Ω, s ∈ chartLat y A.a τ → s ≠ 0 → ∀ c : ℝ, c < Real.exp (-b) →
      ¬ IsBoundedH (mCoordIdeal y) y A τ c s) →
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) τ ≤
      (Module.finrank ℤ (chartLat y A.a τ) : ℝ) * (b + Real.log 3)

section Inhabitant

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

end Inhabitant

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftDegreePolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftDegreePolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (a b : K → ℤ),
    IsArithVar P (D + 1) →
    ∃ r : Polynomial ℝ, r.natDegree ≤ D ∧ r.coeff D = (genDeg P D a : ℝ) ∧
      ∀ q : ℕ, (genDeg P D ((q : ℤ) • a + b) : ℝ) = r.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionSeparation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftSectionSeparation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q → ∀ (n : ℕ) (s : Ω),
      s ∈ chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a n → s ≠ 0 →
      ∀ c : ℝ, c < Real.exp (-(C * n * ((q : ℝ) + 1))) →
        ¬ IsBoundedH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) (q : ℤ) 1) n c s

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallPacking
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallPacking.Statement : Prop := PackingStatement

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

