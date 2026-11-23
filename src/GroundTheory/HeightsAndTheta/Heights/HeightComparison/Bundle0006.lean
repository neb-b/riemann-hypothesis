module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredPlacesFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def CentredPlacesFinite.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal],
      {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}.Finite

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredRingNormal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def CentredRingNormal.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    ∀ [IsFractionRing O L] (m : Ideal O) [m.IsMaximal],
      placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} =
        (integralClosure
          (Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors) L).toSubring

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalLengthPlaces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def LocalLengthPlaces.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal] (f : O), f ≠ 0 →
      (localQuotLength m f : ℝ) * Real.log (Nat.card (O ⧸ m)) =
        ∑ᶠ w ∈ {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}, -Real.log (w (f : L))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalQuotCard
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def LocalQuotCard.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal] (f : O), f ≠ 0 →
      Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
        Nat.card (O ⧸ m) ^ localQuotLength m f

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightLocalQuotCentred
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

def LocalQuotCentred.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : Subalgebra ℤ L), Algebra.FiniteType ℤ O →
    IsFractionRing O L → ∀ (m : Ideal O) [m.IsMaximal] (f : O), f ≠ 0 →
      ∀ g : placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t}, (g : L) = f →
        Nat.card (Localization.AtPrime m ⧸ Ideal.span {algebraMap O (Localization.AtPrime m) f}) =
          Nat.card (placesRing {w : FinitePlace L | AbsCentredAt O m fun t ↦ w t} ⧸ Ideal.span {g})

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitCenterChart.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        ∀ v : FinitePlace (coordField x),
          orbitCenter x v = V ↔ AbsCentredAt (chartRing x c) (chartPoint x c V)
            fun t ↦ v (IntermediateField.inclusion (ratioField_le_coordField x) t)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartDehom
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartDehom.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c c' : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
      (∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1)).comap
            (C : ℤ →+* MvPolynomial (Coord n) ℤ) = V.comap (C : ℤ →+* MvPolynomial (Coord n) ℤ) ∧
          Nonempty ((MvPolynomial (Coord n) ℤ ⧸
              (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1))) ≃+*
            (MvPolynomial (Coord n) ℤ ⧸
              (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) - 1))))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMax
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartMax.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        (chartPoint x c V).IsMaximal

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartMult
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartMult.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        ∀ [(chartPoint x c V).IsPrime],
          Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V =
            localQuotLength (chartPoint x c V) (chartEval x c s)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartQuot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartQuot.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)), (∀ k, x k (c k) ≠ 0) →
    ∀ V : Ideal (MvPolynomial (Coord n) ℤ), orbitIdeal x ≤ V →
      Nonempty ((chartRing x c ⧸ chartPoint x c V) ≃+*
        (MvPolynomial (Coord n) ℤ ⧸
          (V ⊔ Ideal.span (Set.range fun k ↦ (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) - 1))))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartResidue.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ),
    BlockNonzero x → Geo.IsSectionOn (orbitIdeal x) A.toGeo s →
    ∀ V ∈ Geo.divSupp (orbitIdeal x) s, ∀ c : (k : ι) → Fin (n k + 1),
      (∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V) →
        (Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V) =
          Real.log (Nat.card (chartRing x c ⧸ chartPoint x c V))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitChartRing
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

def OrbitChartRing.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)), (∀ k, x k (c k) ≠ 0) →
      Algebra.FiniteType ℤ (chartRing x c) ∧ IsFractionRing (chartRing x c) (ratioField x)

end GroundTheory.Heights₂.Heights
end

