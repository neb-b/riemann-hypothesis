module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionMixed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

def SmallSectionMixed.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M H : HermLine ι) (p q : ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (H.a = fun _ => (1 : ℤ)) → IsSemipositiveRel P0 P H → MonomialsBounded P H (fun _ => 1) → IsConjInvariantH H →
    1 ≤ p → 0 < II K ι P d (fun _ => HermLine.zcomb M H q p) →
    ∃ (n : ℕ) (f g : MRing ι), 1 ≤ n ∧ IsRatSectionOn P (HermLine.zcomb M H ((n * q : ℕ) : ℤ) ((n * p : ℕ) : ℤ)) f g ∧
      divCycle P g ≤ divCycle P f ∧
      ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ ≤
        ‖eval z (map (Int.castRingHom ℂ) g)‖ * (HermLine.zcomb M H ((n * q : ℕ) : ℤ) ((n * p : ℕ) : ℤ)).h z

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def SmallSectionPointHeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (τ : ℕ) (s : Ω) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    1 ≤ τ → s ∈ chartLatNm y A.a τ → s ≠ 0 → IsSmallH (mCoordIdeal y) y A τ s →
    ∃ f : MRing ι, (∃ d, IsMultiHomog f d) ∧ f ∉ mCoordIdeal y ∧
      ∀ W : Ideal (MRing ι), IsArithVar W 1 → mCoordIdeal y ≤ W → f ∉ W → 0 ≤ II K ι W 1 ![A]

theorem SmallSectionPointHeight.chartLat_le_chartLatNm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : chartLat y a τ ≤ chartLatNm y a τ := by
  intro s hs c hc
  have h := hs c hc
  exact (mem_integralClosure_iff _ _).mpr (isIntegral_algebraMap (x := (⟨_, h⟩ : chartRingZ y c)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsNonzero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallSectionsNonzero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmallGeneratedDatum P0 y D A →
    ∀ j : ℕ, ∃ t ∈ chartLat y A.a j, t ≠ 0 ∧ IsSmallH (mCoordIdeal y) y A j t

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SupBoundBlock.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MRing ι, IsMultiHomog f (blockDeg d.k₀ n) →
      ∀ z ∈ mcPts (mCoordIdeal d.y),
        ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2Norm d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundCount
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def SupBoundCount.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) (c : ℝ), 0 < c →
    (∀ f : MRing ι, IsMultiHomog f (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f) →
    (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * c ^ 2 ∧
      blockChi d n - (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) *
          Real.log (c * Real.sqrt (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)))) ≤
        smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopConstantTwist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

def TopConstantTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (c : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → IsSmoothHerm A →
    II K ι P (D + 1) (fun _ => A.tensor (constLine c)) =
      II K ι P (D + 1) (fun _ => A) - ((D + 1 : ℕ) : ℝ) * c * geomDeg P A D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTopPullFS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def TopPullFS.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (m : ConeMetric ℂ (Ix κ)) (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsSmoothMetric m → IsProjFrame x e →
    IsPullFS x e m → top I x m D = (projDeg x e : ℝ) * hhOf I D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistMetric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory NumberField

def TwistMetric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem) (u : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → IsConjInvariantH A →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ c : ℝ, ∀ δ : ℝ, 0 < δ → ∃ A' : HermLine ι, A'.a = A.a ∧
      IsSemipositiveRel P0 (mCoordIdeal y) A' ∧ IsConjInvariantH A' ∧
      (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
        A'.h z = Real.exp (u sg + δ) * A.h z) ∧
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A') ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + c * δ

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUpperNormalisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def UpperNormalisation.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (B : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D B → IsConjInvariantH B → (∀ k, 1 ≤ B.a k) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n ≤
        (II K ι (mCoordIdeal y) (D + 1) (fun _ => B) + ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombExpand
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ZCombExpand.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (d : ℕ) (M H : HermLine ι) (q p : ℕ),
      IsArithVar P d → IsSmoothHerm M → IsSmoothHerm H →
      I P d (fun _ => HermLine.zcomb M H (q : ℤ) (p : ℤ)) =
          ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (q : ℝ) ^ (d - i) * (p : ℝ) ^ i *
            I P d (fun j : Fin d => if (j : ℕ) < d - i then M else H) ∧
        (1 ≤ d → I P d (fun j : Fin d => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)) =
          ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * (q : ℝ) ^ (d - 1 - i) * (p : ℝ) ^ i *
            I P d (fun j : Fin d => if (j : ℕ) < d - i then M else H))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZCombLimit.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : HermLine ι) (II : IntersectionSystem) (k : ℕ),
    IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A → IsSmoothHerm B →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p q : ℕ, 0 < p → 0 < q → (p : ℝ) / q < δ →
      |II K ι (mCoordIdeal y) (D + 1) (fun _ => HermLine.zcomb A B ((q : ℤ) - k * p) p) /
          (q : ℝ) ^ (D + 1) - II K ι (mCoordIdeal y) (D + 1) (fun _ => A)| < ε ∧
      |(genDeg (mCoordIdeal y) D (HermLine.zcomb A B ((q : ℤ) - k * p) p).a : ℝ) / (q : ℝ) ^ D -
          genDeg (mCoordIdeal y) D A.a| < ε

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

