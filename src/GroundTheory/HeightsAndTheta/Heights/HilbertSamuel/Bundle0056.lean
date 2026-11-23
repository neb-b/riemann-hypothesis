module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def IsIsometricOn (P : Ideal (MRing ι)) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : Prop :=
  ∃ (f g : MRing ι) (α β : K → ℕ), IsMultiHomog f α ∧ IsMultiHomog g β ∧ f ∉ P ∧ g ∉ P ∧
    (∀ k, (α k : ℤ) - β k = A.a k - B.a k) ∧ divCycle P f = divCycle P g ∧
    ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ * B.h z = ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z

end Objects

def IsomInvariance.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
      IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) →
      (∀ j, IsIsometricOn P (L j) (L' j)) → I P n L = I P n L'

def GraphIsometric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι ι₂ : K → Type) [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) (d : ℕ) (A : ∀ k, ι₂ k → ι k → ℤ) (B₁ : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι₂)
    (B₁' B' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (Sum.elim ι ι₂)),
    IsArithVar P d → IsBasePtFree P (linForm A) → B₁.a = B.a →
    (∀ z ∈ mcPts P, B₁.h z = B.h (linApply A z)) →
    IsPullHerm Sum.inl inlV B₁ B₁' → IsPullHerm Sum.inr inrV B B' →
    IsIsometricOn (graphIdeal P (linForm A)) B₁' B'

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenKoszulStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenKoszulStep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α →
    ∃ R : ℕ, ∀ c : K → ℤ,
      (∀ p : ℕ, 1 ≤ p → p ≤ R → ∀ i : ℕ, 1 ≤ i →
        Subsingleton (KH.cechHc ι (KH.quotPart S V) (c - (p : ℤ) • α) i)) →
      ∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc ι (KH.quotPart S V) c i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedProductNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedProductNonneg.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (m : ℕ)
    (β : Fin m → K → ℤ),
    IsFieldIntersection I → IsProjVarF V m → (∀ j, KH.GeneratedV F V (β j)) → 0 ≤ I V m β

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHyperplaneRegularSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def HyperplaneRegularSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (e : K → ℕ),
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∃ σ : Ω, σ ≠ 0 ∧ σ ∈ chartLatQ y (fun k => (e k : ℤ)) 1 ∧
      ∀ (b : K → ℤ) (s : Ω), s ∈ chartLatQ y b 1 →
        σ * s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b + (fun k => (e k : ℤ)) - 1) 1 →
        s / (∏ k, y ⟨k, c k⟩) ∈ chartLatQ y (b - 1) 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedSectionStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedSectionStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → 2 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (H.a = fun _ => (1 : ℤ)) → IsSemipositiveRel P0 P H → MonomialsBounded P H (fun _ => 1) → IsConjInvariantH H →
    MixedKleiman.AtDim (d - 1) →
    ∀ q p : ℕ, 1 ≤ p → 0 < II K ι P d (fun _ => HermLine.zcomb M H (q : ℤ) (p : ℤ)) →
      0 ≤ II K ι P d (fun j : Fin d => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PieceDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (sg sg' : F →+* ℂ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) →
    ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) =
      ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg' z}.indicator fun _ => (1 : ℝ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameBasePtFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameBasePtFree.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e →
    IsBasePtFree (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (coordIdeal ℤ x)
      (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameGraphDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameGraphDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    ∃ (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
        (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))))
      (J : IFamily G.Φ (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) (Sum.inr : Unit → Unit ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = (projDeg x e : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameImage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def ProjFrameImage.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e →
    imageZ (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))))
      (graphIdeal (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))) = ⊥

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsQuotPartGraded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def QuotPartGraded.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (V : Ideal (MRingOver S ι)), IsMultiHomogIdeal V → KH.IsMGraded S ι (KH.quotPart S V)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealFormsOnPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RealFormsOnPoints.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (d : ℕ) (e : K → ℕ) (r : ℕ) (g : Fin r → MRing ι),
    IsArithVar (mCoordIdeal y) d → (∀ i, IsMultiHomog (g i) e) →
    LinearIndependent ℤ (fun i => aeval y (g i)) →
    ∀ c : Fin r → ℝ,
      (∀ z ∈ mcPts (mCoordIdeal y), ∑ i, (c i : ℂ) * eval z (map (Int.castRingHom ℂ) (g i)) = 0) →
      c = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealGramComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def RealGramComparison.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ), IsProjFrame d.x e →
    (fun n => resChi d n - resCChi d n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

