module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricMaxComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def MetricMaxComparison.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι), IsSmoothHerm A →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      A.h z ≤ C * (HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) A.a).h z

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMetricToFS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def MetricToFS.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsProjFrame d.x e →
    ∃ d₀ : HSMDatum D Ω κ, d₀.x = d.x ∧ IsPullFS d.x e d₀.m ∧
      (fun n => hsDefect D (resChi d₀) (top I d.x d₀.m D) n - hsDefect D (resChi d) (top I d.x d.m D) n)
        =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleiman
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedKleiman.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M A : HermLine ι) (a : K → ℕ) (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (A.a = fun k => (a k : ℤ)) → IsSemipositiveRel P0 P A → MonomialsBounded P A a → IsConjInvariantH A →
    ∀ j ≤ d, 0 ≤ II K ι P d (fun i : Fin d => if (i : ℕ) < j then M else A)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMonomialShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def MonomialShift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (q τ n : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (A.a = fun k => (a k : ℤ)) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → MonomialsBounded (mCoordIdeal y) A a →
    1 ≤ q → τ ≤ q * n →
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1))
        (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def NefAmpleFibre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (α : K → ℤ) (b a ℓ : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → NefOnFibres (mCoordIdeal y) α → 1 ≤ b → 1 ≤ a → ℓ.Prime →
    KH.AmpleV (ZMod ℓ) (fibreIdeal ℓ y) ((b : ℤ) • α + fun _ => (a : ℤ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNefAmpleGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def NefAmpleGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (M : HermLine ι) (P0 : Ideal (MRing ι))
    (b a : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) M →
    1 ≤ b → 1 ≤ a → KH.AmpleV ℚ (KH.genIdeal y) ((b : ℤ) • M.a + fun _ => (a : ℤ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNestedLattice
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def ChangeOfLatticeNested.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    (fun n : ℕ => latLogIndex x (matAct B x) n -
        (top I (matAct B x) m' D - top I x m D) * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D

namespace ChangeOfLatticeNested

theorem matAct_one {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] [DecidableEq J] (x : J → Ω) :
    matAct (1 : Matrix J J ℚ) x = x := by
  funext i
  simp only [matAct, Matrix.one_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

end ChangeOfLatticeNested

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNmSectionsFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def NmSectionsFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℕ),
    (∀ k, 1 ≤ a k) → (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → Birational y → ∀ τ₂ : ℕ,
    ∃ (J : Type) (_ : Fintype J) (d : J → ℕ) (e : J → Ω) (τ₁ : ℕ),
      (∀ j, τ₂ ≤ d j ∧ d j ≤ τ₁ ∧ e j ∈ chartLatNm y (fun k => (a k : ℤ)) (d j)) ∧
      ∀ τ : ℕ, τ₁ ≤ τ → ∀ s ∈ chartLatNm y (fun k => (a k : ℤ)) τ,
        ∃ r : J → Ω, (∀ j, r j ∈ secM y (fun k => (τ - d j) * a k)) ∧ s = ∑ j, r j * e j

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

def NonvanishingDense.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (f : MRing ι), IsArithVar P d → f ∉ P →
    mcPts P ⊆ closure {z | z ∈ mcPts P ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormalLocusRep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def NormalLocusRep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ (df : K → ℕ) (f : MRing ι), IsMultiHomog f df ∧ f ∉ mCoordIdeal y ∧
      ∀ (a : K → ℤ) (τ : ℕ), ∀ s ∈ chartLatNm y a τ, ∀ z ∈ mcPts (mCoordIdeal y),
        eval z (map (Int.castRingHom ℂ) f) ≠ 0 →
        ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
          (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = s * aeval y h ∧
          eval z (map (Int.castRingHom ℂ) h) ≠ 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SemiposTwist.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P0 P : Ideal (MRing ι)) (L : HermLine ι)
    (p q : ℕ), IsSemipositiveRel P0 P L → IsSemipositiveRel P0 P (HermLine.zcomb L (fsH ι) q p)

def GenOnFibres.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) (w : Fin n → Ω),
    (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    KH.GeneratedV ℚ (KH.genIdeal y) a ∧ ∀ ℓ : ℕ, ℓ.Prime → KH.GeneratedV (ZMod ℓ) (fibreIdeal ℓ y) a

def AmpleOfGenTwist.Statement : Prop :=
  ∀ (S : Type) [Field S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (p q : ℕ),
    IsMultiHomogIdeal V → KH.GeneratedV S V α → 1 ≤ p →
    KH.AmpleV S V ((q : ℤ) • α + fun _ => (p : ℤ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbMonomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def PerturbMonomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (q : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (A.a = fun k => (a k : ℤ)) →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → MonomialsBounded (mCoordIdeal y) A a →
    1 ≤ q →
    IsSmallGeneratedDatum P0 y D (HermLine.zcomb A (fsH ι) q 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

