module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSaturatedFirstCoordinateLine
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelLatticeFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def relChartLat {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω)
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ) : Submodule R Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)}
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  zero_mem' := fun c _ => by simp
  smul_mem' := fun r s hs c hc => by rw [smul_mul_assoc]; exact Subalgebra.smul_mem _ (hs c hc) r

def RelLatticeFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n m : ℕ) (g : Fin m → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (relChartLat (Algebra.adjoin ℤ (Set.range g)) y a n).FG

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResChiIndex.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d d' : HSMDatum D Ω κ)
    (B : Matrix (Ix κ) (Ix κ) ℚ), IsInvMat B → d'.x = matAct B d.x →
    (∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), resGram d' n b = resGram d n fun k => matSubst B (b k)) →
    ∀ n : ℕ, resChi d' n - resChi d n = latLogIndex d.x d'.x n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionImageSup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def ResolutionImageSup.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n →
      ∀ y : d.R.X, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionPullback
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionPullback.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (d : HSMBlockDatum D K ι Ω),
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W : Weight L) (dV : SmoothVolume A),
      A.Compatible d.R.A ∧ W.IsSemipositive ∧ dV.μ = d.dV ∧
      ∀ (n : ℕ) (f : MRing ι), IsMultiHomog f (blockDeg d.k₀ n) →
        ∃ s ∈ L.sections n, ∀ x : d.R.X,
          ptNormSq W n s x =
            (‖eval (blockPt d x) (map (Int.castRingHom ℂ) f)‖ / d.A.h (blockPt d x) ^ n) ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSHProps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def ScaledFSHProps.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)),
    IsSemipositiveRel P0 P (scaledFSH ι) ∧ IsConjInvariantH (scaledFSH ι) ∧
      MonomialsBounded P (scaledFSH ι) (fun _ => 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionLatticeFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionLatticeFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (chartLat y a n).FG

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionOrderAtPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SectionOrderAtPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (W : Ideal (MRing ι)) (G H : MRing ι)
    (dg dh : K → ℕ),
    IsArithVar W 1 → mCoordIdeal y ≤ W → s ∈ chartLatNm y a τ →
    IsMultiHomog G dg → IsMultiHomog H dh → (∀ k, (dg k : ℤ) = dh k + τ * a k) →
    aeval y G = s * aeval y H → G ∉ W → H ∉ W →
    ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSpanStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionSpanStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chartLat y a (n + 1) ≤ AddSubgroup.closure {t | ∃ s ∈ chartLat y a n, ∃ j, t = s * w j}

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionsDimZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    IsArithVar (mCoordIdeal y) 1 →
      (Module.finrank ℚ (chartLatQ y a n) : ℤ) = genDeg (mCoordIdeal y) 0 a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftIntersectionPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ShiftIntersectionPolynomial.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem) (P : Ideal (MRing ι))
    (n : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsIntersectionSystem II → IsArithVar P n → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm B →
    ∃ p : Polynomial ℝ, p.natDegree ≤ n ∧ p.coeff n = II K ι P n (fun _ => A) ∧
      ∀ q : ℕ, II K ι P n (fun _ => HermLine.zcomb A B (q : ℤ) 1) = p.eval (q : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftNefBig
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ShiftNefBig.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    ∀ q : ℕ, 1 ≤ q → IsNefBigDatum P0 y D (HermLine.zcomb A (fsH ι) (q : ℤ) 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftSectionBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def ShiftSectionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (m : ℕ),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ∧
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
          (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) + C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

