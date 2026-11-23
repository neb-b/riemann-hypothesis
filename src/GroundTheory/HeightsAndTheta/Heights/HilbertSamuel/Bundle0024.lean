module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturbSemipos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PerturbSemipos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P0 P : Ideal (MRing ι)) (M : HermLine ι)
    (b a : ℤ),
    IsSemipositiveRel P0 P M → 0 ≤ b → 0 ≤ a → IsSemipositiveRel P0 P (HermLine.zcomb M (fsH ι) b a)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPointHeightFS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def PointHeightFS.Statement : Prop :=
  ∀ I : AllFam, I.IsFamily → hhOf I 0 = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjAvoidingForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def ProjAvoidingForm.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (df : K → ℕ) (f : MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → IsMultiHomog f df → f ∉ mCoordIdeal y →
    ∃ (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (G : MvPolynomial (Fin (D + 1)) ℤ),
      (∀ k, 1 ≤ e k) ∧ (∀ j, IsMultiHomog (L j) e) ∧
      (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) ∧ G ≠ 0 ∧
      ∀ ζ : Fin (D + 1) → ℂ, eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∀ z ∈ mcPts (mCoordIdeal y),
          (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
          eval z (map (Int.castRingHom ℂ) f) ≠ 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjDegGenDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def ProjDegGenDeg.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → IsProjFrame x e →
    genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1 = (projDeg x e : ℤ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFSMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ProjFSMass.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ)
    (m : ConeMetric ℂ (Ix κ)), IsProjFrame x e → IsPullFS x e m →
    ∃ Ψ : (((k : Unit) → GlobalTheory κ k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (ι := GlobalTheory κ) (coordIdeal ℤ x) Ψ ∧
        ptsIntegralAt (ι := GlobalTheory κ) (coordIdeal ℤ x) Ψ (purePot m D) (fun _ => 1) = (projDeg x e : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def PullFSExtension.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ),
    IsProjFrame x e →
    ∃ m₀ : ConeMetric ℂ (Ix κ), IsSmoothMetric m₀ ∧ IsConjInvariant m₀ ∧
      IsSemipositiveRel ⊥ (coordIdeal ℤ x) (HermLine.ofCone m₀) ∧ IsPullFS x e m₀

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatNoetherFrame
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RatNoetherFrame.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) →
    ∃ (B : Matrix (Ix κ) (Ix κ) ℚ) (e : Fin (D + 1) → Ix κ), IsInvMat B ∧ IsRatProjFrame (matAct B x) e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionToProjectiveBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def ReductionToProjectiveBlock.Statement : Prop :=
  ∀ (D : ℕ) (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (I : AllFam) (d : HSMBlockDatum D K ι Ω),
    I.IsFamily →
    (fun n => hsDefect D (blockChi d) (I K ι (mCoordIdeal d.y) (D + 1) fun _ => d.A) n -
        (genDeg (mCoordIdeal d.y) D d.A.a : ℝ) * hsDefect D (chiP D) (hhOf I D) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResChiBounds
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

def ResChiBounds.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ),
    IsProjFrame d.x e → IsPullFS d.x e d.m →
    ∃ (k : ℕ) (C : ℝ), ∀ n : ℕ, k + 1 ≤ n →
      (projDeg d.x e : ℝ) * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ resChi d n ∧
      resChi d n ≤ (projDeg d.x e : ℝ) * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

def ResVolume.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ)
    (R : AnRes P J e) [MeasurableSpace R.X] [BorelSpace R.X],
    IsArithVar P (e + 1) → ∃ dV : Measure R.X, IsSmoothVolume R.A dV

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def resolutionVolumeL2Complex (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℂ) : ℝ :=
  Real.sqrt (∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV)

def ResolutionSupBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : MvPolynomial (Ix κ) ℂ, f.IsHomogeneous n →
      ∀ z ∈ pts (coordIdeal ℤ d.x),
        ptNorm d.m (RingHom.id ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSTopPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable def scaledFSH {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι :=
  (fsH ι).tensor (constLine (-1))

def ScaledFSTopPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (II : IntersectionSystem),
    IsIntersectionSystem II → 1 ≤ d → IsArithVar P d → 0 < II K ι P d (fun _ => scaledFSH ι)

theorem scaledFSH_a {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    (scaledFSH ι).a = fun _ => 1 := by
  funext k
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

theorem scaledFSH_h {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    (scaledFSH ι).h z = (∏ k, (fsMetric (ι := ι k)).ρ (fun i => z ⟨k, i⟩)) * Real.exp 1 := by
  simp [scaledFSH, HermLine.tensor, fsH, HermLine.ofMetrics, constLine, HermLine.ofWeight]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

