module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.CutTrDZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FibreFactorHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F
open scoped Classical

namespace PositivityTheory.Rg.BcB.Desc

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def ldet (x : H E n 0) : ℝ := logAbs x.1.val.det

def IsPiVec (D : Dom E n 0) (π : CuspSub E n) {ι : Type} (f : Hs (ι := ι) D) : Prop :=
  ∀ i, ∃ ψ ∈ π.V, ∃ u : ℝ → ℂ, Continuous u ∧ HasCompactSupport u ∧
    (f i : H E n 0 → ℂ) =ᵐ[D.ν] fun x => ψ.1 x.1 * u (ldet x)

def piSp (D : Dom E n 0) (π : CuspSub E n) (ι : Type) [Fintype ι] : Submodule ℂ (Hs (ι := ι) D) :=
  (Submodule.span ℂ {f | IsPiVec D π f}).topologicalClosure

instance (D : Dom E n 0) (π : CuspSub E n) (ι : Type) [Fintype ι] : CompleteSpace (piSp D π ι) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

def ThetaFix (π : CuspSub E n) : Prop :=
  (∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) ∧ ∀ ψ ∈ π.V, ∃ ψ' ∈ π.V, ∀ g, ψ'.1 g = ψ.1 (thetaA E n g)

def ThetaFixOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ThetaFix π

def PiVecEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ ψ ∈ π.V, ∀ u : ℝ → ℂ, Continuous u → HasCompactSupport u →
    MemLp (fun x : H E n 0 => ψ.1 x.1 * u (ldet x)) 2 D.ν ∧
      ∀ M : ℕ, ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖ψ.1 x.1 * u (ldet x)‖ₑ ^ 2 ∂D.ν < ⊤

def PiInv : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ : Matrix ι ι (H E n 0 → ℂ)) (T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D),
    IsTestM Φ → IsROp D Φ T → ∀ f ∈ piSp D π ι, T f ∈ piSp D π ι

def IsTwTr (μ : Measure (H E n 0)) (π : CuspSub E n) (φ : H E n 0 → ℂ) (t : ℂ) : Prop :=
  ∃ L : π.V →ₗ[ℂ] π.V, (∀ (ψ : π.V) x, (L ψ).1.1 x = ∫ y, φ y * ψ.1.1 (thetaA E n (x * y.1)) ∂μ) ∧
    FiniteDimensional ℂ (LinearMap.range L) ∧
    t = LinearMap.trace ℂ (LinearMap.range L) (L.restrict fun x _ => LinearMap.mem_range_self L x)

def FinOn (μ : Measure (H E n 0)) (π : CuspSub E n) (φ : H E n 0 → ℂ) : Prop :=
  ∃ W : Submodule ℂ (Sm E n), W ≤ π.V ∧ FiniteDimensional ℂ W ∧ ∀ u : ℝ → ℂ, Continuous u → ∀ ψ ∈ π.V,
    ∃ ψ' ∈ W, ∀ x, ψ'.1 x = ∫ y, φ y * u (ldet y) * ψ.1 (x * y.1) ∂μ

def PiSeen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ W : Submodule ℂ (Sm E n), W ≤ π.V → FiniteDimensional ℂ W →
    ∃ (ψ : ℕ → Sm E n) (u : ℕ → ℝ → ℂ), (∀ j, ψ j ∈ π.V ∧ Continuous (u j) ∧ HasCompactSupport (u j)) ∧
      ∀ φ ∈ W, ∀ z : ℂ, (∀ j, ∫ x, starRingEnd ℂ ((ψ j).1 x.1 * u j (ldet x)) * (φ.1 x.1 * Complex.exp (z * ldet x)) ∂D.ν = 0) →
        φ = 0

end PositivityTheory.Rg.BcB.Desc

end
