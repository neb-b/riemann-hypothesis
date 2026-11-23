module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001

@[expose] public section

open MeasureTheory NumberField Finset

noncomputable section

namespace GlobalTheory.Deep

open Formalism.MainNotions.S GlobalTheory.Count

def PtBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h : ℝ),
    IsDSData B d → SigIs B p q → GapGe B h →
    120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      (1 ≤ min p q → ∀ y : B.I.GA,
          ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re *
            ∏ v, GlobalTheory.IndefiniteRowSideFullHecke.PointwiseKernelBound.decHS (min p q) h (dHS (uMat (y.1 v)))) ∧
      (∀ y : B.I.GA, ‖phe B d y‖ ≤ (∏ v, d v) * (B.e 1).re) ∧
      phe B d 1 = ((∏ v, d v : ℝ) : ℂ) * B.e 1 ∧
      (B.e 1).im = 0 ∧ 0 ≤ (B.e 1).re ∧
      (∀ y : B.I.GA, phe B d y ≠ 0 → y.2 ∈ B.I.Kset) ∧ GlobalTheory.Dec.LocDec B h

def FarBound : Prop :=
  ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (h ep : ℝ),
    IsDSData B d → SigIs B p q → q = min p q → 1 ≤ q → GapGe B h →
    0 < ep → ep ≤ 1 / Real.sqrt (2 * (q : ℝ)) → 2 * (B.I.n : ℝ) ^ 2 * ep ≤ Real.log 2 →
    64 * (B.I.n : ℝ) ^ 2 ≤ h * ep → 1 ≤ h * ep ^ 2 / 16 →
    120 * (B.I.n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
    ∀ x : B.I.GA,
      Summable (fun γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x => ‖phe B d (x⁻¹ * γ.1 * x)‖) ∧
      ∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x, ‖phe B d (x⁻¹ * γ.1 * x)‖ ≤
        (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
          (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * ep ^ 2 / 16)))

end GlobalTheory.Deep
