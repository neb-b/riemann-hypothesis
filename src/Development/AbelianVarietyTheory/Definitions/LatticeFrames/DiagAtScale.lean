module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004

@[expose] public section

noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Diag

def TrueS (D : D7) : Prop :=
  Formalism.BasicNotions.Ties D ∧ Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D ∧ Formalism.L2.SG.Pf.LocCP.LocTied D ∧ Nonempty (Formalism.L2.SG.SpectralTiesReal.STies D)

def e0 (D : D7) (C0 : ℝ) : ℝ := 2 * C0 / AdmissibleBoundsFromSource.Gam D + 2 * AdmissibleBoundsFromSource.xK D

def gamL (D : D7) (L C : ℝ) : ℝ := Real.exp (C * (D.R.m : ℝ) ^ 5 * D.R.f * L)

def SDiagAt (D : D7) (u : D.what₂.Word) (Γ c : ℝ) : Prop :=
  GlobalTheory.Core.Rk.hsDev D u ≤
    4 * ((Γ + 1) * (D.duS u : ℝ) ^ 2 / D.what₂.Dstar + (D.duS u : ℝ) * Real.exp (-(c * D.R.k * D.R.f * Real.log D.R.k))) +
      2 * (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

end GlobalTheory.Core.Diag
