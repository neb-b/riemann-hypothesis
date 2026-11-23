module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexOrder ContDiff

noncomputable section

def HermitianDetMono.Statement : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), B.PosSemidef → (A - B).PosSemidef →
    B.det.re ≤ A.det.re

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.FourB
