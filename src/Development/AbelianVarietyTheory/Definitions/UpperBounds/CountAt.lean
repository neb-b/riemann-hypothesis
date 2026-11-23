module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

@[expose] public section

noncomputable section

namespace GlobalTheory.UpTie

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def domSpan (X : Data E r) (A : Set (Frame X.Ψ r → ℂ)) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  Submodule.span ℂ ((fun f => X.dom.indicator f) '' A)

end Model

section Record

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

end Record

end GlobalTheory.UpTie
