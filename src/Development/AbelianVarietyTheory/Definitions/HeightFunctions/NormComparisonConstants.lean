module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.NetNorms Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

structure FieldOK0 (D : D7) (p : ℕ) : Prop where
  own : p = D.host.pde ∨ p = D.host.pde'
  full : OFull D
  zetaM : OZeta D
  zetaP : zeta p ∈ FO D
  curve : GlobalTheory.CompRat.CurveOver (hostOfRecord D) (FO D) (D.host.g 0 * D.host.g 1 * p)
  kpsi : OKPsi D
  bad : 0 ∉ D.host.levelPrimes
  split : D.host.cls p = PrimeClass.splitK

def FieldSmall (D : D7) (large₂ : SizeData₂ D) : Prop :=
  letI : NumberField (FO D) := NumberField.mk
  Real.log (Module.finrank ℚ (FO D)) ≤ PO D large₂ ∧
    Real.log |((NumberField.discr (FO D) : ℤ) : ℝ)| / Module.finrank ℚ (FO D) ≤ PO D large₂

def NumOK (D : D7) (x : ℝ) : Prop :=
  ∃ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm), DV.KapDef D ∧ SizesAt L ∧ Pm.CnW = 10 ∧
    (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) ∧ 1000 ≤ Tp.CP ∧ Tp.CP ^ 20 ≤ zBase L ∧ x ≤ L.sc.x ∧ FieldSmall D L

structure RecOK (D : D7) (x : ℝ) : Prop where
  one : FieldOK0 D D.host.pde
  two : FieldOK0 D D.host.pde'
  xi1 : ∃ xi, XiOK D D.host.pde xi
  xi2 : ∃ xi, XiOK D D.host.pde' xi
  err : Nonempty (ErrX D)
  num : NumOK D x

variable {D : D7}

end GlobalTheory.FinalJoin2
