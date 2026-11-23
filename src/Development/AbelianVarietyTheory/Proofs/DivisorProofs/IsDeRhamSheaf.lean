module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham

namespace GlobalTheory.DeRhamSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

abbrev onAff {V : T.Opens} (hV : IsAffineOpen V) : Over (Sp Γ(T, V)) :=
  (Over.pullback hV.fromSpec).obj A

instance {V : T.Opens} (hV : IsAffineOpen V) : GrpObj (onAff A hV) := Functor.grpObjObj

end GlobalTheory.DeRhamSheaf
