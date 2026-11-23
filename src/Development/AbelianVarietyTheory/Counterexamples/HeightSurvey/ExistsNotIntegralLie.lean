module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
public import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0083
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029

@[expose] public section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.NonIntegralFrameExample

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

theorem spread_holds : SpreadSt Xo c :=
  GlobalTheory.Frames.framedPoint_field_fromTest GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c

variable {Xo c}

theorem exists_framed {S : Type} [Field S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c S) :
    ∃ y : FrPt Xo c S, y.x = x := by
  choose u hu using fun τ => GlobalTheory.IntFramesCompare.exists_eigenBasisAt (c := c) hx τ
  obtain ⟨s, hs⟩ := gfp_gen GlobalTheory.abelianSchemeLaws_all.2.secTwist x
  exact ⟨⟨x, hx, u, fun τ => (hu τ).1, fun τ => (hu τ).2.1, fun τ => (hu τ).2.2, s, hs⟩, rfl⟩

end GlobalTheory.NonIntegralFrameExample
