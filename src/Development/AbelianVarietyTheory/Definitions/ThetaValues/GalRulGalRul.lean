module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.GalTw.Test

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CoefChangeCompare (Natural FromT ValueWD map_trans evR_spec evR_not evR_map)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem allTest : AllTest Xo c :=
  Frames.allTest_of_secBaseChange (Out.Laws.secBaseChange GlobalTheory.abelianSchemeLaws_all.1) E H Dw l Xo c

theorem galRul_one {ta : c.F ≃+* c.F} (h : Fixes c ta) : galRul (Xo := Xo) h 1 = 1 := by
  funext p y
  obtain ⟨q, φ, y₀, -, hq⟩ := evR_spec (GlobalTheory.GalTw.Rule.fromT_tw_test h allTest p y)
  show (evR Xo c 1 (twPt h y)).val = (1 : Rul Xo c) p y
  rw [hq]
  simp only [Pi.one_apply, map_one]
  rfl

theorem galRul_const {ta : c.F ≃+* c.F} (h : Fixes c ta) (a : c.F) :
    galRul h (a • (1 : Rul Xo c)) = ta a • (1 : Rul Xo c) := by
  rw [galRul_smul h a 1, galRul_one h]

end GlobalTheory.GalTw.Test
