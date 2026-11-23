module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0024
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePCEqEx
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0014
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0019
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0022
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0020
public import Formalism.LocalToGlobal.CharacterGerms.RowTieValK
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0039
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0010
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0040
public import Formalism.LocalToGlobal.CharacterGerms.CharacterHypothesisUnramified
public import Formalism.LocalToGlobal.CharacterGerms.CoeffPowCharFrobenius
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
public import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0021

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField Formalism.L2.FormalSeriesBounds.RF
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

theorem descent_holds : DescentSt Xo c := descent_of (nabMapSt_holds Xo c) descent_span nvalEqSt_holds

variable {Xo c}
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} {Orb : Type} [Fintype Orb] {d : ℕ} [NeZero d]

end Formalism.L2.FormalSeriesBounds
