module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartTransportToFramedPoint
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0041

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.IntChartExists

theorem intChart_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], IntegralChartExists Xo c ∧ ((∀ a : 𝓞 E, star a = H.bar a) → IntChartEx Xo c) ∧ ((∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT) := by
  intro E _ _ _ H Dw l Xo c _
  have h3 : (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
      ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT := fun hs =>
    GlobalTheory.IntChartTrunc.exists_intChart_frTrunc _root_.GlobalTheory.intChart E H Dw l Xo c hs (_root_.GlobalTheory.chartTransport_holds E H Dw l Xo c)
  refine ⟨fun hs T io y => ⟨(h3 hs T io y).choose⟩, fun hs => ?_, h3⟩
  unfold IntChartEx
  intros
  exact ⟨(h3 hs _ _ _).choose⟩

end GlobalTheory.IntChartExists
