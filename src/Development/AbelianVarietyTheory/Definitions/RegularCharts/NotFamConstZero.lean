module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

@[expose] public section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg.PChartModel

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem evR_map (h : EvLaws Xo c) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  have hy := h.test S y
  have h1 := hy.choose_spec.choose_spec.choose_spec
  have h2 := frMap_trans _ _ _ _ φ _ _ _ h1 hyz
  have hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨_, _, _, h2⟩
  unfold evR evalAt
  rw [dite_eq_left hy, dite_eq_left hz]
  exact h.wd f hf T _ _ _ (φ.comp _) _ _ z hz.choose_spec.choose_spec.choose_spec h2

end GlobalTheory.Reg.PChartModel
