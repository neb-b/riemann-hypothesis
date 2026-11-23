module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TruncatedExpSecondEqFull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeExists
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem canonGauge_exists : CanonGaugeSt :=
  canonGauge_of_log FormalLog.logSt_and_logDerivSt.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceAll
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem gaugeExp_holds : GaugeExpSt :=
  GE.gauge_exp_identity germ_expAdd_and_evConst.1 germ_expAdd_and_evConst.2 canonGauge_sub_isBiadd
    quadDeriv_of_biadditive HalfIdentity.halfSt

theorem canonGauge_independence_all : AdmissibilitySecond ∧ GaugeExpSt ∧ GaugeIndependenceColumns ∧ NabTransSt :=
  ⟨G2.galois_twist_preserves_siegel_bound germ_expAdd_and_evConst.1 germ_expAdd_and_evConst.2 canonGauge_sub_isBiadd
      quadDeriv_of_biadditive (wickVanish_of_half HalfIdentity.halfSt),
    gaugeExp_holds, WickVanishing.gauge_second_columns_of_exp gaugeExp_holds, WickVanishing.connection_translation_of_poly ChartTrans.transPolySt⟩

end GlobalTheory
end

