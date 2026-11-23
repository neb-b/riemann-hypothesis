module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
section
namespace Formalism.L2.Th1.E

theorem nonsingNorm : NonsingNorm := nonsingular_norm
theorem unitKap : UnitKap := UnitKap_of nonsingNorm
theorem unitPsi2 : UnitPsi2 := UnitPsi2_of nonsingNorm
theorem unitDiff : UnitDiff := UnitDiff_of nonsingNorm
theorem intRules : IntRules := integrality_rules
theorem unitAtRules : UnitAtRules := unit_at_rules
theorem rootInt : RootInt := root_integral_alt
theorem gaussMul : GaussMul := gauss_multiplicative
theorem xTShape : XTShape := XTShape_holds
theorem facShape : FacShape := FacShape_of intRules unitAtRules unitKap unitPsi2 unitDiff xTShape
theorem transPower : TransPower := translate_power
theorem parSumTwo : ParSumTwo := parallelogram_sum_two
theorem transUnit : TransUnit := TransUnit_of intRules unitAtRules rootInt facShape transPower
theorem transGauss : TransGauss := TransGauss_of intRules unitAtRules transUnit

theorem prodInt : ProdInt := product_integral
theorem substExpInt : SubstExpInt := subst_exp_integral
theorem congIffSimeq : CongIffSimeq := congruence_iff_simeq
theorem sumEBridge : SumEBridge := sum_series_analytic
theorem mapCob : MapCob := map_coboundary

end Formalism.L2.Th1.E
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
section
open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

section Gen

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l])

def Unif : Prop := Formalism.L2.Th1.A.g₂ W = ι L.g₂ ∧ Formalism.L2.Th1.A.g₃ W = ι L.g₃


open Classical in
def ptW (t : ℂ) : W.toAffine.Point :=
  if h : t ∉ L.lattice ∧ W.toAffine.Nonsingular (ι (L.weierstrassP t) - W.b₂ / 12)
      ((ι (L.derivWeierstrassP t) - W.a₁ * (ι (L.weierstrassP t) - W.b₂ / 12) - W.a₃) / 2)
  then .some _ _ h.2 else 0

def inW (f : ℂ → ℂ) : PowerSeries ℂ_[l] :=
  (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.taylor0 f)).subst (Formalism.L2.Th1.A.logSer W)

def phW : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.phO (ι (Formalism.L2.Th1.F.s2 L)) (PowerSeries.map (ι : ℂ →+* ℂ_[l]) (Formalism.L2.Th1.F.pSeries L))
    (Formalism.L2.Th1.A.logSer W)

def gW (t : ℂ) : PowerSeries ℂ_[l] :=
  Formalism.L2.Th1.B.fExp (phW l L ι W) * inW l ι W (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L))

end Gen


open Classical in
def PtWAdd : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ s t : ℂ, ptW l L ι W (s + t) = ptW l L ι W s + ptW l L ι W t

def PtWZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ t : ℂ, ptW l L ι W t = 0 ↔ t ∈ L.lattice


open Classical in
def AnalyticSysW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    ∀ (π : ℂ →+ W.toAffine.Point), (∀ t, π t = ptW l L ι W t) → IsTransSys W π (gW l L ι W)

def AnalyticTransW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W →
    ∀ (t : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      ‖ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0)‖ = 1 ∧
      OneUnit (C (ι (Formalism.L2.Th1.F.opU L t (Formalism.L2.Th1.F.sgStar L) 0))⁻¹ * gW l L ι W t)

def ShiftAnalyticW : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (W : WeierstrassCurve ℂ_[l]), Unif l L ι W →
    IntCurve W → ∀ ω₀ : ℂ, ω₀ ∈ L.lattice → ω₀ / 2 ∉ L.lattice →
    ‖px W (ptW l L ι W (ω₀ / 2))‖ ≤ 1 → OneUnit (inW l ι W (Formalism.L2.Th1.F.th0 L (ω₀ / 2))) →
    ∀ (s : ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) * s ∈ L.lattice →
      GaussOne (inW l ι W (Formalism.L2.Th1.F.opU L s (Formalism.L2.Th1.F.th0 L (ω₀ / 2))))

end Formalism.L2.Th1.E
end
end

