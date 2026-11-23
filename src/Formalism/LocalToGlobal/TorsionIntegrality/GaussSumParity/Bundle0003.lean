module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.EqZeroOfPowEqOne
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstFirstCoboundaryThree
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SubstZeroOfConstantCoeff
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.BiextensionHypothesesOfConditions
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.TilInvariantLOf
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.FirstMomentIdempotentLaw
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementF
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
section
namespace Formalism.L2.Th1.D

theorem expSpec : ExpSpec := exponential_specification
theorem frobSq : FrobSq := frobenius_square
theorem ipLemma : IPLemma := integral_part_lemma
theorem ipClosure : IPClosure := integral_part_closure
theorem teichSigma : TeichSigma := teichmuller_sigma
theorem mulSpec : MulSpec := MulSpec_of expSpec ipLemma ipClosure
theorem betaHypOfF : BetaHypOfF := BetaHypOfF_of teichSigma
theorem letterShift : LetterShift := letter_shift
theorem shiftIP : ShiftIP := ShiftIP_of_frobSq frobSq
theorem substTil : SubstTil := subst_tilde
theorem pairRules : PairRules := PairRules_of expSpec ipLemma
theorem torusTil : TorusTil := torus_tilde
theorem mean_second_biextension_condition : MeanTorusInvariant := second_mean_condition
theorem mean_third_biextension_condition : MeanNoLowBidegreeTerms := third_mean_condition
theorem torus_sum_coboundary_condition : TorusSumCoboundaryCondition := fourth_condition_of_pairing_rules pairRules substTil shiftIP letterShift
theorem biextension_hypotheses_of_level_one : MeanBiextensionHypothesesOfCocycle := biextension_hypotheses_of_conditions torus_sum_coboundary_condition torusTil teichSigma mean_second_biextension_condition mean_third_biextension_condition
theorem dualExpand : DualExpand := dual_expansion
theorem tilInvariantL : TilInvariantL := TilInvariantL_of pairRules substTil torusTil teichSigma shiftIP ipClosure dualExpand frobSq
theorem meanSimeqL : MeanSimeqL := MeanSimeqL_of tilInvariantL
theorem beTilXY : BeTilXY := BeTilXY_of expSpec
theorem bMinus1 : BMinus1 := BMinus1_of' expSpec
theorem meanSimeq : MeanSimeq := MeanSimeq_of' meanSimeqL beTilXY letterShift
theorem biextension_points_integral : BiextensionPointsIntegral := biextension_points_of_exp_spec expSpec meanSimeqL
theorem b0 : B0 := biextension_of_exp_spec expSpec biextension_points_integral
theorem oneLetterHalf : OneLetterHalf := OneLetterHalf_of meanSimeqL

end Formalism.L2.Th1.D
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementG
section
noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.D

open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights (Integral frameJet frameJetOne nablaO)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq cob UnrOK IsLawOfLog alG capG lsG deLoss dSet oddT)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

def ThmAEntryAll : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l →
  ∀ g2 g3 ε : MaximalUnramifiedExtension l, ‖g2‖ ≤ 1 → ‖g3‖ ≤ 1 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
  ∀ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F →
  ∀ s2 : MaximalUnramifiedExtension l, (∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α) →
  ∀ (d N0 N1 : ℕ) [NeZero d], 2 ≤ d → Even d →
  ∀ (ιr : Type) [Fintype ιr] [DecidableEq ιr] (om oms : ιr → MaximalUnramifiedExtension l), OwOK d σ om oms →
    TrDual d σ om oms → (∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ d - 1)) →
  ∀ U0 Φ : MvPowerSeries (Bool × ιr × Fin N0 × Fin N1) ℂ_[l], Integral U0 →
    MvPowerSeries.constantCoeff Φ = 0 →
    Simeq Φ (sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (cob F (phFF l g2 g3 s2 ε)))) →
    ∀ (TT : Finset (ZMod d)) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
      (hp : ∀ s c, p s c ≤ N0), (∀ s c, 1 ≤ p s c) → ∀ (I : ∀ s c, Fin (p s c) → Fin N1),
    ∀ (nu1 nu2 size : ZMod d → ℕ), (∀ s, nu1 s = colN s) →
      (∀ s, nu2 s = (Finset.univ.filter (fun c => 2 ≤ p s c)).card) → (∀ s, size s = ∑ c, p s c) →
    ∀ a : ℕ, 1 ≤ a → (∀ s, size s ≤ a) → 2 * Real.logb l a + 2 ≤ (N0 : ℝ) - 1 →
    ∀ δ : MvPolynomial (ZMod d × Fin N0 × Fin N0) ℂ_[l] →ₗ[ℂ_[l]] ℂ_[l],
      (∀ P ∈ nablaO (K := ℂ_[l]) colN p hp, ‖δ P‖ ≤ 1) →
      ‖δ (frameJet colN p hp I (thetaInZ l (MaximalUnramifiedExtension l).subtype σ om oms (Formalism.DworkPowerSeriesWeights.mvExp (-Φ) * U0)))‖ ≤
        ‖(l : ℂ_[l])‖ ^ ((∑ s ∈ TT, (topTerm l d TT nu1 nu2 s -
            gam l * (Wcap l d TT nu1 nu2 size s : ℝ))) +
          Fnum l d (fun s => (Dl d TT nu1 size s : ℝ)) -
          ((d : ℝ) * N0 * N1) * (Real.logb l (a : ℝ) + 1))

def NRCM : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), Squarefree dK → dK % 4 = 3 → Formalism.L2.Th1.CM.HasCMBy dK L →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l, Formalism.L2.Th1.CM.IsGoodModel l L ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ s2 : MaximalUnramifiedExtension l, ‖s2‖ ≤ 1 ∧
    (∃ (c : ℂ) (hc : c ≠ 0), (g2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ ∧
      (g3 : ℂ_[l]) = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ ∧
      (s2 : ℂ_[l]) = ι (Formalism.L2.Th1.F.s2 (Formalism.L2.Th1.F.scalePair L c hc))) ∧
    ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
    ∀ α : MaximalUnramifiedExtension l, ‖α‖ = 1 → σ (σ α) = α → NormRel l σ (phFF l g2 g3 s2 ε) α

end Formalism.L2.Th1.D
end
end

