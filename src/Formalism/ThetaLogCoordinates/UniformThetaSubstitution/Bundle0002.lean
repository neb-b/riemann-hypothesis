module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LocalComponentGL
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.IntegralPderivLgF
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NotDvdChoosePowMul
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LemmaTwoOf
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ScalingSwapLemmas
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ConstantCoeffLawFirstTwoOfThree
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.PartialCoboundaryLinear
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ConstantCoeffFirstTwoOfThree
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormLiftLeOne
public import Mathlib
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
public import Formalism.GaussJetBounds.StatementP

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
section
namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem frobExprG : FrobExprG := frobenius_expression_g
theorem valTable : ValTable := valuation_table
theorem expIntegral : ExpIntegral := exp_integral
theorem classChange : ClassChange := classChange_statement
theorem classMul : ClassMul := class_multiplication
theorem classSubst : ClassSubst := class_substitution
theorem classExp : ClassExp := class_exponential
theorem rescaleExact : RescaleExact := RescaleExact_of valTable expIntegral
theorem rescaleCore : RescaleCore := RescaleCore_of rescaleExact classExp classMul

theorem dworkMv : DworkMv := dwork_multivariable
theorem simeqRules : SimeqRules := equivalence_rules
theorem logRescale : LogRescale := log_rescale_alt
theorem logRescaleUnique : LogRescaleUnique := log_rescale_unique
theorem twoSums : TwoSums := two_sums
theorem thmSCore : ThmSCore :=
  ThmSCore_of rescaleCore classSubst classChange classMul twoSums logRescale logRescaleUnique
theorem theorem_s_from_k_one : CyclicPowerClassOfExpEquiv := theorem_s_from_k_one_of thmSCore simeqRules

theorem lawExists : LawExists := formal_law_exists
theorem lawSymm : LawSymm := formal_law_symmetric
theorem divDeriv : DivDeriv := divided_derivative
theorem deIntegral : DeIntegral := DeIntegral_of divDeriv lawSymm
theorem derivA : DerivA := derivative_a
theorem lemmaOne : LemmaOne := LemmaOne_of deIntegral lawSymm
theorem lemmaTwo : LemmaTwo := LemmaTwo_of lemmaOne lawSymm
theorem lamModule : LamModule := LamModule_of dworkMv
theorem zeroCondition : StepZero := StepZero_of lamModule simeqRules lawSymm
theorem firstDeriv : FirstDeriv := FirstDeriv_of lawSymm
theorem cobLin : CobLin := CobLin_of lawSymm
theorem stepI : StepI := StepI_of lemmaOne firstDeriv cobLin
theorem stepII : StepII := StepII_of dworkMv divDeriv deIntegral lawSymm
theorem swapRules : SwapRules := swap_rules
theorem stepH : StepH := StepH_of lemmaTwo swapRules lawSymm
theorem stepIII : StepIII := c_add_sigma_c_eq_zero
theorem stepIV : StepIV := StepIV_of dworkMv
theorem mapSimeq : MapSimeq := mapSimeq_statement
theorem betaIsG : BetaIsG :=
  BetaIsG_of zeroCondition stepI stepII stepH stepIII stepIV swapRules simeqRules

end Formalism.InvariantFactorPaths.G7.Top
end

-- bundled from Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementG
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral frameJet)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

section Shape

variable {ν : ℕ}

def alG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  if s ∈ TT then (univ.filter (fun c => hts s c = 1)).card else 0

def capG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  colN s - alG TT colN hts s

def lsG (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (s : ZMod (2 * ν)) : ℕ :=
  ∑ c, hts s c - alG TT colN hts s

end Shape

end Formalism.InvariantFactorPaths.G7
end
end

