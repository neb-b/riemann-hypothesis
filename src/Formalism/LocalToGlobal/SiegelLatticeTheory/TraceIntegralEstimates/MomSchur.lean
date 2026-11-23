module

public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0016
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.BesselNVGClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Bundle0001

@[expose] public section

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem psiGen_const {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    psiGen k r z (fun _ => c) = psi k r z c := by
  funext g
  unfold psiGen psi ell ellA
  rw [Finset.mul_sum]




end Formalism.L2.S.Pv.Mom
