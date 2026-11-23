module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassSumDenominatorBoundOfCmThetaHypotheses
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem intSt_and_archSt : IntSt ∧ ArchSt :=
  ⟨_root_.GlobalTheory.NormSum.DenomBound.intSt_of_forall_inp _root_.GlobalTheory.NormSum.inp_all, _root_.GlobalTheory.ArchTop.archSt_of_inp _root_.GlobalTheory.NormSum.inp_all⟩

end GlobalTheory.NormSum
