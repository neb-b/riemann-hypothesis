module

public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0002
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.GaussElementarySymmetric
public import Mathlib
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementC
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ABArith
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.FinsuppStepInduction
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.MinorProdBlockDegree
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormNatCastLeOfDvd
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EDecomp
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.NormLeOfDvd
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EntryAOneParity
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EntryATwoAndB
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EJoint
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.MPlaces
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.CyclicPowerClassOfExpEquiv
public import Formalism.GaussJetBounds.StatementI
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne
public import Formalism.GrowthSums.FactorialBaseGrowth.Bundle0002

@[expose] public section

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

theorem e_one_identity : JetPairingHasseIdentity := e_one_identity_of
theorem e_one_integral : HasseDerivIntegralHomogeneous := e_one_integral_of
theorem e_one_vanish : HasseDerivProdVanish := e_one_vanish_of
theorem minorHits : MinorHits := minor_hits
theorem starArith : StarArith := gainFactorialInequality
theorem chargeLemma : ChargeLemma := cyclicShiftLeast
theorem entry_a_one_bound : ExcessGainBound := excessGainBound
theorem bCore : BCore := cappedGainBound
theorem hitsCapPos : HitsCapPos := HitsCapPos_of e_one_vanish minorHits
theorem hitsColumnsPos : HitsColumnsPos := HitsColumnsPos_of e_one_vanish minorHits
theorem hasseDegree : HasseDegree := hasseDerivSupport
theorem minorProdDegree : MinorProdDegree := minorProdBlockDegree
theorem termBound : TermBound := TermBound_of e_one_identity e_one_integral
theorem hhDecomp : HhDecomp := decomposition_of_hh
theorem entryStar : EntryStar :=
  EntryStar_of termBound hhDecomp classSubst Formalism.DworkPowerSeriesWeights.jet_pair_linearity starArith hasseDegree
    minorProdDegree

theorem entry_a_one : EntryExcessBound := entryExcessBound_of entryStar hitsCapPos entry_a_one_bound chargeLemma
theorem entry_a_two : EntryCappedBound := entryCappedBound_of entryStar hitsCapPos Formalism.GrowthSums.cappedGainSubLE
theorem entryB : EntryB := EntryB_of entryStar hitsCapPos hitsColumnsPos bCore

end Formalism.InvariantFactorPaths.G7.Top
