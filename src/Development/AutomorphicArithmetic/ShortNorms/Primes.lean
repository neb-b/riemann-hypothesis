module

public import Development.AutomorphicArithmetic.ShortNorms.SmallOneOf
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc

@[expose] public section

theorem UpperTheory.T3.shortNorm : UpperTheory.T3.ShortNorm := _root_.GlobalTheory.Hk.normPrimes_short_interval_lower

theorem UpperTheory.T3.smallOne : UpperTheory.T3.SmallOne := UpperTheory.T3.smallOne_of _root_.GlobalTheory.Lin.primesRel_holds
