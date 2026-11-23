module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JacquetShalikaRigidity
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport

@[expose] public section

namespace GlobalTheory.Fc.S0

structure Hypotheses2 : Prop extends Hypotheses1 where
  litN : GlobalTheory.Mem.LiteralAutomorphy.LitN
  toHypothesesX : GlobalTheory.NRows.HypothesesX
  nLink : GlobalTheory.NLink.Hypotheses₂
  depthZeroWild' : GlobalTheory.Published.DepthZeroWild
  depthZeroSupport' : GlobalTheory.Published.DepthZeroSupport

end GlobalTheory.Fc.S0
