module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.Bundle0005
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefRiemannRochStatement

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory

theorem nefNumerics_outright : GlobalTheory.Published.NefNumerics :=
  GlobalTheory.Published.nefNumerics_of_product_of_riemannRoch GlobalTheory.T.nef_product_nonneg GlobalTheory.T.nef_riemann_roch

end GlobalTheory
