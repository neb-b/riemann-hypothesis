module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorIntegralModel_nonempty : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (Model b N) := by
  first | (exact @GlobalTheory.UPel.HT.model_nonempty) | (exact GlobalTheory.UPel.HT.model_nonempty) | (intros; apply GlobalTheory.UPel.HT.model_nonempty  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaVectorBundleAnySpace
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC

theorem projectiveBundleFormula_vectorBundle_any_space : D1 :=
  projectiveBundleFormula_of_unitOnEtalePoints fun q _ _ N V hq => GlobalTheory.T.projectiveBundleFormula_of_discrete_spaces q N (_root_.GlobalTheory.EtC.pbf_disc q N) V hq

end GlobalTheory.EtC

end
end

