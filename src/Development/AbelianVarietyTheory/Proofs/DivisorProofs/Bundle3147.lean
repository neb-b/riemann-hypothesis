module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2839
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiProjectiveHarrisTaylorFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quasiProjective_harrisTaylor_family : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∃ F : RepFam b N, IsQProjOver F.s := by
  first | (exact @GlobalTheory.UPel.HT.exists_repFam_qproj) | (exact GlobalTheory.UPel.HT.exists_repFam_qproj) | (intros; apply GlobalTheory.UPel.HT.exists_repFam_qproj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationHolds
section
namespace GlobalTheory

open NumberField

theorem toroidalCompactification_holds : GlobalTheory.Published.ToroidalCompactification := by
  intro E _ _ _ H Dw hr l Xo c
  obtain ⟨φs, hs, -⟩ := _root_.GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt (max 1 (Module.finrank ℚ E * min Dw.p Dw.q))
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  obtain ⟨Y, -, -, -, -, -, a₁, a₂, a₃, -⟩ := GlobalTheory.Published.ToroidalForFanKS.exists_model_of_fan _root_.GlobalTheory.TorKSField.toroidalForFanKS hr h₁ h₂ Xo c
  exact ⟨Y, a₁, a₂, a₃⟩

end GlobalTheory
end

