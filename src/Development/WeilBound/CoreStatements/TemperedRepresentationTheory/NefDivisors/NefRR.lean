module

public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ProjLineLimit
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NefRR
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinrankLeAddOfMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartLatticeDimensionUpper
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0051
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0031

@[expose] public section

namespace PositivityTheory.Tls2.Nef

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem nefRR : GlobalTheory.CompanionTheory.Ar.Pub.NefRR := by
  intro K _ ι _ Ω _ _ y D a hV hB hN
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact GlobalTheory.CompanionTheory.Ar.Pub.NefRRModel.nefRR_dimZero y a hV hB
  obtain ⟨e, c, hc, hmem⟩ := _root_.GlobalTheory.CompanionTheory.Conductor.exists_conductor_section K ι Ω y D hV hB
  have hinj : Function.Injective (LinearMap.mulLeft ℚ c) := mul_right_injective₀ hc
  have hle : ∀ τ : ℕ, (Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c) ≤
      chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
    intro τ
    rintro _ ⟨s, hs, rfl⟩
    exact hmem a τ s hs
  have hfd : ∀ τ : ℕ, FiniteDimensional ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := _root_.GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    haveI : FiniteDimensional ℚ ((Submodule.span ℚ (chartLatNm y a τ : Set Ω)).map (LinearMap.mulLeft ℚ c)) :=
      Submodule.finiteDimensional_of_le (hle τ)
    exact LinearEquiv.finiteDimensional (Submodule.equivMapOfInjective _ hinj _).symm
  have hup : ∀ τ : ℕ, Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) ≤
      Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1) := by
    intro τ
    haveI := _root_.GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y D ((τ : ℤ) • a + fun k => (e k : ℤ)) hV
    rw [(Submodule.equivMapOfInjective _ hinj (Submodule.span ℚ (chartLatNm y a τ : Set Ω))).finrank_eq]
    exact Submodule.finrank_mono (hle τ)
  have hlow : ∀ τ : ℕ, Module.finrank ℚ (chartLatQ y ((τ : ℤ) • a + 0) 1) ≤
      Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) := by
    intro τ
    haveI := hfd τ
    have hsub : chartLatQ y ((τ : ℤ) • a + 0) 1 ≤ Submodule.span ℚ (chartLatNm y a τ : Set Ω) := by
      rw [add_zero, ← chartLatQ_eq_smul_one]
      exact _root_.GlobalTheory.CompanionTheory.Ar.ChartDenom.chartLatQ_le_span_chartLatNm K ι Ω y a τ
    exact Submodule.finrank_mono hsub
  refine ⟨hfd, ?_⟩
  apply GlobalTheory.T.tendsto_of_asymptotic_bounds (fun τ => (Module.finrank ℚ (Submodule.span ℚ (chartLatNm y a τ : Set Ω)) : ℝ)) _ D
  · intro ε hε
    filter_upwards [GlobalTheory.CompanionTheory.NefLower.nef_sections_lower K ι Ω y D a 0 hD hV hB hN ε hε] with n hn
    exact hn.trans (by exact_mod_cast hlow n)
  · intro ε hε
    filter_upwards [_root_.GlobalTheory.CompanionTheory.NefSections.finrank_chartLatQ_nsmul_add_le K ι Ω y D a (fun k => (e k : ℤ)) hD hV hB hN ε hε] with n hn
    exact le_trans (by exact_mod_cast hup n) hn

end PositivityTheory.Tls2.Nef
