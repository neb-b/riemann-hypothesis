module

public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsCoordLattice
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0216
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0233
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0261
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenericCentreSpecializes
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0171
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemSpan

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have := congrArg Complex.im H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_im] using this
  have h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    have := congrArg Complex.re H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_re] using this
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3
    · exact h3
    · rw [h3] at h2
      nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨by apply Complex.ext <;> simp [hre], fun h => ?_⟩
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

end LevelTowerAlt
