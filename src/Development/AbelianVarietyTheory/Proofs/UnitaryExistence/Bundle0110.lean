module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0219
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentWeight
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.CharacterFunction

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem natCast_mem_half {l l₂ : Level H} {pd : ℕ} {I : Ideal (𝓞 E)} (hM : l₂.M = l.M * pd)
    (hMb : l₂.Mb = l.Mb * I) : (pd : 𝓞 E) ∈ I := by
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hp : I * I.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(pd : 𝓞 E)} := by
    have h2 := l₂.prod
    rw [hMb, hM, Ideal.map_mul, mul_mul_mul_comm, l.prod, Nat.cast_mul,
      ← Ideal.span_singleton_mul_span_singleton] at h2
    refine mul_left_cancel₀ ?_ h2
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have : Ideal.span {(pd : 𝓞 E)} ≤ I := hp ▸ Ideal.mul_le_left
  exact this (Ideal.subset_span rfl)

theorem nsmul_mem_smul_top {R L : Type} [CommRing R] [AddCommGroup L] [Module R L] {I : Ideal R} {N : ℕ}
    (h : (N : R) ∈ I) (x : L) : N • x ∈ (I • ⊤ : Submodule R L) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact Submodule.smul_mem_smul h trivial

end GlobalTheory.CharacterFunction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValues
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat

namespace GlobalTheory.FinalJoin.FieldAlg

theorem fnAlgClosed_of_weberIn : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l' : Level Q.H) (Xo' : Moduli (Q.Dw j) l') (c' : Coeff l') (n : ℕ), 0 < n → l'.M' ∣ n → (WeberIn Q.H c'.F n ∨ CurveOver Q.H c'.F n) → FnAlgClosed (Xo := Xo') (c := c') := by
  intro D Q hP j hj l' Xo' c' n hn hM hW
  obtain ⟨⟨ι, hι⟩, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hj
  have h6 : 6 ≤ D.R.r := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have h1 := GlobalTheory.RankOneDatum.exists_datum_rank_one D Q.H (Q.Dw j) (D.sp.W j) ι hι (by omega)
  have h0 : Q.H.rt0 ∈ c'.F := c'.le (IntermediateField.subset_adjoin _ _ (by simp))
  have hC := GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ Q.H c'.F n hn
  have hc : CurveOver Q.H c'.F l'.M' := hC.2 _ hM (hW.elim (hC.1 h0) id)
  exact GlobalTheory.CompRat.fnAlgClosed_of_curveOver_lcm _ Q.H (Q.Dw j) l' Xo' c' (by omega)
    (Or.inr (Or.inr ⟨by omega, h1⟩)) hc

end GlobalTheory.FinalJoin.FieldAlg
end

