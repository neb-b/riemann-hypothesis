module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundOfCoreLaws
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralFormsLogSupNormLowerBoundAbsolute
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunJoin

theorem lamwAt_absolute : ∃ CL : ℝ, 0 < CL ∧ ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D) (CA : ℝ), ParA large₂ CA → ∀ (j : ℕ) (w : WeightFamilies.Wt D j), LAMwAt large₂ (recB h.toLawsCore) j w CL 2 := by
  obtain ⟨C0, hC0, H⟩ := _root_.GlobalTheory.lamwAt_of_lawsCore
  exact ⟨C0, hC0, fun D T h large₂ CA hP j w =>
    H D T.toCore h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore D T.toCore h.toLawsCore) large₂ hP.2.2.2.2.1 j w C0 2 le_rfl le_rfl⟩

end GlobalTheory.RunJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeightModuleIsLatticeOfShortSeriesSpan
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory

private theorem full_of_short_span {D : D7} {B : WeightFamilies.Prov D}
    {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (S : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (hs : S.sK ≠ 0) (hsp : PullbackSections.SpanAt X ka)
    (hH : WeightAlgebra.H2 X S ka wL wF)
    (hlat : Submodule.IsLattice B.KO (B.Mlat j ka)) :
    Submodule.IsFullLattice B.KO (B.Mlat j ka) := by
  letI := hlat
  refine ⟨?_⟩
  apply top_unique
  rw [← hsp]
  apply Submodule.span_le.mpr
  intro f hf
  let n : ℕ := D.host.g 0 * D.host.g 1
  let k : ℕ := D.R.f * D.R.r * ka.n
  let t : 𝓞 B.KO := S.sK * (n : 𝓞 B.KO) ^ k
  have hn : n ≠ 0 := Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have ht : (t : B.KO) ≠ 0 := by
    have hsK : (S.sK : B.KO) ≠ 0 := by exact_mod_cast hs
    have hnK : (n : B.KO) ≠ 0 := by exact_mod_cast hn
    simp only [t, map_mul, map_pow, map_natCast]
    exact mul_ne_zero hsK (pow_ne_zero _ hnK)
  have hmem : t • f ∈ B.Mlat j ka := hH.2.2.2 (by
    simp only [WeightAlgebra.PJ.Thc, WeightAlgebra.PJ.scaled]
    refine Submodule.mem_map.mpr ⟨(n : 𝓞 B.KO) ^ k • f,
      Submodule.mem_map.mpr ⟨f, hf, by simp [n, k]⟩, ?_⟩
    simp only [t, LinearMap.smul_apply, LinearMap.id_apply, mul_smul])
  have hm : t • f ∈ Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) := Submodule.subset_span hmem
  have hsm : t • f = (t : B.KO) • f := (algebraMap_smul B.KO t f).symm
  rw [hsm] at hm
  have hm' := (Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka))).smul_mem (t : B.KO)⁻¹ hm
  have heq : (t : B.KO)⁻¹ • ((t : B.KO) • f) = f := by
    rw [← mul_smul, inv_mul_cancel₀ ht, one_smul]
  rwa [heq] at hm'


theorem latAt_record : ∀ (D : D7) (T : Core D) (h : LawsCore T), GamAt T → ∀ (large₂ : SizeData₂ D) (CA : ℝ), WeightAlgebra.ParA large₂ CA → ∀ (j : ℕ) (ka : WeightFamilies.Wt D j) (P : ModuliIntegralCharts.Prov D) (X : WeightAlgebra.PJ D (recB h) P j) (S : WeightAlgebra.Scal (recB h)) (wL wF : WeightFamilies.Wt D j), S.sK ≠ 0 → PullbackSections.SpanAt X ka → WeightAlgebra.H2 X S ka wL wF → Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h) j ka := by
  intro D T h hG large₂ CA hA j ka P X S wL wF hs hsp hH
  obtain ⟨C0, -, hC⟩ := _root_.GlobalTheory.lamwAt_of_lawsCore
  apply full_of_short_span X S ka wL wF hs hsp hH
  exact PullbackSections.latOfLam D (recB h) P j X S ka wL wF large₂ C0 2 (fun i => (D.host.g_prime i).pos) hs
    (hC D T h hG large₂ hA.2.2.2.2.1 j ka C0 2 le_rfl le_rfl) hsp hH

end GlobalTheory
end

