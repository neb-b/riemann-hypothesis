module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0647
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0643
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0648
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrability
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

theorem integral_nonneg_real {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : 0 ≤ (∫ x, f x ∂μ).re ∧ (∫ x, f x ∂μ).im = 0 := by
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) integral_complex_ofReal
    exact Complex.ext (by simp) (by simp [(hn x).2])
  rw [e2]
  exact ⟨by simpa using integral_nonneg fun x => (hn x).1, by simp⟩

theorem lintegral_enorm_eq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (hf : Integrable f μ)
    (hn : ∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) : ∫⁻ x, ‖f x‖ₑ ∂μ = ‖∫ x, f x ∂μ‖ₑ := by
  have e : ∀ x, f x = ((f x).re : ℂ) := fun x => Complex.ext (by simp) (by simp [(hn x).2])
  have hr : Integrable (fun x => (f x).re) μ := hf.re
  have h0 : 0 ≤ ∫ x, (f x).re ∂μ := integral_nonneg fun x => (hn x).1
  have e2 : ∫ x, f x ∂μ = ((∫ x, (f x).re ∂μ : ℝ) : ℂ) := by
    exact Eq.trans (integral_congr_ae (ae_of_all _ e)) integral_complex_ofReal
  have e3 : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x).re := fun x => by
    conv_lhs => rw [e x]
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hn x).1]
  rw [lintegral_congr e3, ← ofReal_integral_eq_lintegral_ofReal hr (ae_of_all _ fun x => (hn x).1), e2,
    ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg h0]

variable {D : D7}

theorem integrable_ik {θ : InfFam D} (hθ : IsInfFam θ) {T T' : HSp D} {t n : ℕ} (d : HypDec T T' t)
    (μ : Measure (Mx D t n)) [μ.IsAddHaarMeasure] {Φ : Mx D T.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ T.rank n)
    (a : Mx D T'.rank n) : Integrable (fun x : Mx D t n => Φ (d.jX ⬝ x + d.j0 ⬝ a)) μ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, h⟩ := h
    exact (GlobalTheory.RegSch.IkSchwartz.pure d hθ μ f g hg Φ h).1 a
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

theorem integrable_K {T : HSp D} {n : ℕ} {K : Subgroup (GA D T)} (hK : IsCompact (K : Set (GA D T))) (ν : Measure K)
    [IsProbabilityMeasure ν] {Φ : Mx D T.rank n → ℂ} (hΦ : Continuous Φ) (x : Mx D T.rank n) :
    Integrable (fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x)) ν := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  have hB : BorelSpace (GA D T) := ⟨rfl⟩
  have hKB : BorelSpace K := Subtype.borelSpace _
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hc : Continuous fun k : K => Φ (mm (mt T ((k : GA D T)⁻¹)) x) :=
    hΦ.comp (((continuous_mt T).comp continuous_subtype_val.inv).matrix_mul continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end GlobalTheory.CompanionTheory.ColumnSplitting.IkLintProof

namespace GlobalTheory.CompanionTheory.ColumnSplitting


open IkLintProof in
theorem ikLint : IkLint := by
  intro D n t B W d I θ hθ M hM hn a
  haveI := I.probK
  obtain ⟨𝓕, hμ⟩ := I.cov₁
  haveI := hμ.1
  have hK := (GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d I.good).2
  have hP : projS I.νK M ∈ schwartzA θ B.rank n := _root_.GlobalTheory.CompactAvgSchwartz.projS_mem D θ hθ B n I.l.K hK I.νK I.probK _ hM
  have hc : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hi := fun x => integrable_K hK I.νK hc x
  have inner : ∀ x, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) x)‖ₑ ∂I.νK = ‖projS I.νK M x‖ₑ :=
    fun x => lintegral_enorm_eq (hi x) fun k => hn _
  have pos : ∀ x, 0 ≤ (projS I.νK M x).re ∧ (projS I.νK M x).im = 0 :=
    fun x => integral_nonneg_real fun k => hn _
  rw [lintegral_congr fun U => inner _]
  exact lintegral_enorm_eq (integrable_ik hθ d I.μ₁ hP a) fun U => pos _

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResABound
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem resA_lim (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) (f : ℝ → G D p → ℂ)
    (hc : ContinuousOn (fun u : ℝ × G D p => f u.1 u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ))
    (hl : ∀ σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1), IsLaw 1 (σ : ℂ) (f σ)) (a : ℂ)
    (ha : Tendsto (fun σ : ℝ => ((σ - p / 2 : ℝ) : ℂ) * eisS (f σ) 1) (𝓝[>] ((p : ℝ) / 2)) (𝓝 a)) :
    IsRho (f (p / 2)) ∧ a = resA H (f (p / 2)) 1 := by
  have hm : (p : ℝ) / 2 ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨le_rfl, by linarith⟩
  have hc0 : Continuous (f ((p : ℝ) / 2)) :=
      ContinuousOn.comp_continuous (f := fun g : G D p => (((p : ℝ) / 2, g) : ℝ × G D p)) hc
        (continuous_const.prodMk continuous_id) fun g => ⟨hm, mem_univ _⟩
  have h2 := hl _ hm
  have e : ((((p : ℝ) / 2 : ℝ)) : ℂ) = (p : ℂ) / 2 := by push_cast; ring
  rw [e] at h2
  have hf0 : IsRho (f (p / 2)) := And.intro hc0 h2
  refine ⟨hf0, ?_⟩
  have hc' : ContinuousOn (fun u : ℝ × G D p => fam H (f (p / 2)) ((p : ℂ) / 2) (u.1 : ℂ) u.2) (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ univ) :=
    (fam_cont hH hf0.1 _).continuousOn
  have h00 : f ((p : ℝ) / 2) = (fun σ : ℝ => fam H (f (p / 2)) ((p : ℂ) / 2) (σ : ℂ)) ((p : ℝ) / 2) := (fam_at H (f (p / 2))).symm
  have hd := tendsto_diff hS hp hH hC hcov (S := f) (S' := fun σ => fam H (f (p / 2)) ((p : ℂ) / 2) (σ : ℂ)) hc
    hc' hl (fun σ _ => fam_law_real hH hf0 σ) h00
  have h1 := (ha.sub hd).mono_left (ufil_le p)
  rw [sub_zero] at h1
  have h3 : Tendsto (fun σ => res H (f (p / 2)) σ 1) ((ufil p : Ultrafilter ℝ) : Filter ℝ) (𝓝 a) := by
    refine h1.congr fun σ => ?_
    simp only [res]
    ring
  exact tendsto_nhds_unique h3 (res_tendsto hS hp hH hC hcov hf0 1)

theorem rho_add {f f' : G D p → ℂ} (hf : IsRho f) (hf' : IsRho f') : IsRho (f + f') := by
  refine ⟨hf.1.add hf'.1, fun q hq a ha g => ?_⟩
  simp only [Pi.add_apply, hf.2 q hq a ha g, hf'.2 q hq a ha g]; ring

theorem rho_smul {f : G D p → ℂ} (hf : IsRho f) (c : ℂ) : IsRho (c • f) := by
  refine ⟨continuous_const.smul hf.1, fun q hq a ha g => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hf.2 q hq a ha g]; ring

theorem fam_add (H : G D p → ℝ≥0) (f f' : G D p → ℂ) (s z : ℂ) : fam H (f + f') s z = fam H f s z + fam H f' s z := by
  funext g; simp [fam, mul_add]

theorem fam_smul (H : G D p → ℝ≥0) (f : G D p → ℂ) (c s z : ℂ) : fam H (c • f) s z = c • fam H f s z := by
  funext g; simp only [fam, Pi.smul_apply, smul_eq_mul]; ring

theorem resA_add (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f f' : G D p → ℂ} (hf : IsRho f) (hf' : IsRho f') (h : G D p) :
    resA H (f + f') h = resA H f h + resA H f' h := by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov (rho_add hf hf') h) ?_
  refine ((res_tendsto hS hp hH hC hcov hf h).add (res_tendsto hS hp hH hC hcov hf' h)).congr' ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ
  have c1 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) h
  have c2 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf'.1 _ σ) (fam_law_real hH hf' σ) h
  simp only [res, fam_add, eisS]
  rw [cosetSum_add c1 c2]; ring

theorem resA_smul (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (c : ℂ) (h : G D p) :
    resA H (c • f) h = c * resA H f h := by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov (rho_smul hf c) h) ?_
  refine ((res_tendsto hS hp hH hC hcov hf h).const_mul c).congr fun σ => ?_
  simp only [res, fam_smul, eisS]
  rw [cosetSum_smul]; ring

theorem npow_real {r : ℝ≥0} (σ : ℝ) : npow r ((σ : ℂ) - (p : ℂ) / 2) = (((r : ℝ) ^ (σ - p / 2) : ℝ) : ℂ) := by
  rw [npow, Complex.ofReal_cpow r.coe_nonneg]; push_cast; rfl

theorem resA_pos (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f)
    (hpos : ∀ g, 0 ≤ (f g).re ∧ (f g).im = 0) (h : G D p) : 0 ≤ (resA H f h).re ∧ (resA H f h).im = 0 := by
  have hT := res_tendsto hS hp hH hC hcov hf h
  have hev : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), 0 ≤ (res H f σ h).re ∧ (res H f σ h).im = 0 := by
    refine ufil_le p ?_
    filter_upwards [ev_Ioc p] with σ hσ
    have c1 := conv_of_section hS hp hH hC hcov hσ (fam_cont_at hH hf.1 _ σ) (fam_law_real hH hf σ) h
    have hsum : Summable (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h) := c1.of_norm
    have hterm : ∀ q, 0 ≤ (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h q).re ∧
        (term (P D p) (GF D p) (fam H f ((p : ℂ) / 2) (σ : ℂ)) h q).im = 0 := fun q => by
      simp only [term, fam]
      rw [npow_real, Complex.re_ofReal_mul, Complex.im_ofReal_mul, (hpos _).2, mul_zero]
      exact ⟨mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (hpos _).1, rfl⟩
    have e1 : (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) h).re ≥ 0 := by
      simp only [eisS, cosetSum]
      rw [Complex.re_tsum hsum]
      exact tsum_nonneg fun q => (hterm q).1
    have e2 : (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) h).im = 0 := by
      simp only [eisS, cosetSum]
      rw [Complex.im_tsum hsum]
      simp only [hterm, tsum_zero]
    simp only [res]
    rw [Complex.re_ofReal_mul, Complex.im_ofReal_mul, e2, mul_zero]
    exact ⟨mul_nonneg (by linarith [hσ.1]) e1, rfl⟩
  have hre := (Complex.continuous_re.tendsto _).comp hT
  have him := (Complex.continuous_im.tendsto _).comp hT
  exact ⟨ge_of_tendsto hre (hev.mono fun σ h => h.1),
    tendsto_nhds_unique him (tendsto_const_nhds.congr' (hev.mono fun σ h => h.2.symm))⟩

theorem resA_bound (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) (H' : G D p → ℝ≥0) (hH' : IsHt H') :
    ∃ K : ℝ, ∀ f, IsRho f → ∀ B : ℝ, (∀ g, ‖f g‖ ≤ B * (H' g : ℝ) ^ p) → ‖resA H f 1‖ ≤ K * B := by
  have hs : IsRho fun g => npow (H' g) (p : ℂ) := by
    refine ⟨continuous_npow hH'.1 hH'.2.1 _, fun q hq a ha g => ?_⟩
    show npow (H' (q * g)) (p : ℂ) = _ * npow (absA D _) ((p : ℂ) / 2 + (p : ℂ) / 2) * npow (H' g) (p : ℂ)
    rw [hH'.2.2 q hq a ha g, npow_mul, show (p : ℂ) / 2 + (p : ℂ) / 2 = p by ring]
    simp
  obtain ⟨δ, hδ⟩ := rho_bound hH hC hcov hs
  have hle : ∀ g, (H' g : ℝ) ^ p ≤ δ * (H g : ℝ) ^ p := fun g => by
    have := hδ g
    rwa [norm_npow (hH'.2.1 g), show ((p : ℂ)).re = (p : ℝ) by simp, Real.rpow_natCast] at this
  obtain ⟨B₁, -, hB₁⟩ := res_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  refine ⟨δ * B₁, fun f hf B hB => ?_⟩
  have hB0 : 0 ≤ B := by
    have h1 := (norm_nonneg _).trans (hB 1)
    exact nonneg_of_mul_nonneg_left h1 (pow_pos (NNReal.coe_pos.2 (hH'.2.1 1)) p)
  have hf2 : ∀ g, ‖f g‖ ≤ (B * δ) * (H g : ℝ) ^ p := fun g =>
    (hB g).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hle g) hB0)
  have hlim := (res_tendsto hS hp hH hC hcov hf 1).norm
  refine le_of_tendsto hlim ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ
  have := hB₁ f _ hf2 σ hσ 1 rfl
  calc _ ≤ B * δ * B₁ := this
    _ = _ := by ring

end GlobalTheory.CompanionTheory.ResMu
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictedProductEmbeddings
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

namespace GlobalTheory.CompanionTheory.FinActS

theorem map_list_prod_embed_of_nodup {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ)
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (f : ∀ i, Hl i) (j : ι) (l : List ι) (hl : l.Nodup) :
    p j (l.map fun i => e i (f i)).prod = if j ∈ l then f j else 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hnd := List.nodup_cons.mp hl
    have ih' := ih hnd.2
    rw [List.map_cons, List.prod_cons, map_mul, ih']
    by_cases hja : a = j
    · subst hja
      simp [hnd.1, hpe]
    · have hne : ¬ j = a := fun h => hja h.symm
      rw [hpe' a j _ hja, one_mul]
      simp [hne]

theorem exists_local_levels_le_open : ∀ {ι Γ : Type} [Group Γ] {Hl : ι → Type} [∀ i, Group (Hl i)] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [∀ i, TopologicalSpace (Hl i)] [∀ i, T2Space (Hl i)]
    (p : ∀ i, Γ →* Hl i) (e : ∀ i, Hl i →* Γ) (K : Subgroup Γ) (KH : ∀ i, Subgroup (Hl i))
    (hpc : ∀ i, Continuous (p i)) (hec : ∀ i, Continuous (e i))
    (hpe : ∀ i m, p i (e i m) = m) (hpe' : ∀ i j m, i ≠ j → p j (e i m) = 1)
    (hsep : ∀ x y : Γ, (∀ i, p i x = p i y) → x = y)
    (hK : ∀ x, x ∈ K ↔ ∀ i, p i x ∈ KH i) (hKc : IsCompact (K : Set Γ))
    (hKo : ∀ i, IsOpen (KH i : Set (Hl i))) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)),
    ∃ V : ∀ i, Subgroup (Hl i), (∀ i, IsOpen (V i : Set (Hl i))) ∧ (∀ i, V i ≤ KH i) ∧
      (∀ᶠ i in cofinite, V i = KH i) ∧ ∀ u, (∀ i, p i u ∈ V i) → u ∈ U := by
  intro ι Γ _ Hl _ _ _ _ _ p e K KH hpc hec hpe hpe' hsep hK hKc hKo U hU
  classical
  have hcomp : IsCompact ((K : Set Γ) \ (U : Set Γ)) := hKc.diff hU
  have hopen : ∀ i, IsOpen {x : Γ | p i x ≠ 1} := fun i =>
    (isOpen_ne (x := (1 : Hl i))).preimage (hpc i)
  have hcover : (K : Set Γ) \ (U : Set Γ) ⊆ ⋃ i, {x : Γ | p i x ≠ 1} := by
    intro x hx
    by_contra hcon
    have hall : ∀ i, p i x = p i 1 := by
      intro i
      by_contra hi
      exact hcon (Set.mem_iUnion.mpr ⟨i, by simpa using hi⟩)
    have hx1 : x = 1 := hsep x 1 hall
    exact hx.2 (hx1 ▸ U.one_mem)
  obtain ⟨T, hT⟩ := hcomp.elim_finite_subcover _ hopen hcover
  have hTU : ∀ x, x ∈ K → (∀ i ∈ T, p i x = 1) → x ∈ U := by
    intro x hxK hx
    by_contra hxU
    have hmem := hT ⟨hxK, hxU⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hmem
    obtain ⟨i, hi, hne⟩ := hmem
    exact hne (hx i hi)
  refine ⟨fun i => if i ∈ T then KH i ⊓ U.comap (e i) else KH i, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact (hKo i).inter (hU.preimage (hec i))
    · simp only [hi, if_false]
      exact hKo i
  · intro i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact inf_le_left
    · simp only [hi, if_false]
      exact le_rfl
  · have hfin : ∀ᶠ i in cofinite, i ∉ T := T.finite_toSet.compl_mem_cofinite
    filter_upwards [hfin] with i hi
    simp only [hi, if_false]
  · intro u hu
    have hle : ∀ i, p i u ∈ KH i := by
      intro i
      have := hu i
      by_cases hi : i ∈ T
      · simp only [hi, if_true] at this
        exact this.1
      · simpa only [hi, if_false] using this
    have huK : u ∈ K := (hK u).mpr hle
    set v : Γ := (T.toList.map fun i => e i (p i u)).prod with hv
    have hpv : ∀ j, p j v = if j ∈ T then p j u else 1 := by
      intro j
      have := map_list_prod_embed_of_nodup p e hpe hpe' (fun i => p i u) j T.toList T.nodup_toList
      simpa [hv] using this
    have hvU : v ∈ U := by
      refine U.list_prod_mem ?_
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have hiT : i ∈ T := Finset.mem_toList.mp hi
      have := hu i
      simp only [hiT, if_true] at this
      exact this.2
    have hwK : v⁻¹ * u ∈ K := by
      refine (hK _).mpr fun j => ?_
      rw [map_mul, map_inv, hpv j]
      by_cases hj : j ∈ T
      · simp [hj, (KH j).one_mem]
      · simpa [hj] using hle j
    have hwU : v⁻¹ * u ∈ U := by
      refine hTU _ hwK fun i hi => ?_
      rw [map_mul, map_inv, hpv i]
      simp [hi]
    have := U.mul_mem hvU hwU
    simpa using this

end GlobalTheory.CompanionTheory.FinActS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormula
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.CoefSum

open GlobalTheory.Published.SiegelOneVector

def flat (S : Type) [AddCommGroup S] [TopologicalSpace S] (n M : ℕ) :
    (Fin n → Fin M → S) ≃ₜ+ (Fin 1 → Fin (n * M) → S) where
  toFun X _ k := X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  invFun Y a i := Y 0 (finProdFinEquiv (a, i))
  left_inv X := by
    funext a i
    simp
  right_inv Y := by
    funext a k
    rw [Subsingleton.elim a 0]
    show Y 0 (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = Y 0 k
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
  map_add' X Y := by
    funext a k
    simp
  continuous_toFun := continuous_pi fun _ => continuous_pi fun k =>
    (continuous_apply _).comp (continuous_apply _)
  continuous_invFun := continuous_pi fun a => continuous_pi fun i =>
    (continuous_apply _).comp (continuous_apply 0)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isSchwartzBruhat_flat {n M : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    (hΦ : IsSchwartzBruhat Φ) : IsSchwartzBruhat (Φ ∘ (flat (AF F ⊗[F] E) n M).symm) := by
  obtain ⟨k, Φinf, Φf, hi, hf, hs⟩ := hΦ
  refine ⟨k, fun i => Φinf i ∘ (flat (Ainf F ⊗[F] E) n M).symm,
    fun i => Φf i ∘ (flat (Af F ⊗[F] E) n M).symm, fun i => ?_, fun i => ?_, fun Y => ?_⟩
  · obtain ⟨N, e, c1, c2, f, hfe⟩ := hi i
    let a : (Fin 1 → Fin (n * M) → Ainf F ⊗[F] E) ≃+ (Fin n → Fin M → Ainf F ⊗[F] E) :=
      (flat (Ainf F ⊗[F] E) n M).symm
    exact ⟨N, a.trans e, c1.comp (flat (Ainf F ⊗[F] E) n M).symm.continuous,
      (flat (Ainf F ⊗[F] E) n M).continuous.comp c2, f, fun X => hfe _⟩
  · exact ⟨(hf i).1.comp_continuous (flat (Af F ⊗[F] E) n M).symm.continuous,
      (hf i).2.comp_homeomorph (flat (Af F ⊗[F] E) n M).symm.toHomeomorph⟩
  · exact hs _

theorem continuous_integrable_tuple (σ : E →ₐ[F] E) [NumberField E] (hCM : IsCMExt F E σ) (M n : ℕ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : dx.IsAddHaarMeasure)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : IsSchwartzBruhat Φ) :
    Continuous Φ ∧ Integrable Φ dx := by
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hB n M
  haveI := hB 1 (n * M)
  let c := flat (AF F ⊗[F] E) n M
  haveI : (dx.map c).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map _
      (c : (Fin n → Fin M → AF F ⊗[F] E) ≃+ (Fin 1 → Fin (n * M) → AF F ⊗[F] E)).toAddMonoidHom
      c.continuous c.surjective
      c.toHomeomorph.isClosedEmbedding.tendsto_cocompact
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.PoiInt.continuous_integrable_of_isSchwartzBruhat F E σ hCM
    (n * M) (dx.map c) inferInstance _ (isSchwartzBruhat_flat hΦ)
  have hcomp : (Φ ∘ c.symm) ∘ c = Φ := by
    funext X
    simp
  refine ⟨?_, ?_⟩
  · have h : Continuous ((Φ ∘ c.symm) ∘ c) := h1.comp c.continuous
    rwa [hcomp] at h
  · have h := (c.toHomeomorph.measurableEmbedding.integrable_map_iff).1 h2
    rwa [show (Φ ∘ c.symm) ∘ c.toHomeomorph = Φ from hcomp] at h

theorem coefN_finset_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (k : ℕ) (Φ : Fin k → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  intro F E _ _ _ _ _ σ hCM M J hJ n _ hM ψ hψ dx hdx db hdb T k Φ hΦ
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, ht, -, hB, -, hG⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := hB n M
  obtain ⟨hψc, hψn, -⟩ := id hψ
  have hstar : ∀ b, starN σ J ψ dx (fun X => ∑ i, Φ i X) b = ∑ i, starN σ J ψ dx (Φ i) b := by
    intro b
    unfold starN
    simp_rw [Finset.sum_mul]
    refine integral_finsetSum _ fun i _ => ?_
    obtain ⟨hc, hi⟩ := continuous_integrable_tuple σ hCM M n dx hdx.1 (Φ i) (hΦ i)
    have hq : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E =>
        algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
          (Matrix.trace ((b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * gramR (AF F) σ J X)) :=
      continuous_const.mul (ht.comp (continuous_const.matrix_mul (hG n M J)).matrix_trace)
    refine hi.norm.mono' (hc.mul (hψc.comp hq)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, hψn, mul_one]
  unfold coefN
  simp_rw [hstar, Finset.sum_mul]
  refine integral_finsetSum _ fun i _ => ?_
  have hI := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.integrable_starN F E σ hCM M J hJ n hM ψ hψ dx hdx db hdb (Φ i) (hΦ i)
  have hc : Continuous fun b : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (b : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp (continuous_const.mul
      (ht.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace)).neg
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  refine hI.norm.mono' (hI.1.mul hc.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun b => ?_
  rw [norm_mul, hψn, mul_one]

end GlobalTheory.CompanionTheory.SiegelND.CoefSum
end

