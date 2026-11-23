module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralTsumNormalEigenfunctionsEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
namespace GlobalTheory.CutSum

open Filter Topology

theorem measurable_tsum_of_summable {X I : Type} [MeasurableSpace X] [Countable I]
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (hs : ∀ x, Summable fun i => F i x) :
    Measurable fun x => ∑' i, F i x :=
  measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (f := fun s x => ∑ i ∈ s, F i x) (fun s => Finset.measurable_sum s fun i _ => hF i)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

theorem summable_of_tsum_enorm_ne_top {I : Type} (f : I → ℂ) (h : ∑' i, ‖f i‖ₑ ≠ ⊤) :
    Summable f := by
  refine Summable.of_norm ?_
  simp only [enorm_eq_nnnorm] at h
  exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h)

theorem integrableOn_of_enorm_le {X : Type} [MeasurableSpace X] {μ : Measure X} {s : Set X}
    (hs : μ s ≠ ⊤) {φ : X → ℂ} (hφ : Measurable φ) (B : NNReal) (hb : ∀ x, ‖φ x‖ₑ ≤ B) :
    IntegrableOn φ s μ := by
  refine ⟨hφ.aestronglyMeasurable, ?_⟩
  show ∫⁻ x in s, ‖φ x‖ₑ ∂μ < ⊤
  exact (lintegral_mono hb).trans_lt
    ((setLIntegral_const s _).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hs.lt_top))

end GlobalTheory.CutSum


open GlobalTheory.CutSum in
theorem GlobalTheory.CutSum.integral_tsum_eq_zero : ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (ν : Measure N) [ν.IsHaarMeasure] (Γ M : Subgroup N), Countable Γ → DiscreteTopology Γ → M.Normal → IsClosed (M : Set N) → (∃ K : Set M, IsCompact K ∧ ∀ m, ∃ γ ∈ Γ.subgroupOf M, ∃ k ∈ K, m = γ * k) → ∀ 𝓝 : Set N, IsFundamentalDomain Γ 𝓝 ν → ν 𝓝 ≠ ⊤ → ∀ (I C : Type) [Countable I] (κ : I → C) (F : I → N → ℂ), (∀ i, Measurable (F i)) → (∃ B : NNReal, ∀ n, ∑' i, ‖F i n‖ₑ ≤ B) → (∀ γ ∈ Γ, ∀ n, ∑' i, F i (γ * n) = ∑' i, F i n) → (∀ c, ∀ γ ∈ Γ, γ ∈ M → ∀ n, ∑' i : {i // κ i = c}, F i (γ * n) = ∑' i : {i // κ i = c}, F i n) → (∀ c, ∃ u ∈ M, ∃ a : ℂ, a ≠ 1 ∧ ∀ i, κ i = c → ∀ m ∈ M, ∀ n, F i (m * u * n) = a * F i (m * n)) → ∫ n in 𝓝, ∑' i, F i n ∂ν = 0 := by
  intro N _ _ _ _ _ _ _ _ ν _ Γ M hΓc hΓd hMn hMc hK 𝓝 h𝓝 h𝓝fin I C _ cl F hFm hB hΓ hcl heig
  classical
  haveI := hΓd
  haveI : LocallyCompactSpace M := hMc.locallyCompactSpace
  haveI : SecondCountableTopology M := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace M := Subtype.borelSpace _
  obtain ⟨B, hB⟩ := hB

  have hinj : Function.Injective fun γ : Γ.subgroupOf M =>
      (⟨(γ : M), Subgroup.mem_subgroupOf.1 γ.2⟩ : Γ) :=
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : Γ => (x : N)) h))
  haveI : Countable (Γ.subgroupOf M) := hinj.countable
  haveI : DiscreteTopology (Γ.subgroupOf M) := DiscreteTopology.of_continuous_injective
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hinj
  let μM : Measure M := Measure.haar
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf M)
  have hDf : μM D ≠ ⊤ := by
    obtain ⟨K, hKc, hKcov⟩ := hK
    refine ne_top_of_le_ne_top hKc.measure_lt_top.ne
      (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hD μM) (D' := K)
        (Filter.Eventually.of_forall fun m => ?_))
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hKcov m
    refine ⟨⟨γ, hγ⟩⁻¹, ?_⟩
    show ((⟨γ, hγ⟩⁻¹ : Γ.subgroupOf M) : M) * (γ * k) ∈ K
    rw [Subgroup.coe_inv, Subgroup.coe_mk, inv_mul_cancel_left]
    exact hk
  have hR : ∀ u : M, μM.map (· * u) = μM :=
    GlobalTheory.haar_map_mul_right_eq_of_fundamentalDomain N Γ M hΓc hMc μM D inferInstance (hD μM) hDf

  have hs : ∀ n, Summable fun i => F i n := fun n =>
    summable_of_tsum_enorm_ne_top _ (ne_top_of_le_ne_top ENNReal.coe_ne_top (hB n))
  let g : I → Set.range cl := Set.rangeFactorization cl
  haveI : Countable (Set.range cl) := (Set.countable_range cl).to_subtype
  let G : Set.range cl → N → ℂ := fun c n => ∑' i : {i // cl i = c.1}, F i n
  have hfib : ∀ c n, ∑' b : ↑(g ⁻¹' {c}), F b n = G c n := fun c n =>
    (Equiv.subtypeEquivRight (fun i => by
      simp [g, Set.rangeFactorization, Subtype.ext_iff])).tsum_eq
      (fun j : {i // cl i = c.1} => F j.1 n)
  have hsplit : ∀ n, ∑' i, F i n = ∑' c, G c n := fun n =>
    (((hs n).hasSum.tsum_fiberwise g).tsum_eq).symm.trans (tsum_congr fun c => hfib c n)
  have hGle : ∀ n, ∑' c, ‖G c n‖ₑ ≤ B := fun n => by
    calc ∑' c, ‖G c n‖ₑ ≤ ∑' c, ∑' b : ↑(g ⁻¹' {c}), ‖F b n‖ₑ :=
          ENNReal.tsum_le_tsum fun c => by rw [← hfib c n]; exact enorm_tsum_le_tsum_enorm
      _ = ∑' i, ‖F i n‖ₑ := ENNReal.tsum_fiberwise (fun i => ‖F i n‖ₑ) g
      _ ≤ B := hB n
  have hGm : ∀ c, Measurable (G c) := fun c =>
    measurable_tsum_of_summable (fun i : {i // cl i = c.1} => F i) (fun i => hFm i)
      (fun n => (hs n).comp_injective Subtype.val_injective)
  have hfm : Measurable fun n => ∑' i, F i n := measurable_tsum_of_summable F hFm hs

  have hzero : ∀ c (h : N), ∫ m in D, G c ((m : N) * h) ∂μM = 0 := by
    intro c h
    obtain ⟨u, huM, a, ha1, hu⟩ := heig c.1
    set φ : M → ℂ := fun m => G c ((m : N) * h) with hφ
    have hφm : Measurable φ := (hGm c).comp (measurable_subtype_coe.mul_const h)
    have hφint : IntegrableOn φ D μM :=
      integrableOn_of_enorm_le hDf hφm B fun m => (ENNReal.le_tsum c).trans (hGle _)
    have hinv : ∀ γ ∈ Γ.subgroupOf M, ∀ m : M, φ (γ * m) = φ m := by
      intro γ hγ m
      show G c (((γ * m : M) : N) * h) = G c ((m : N) * h)
      rw [Subgroup.coe_mul, mul_assoc]
      exact hcl c.1 γ (Subgroup.mem_subgroupOf.1 hγ) γ.2 _
    have hshift : ∀ m : M, φ (m * ⟨u, huM⟩) = a * φ m := by
      intro m
      show G c (((m * ⟨u, huM⟩ : M) : N) * h) = a * G c ((m : N) * h)
      rw [Subgroup.coe_mul, Subgroup.coe_mk]
      show ∑' i : {i // cl i = c.1}, F i ((m : N) * u * h)
        = a * ∑' i : {i // cl i = c.1}, F i ((m : N) * h)
      rw [← tsum_mul_left]
      exact tsum_congr fun i => hu i i.2 m m.2 h
    have key := (GlobalTheory.fundamentalDomain_setIntegral_mul_right (Γ.subgroupOf M) μM D (hD μM)
      ⟨u, huM⟩ (hR _) φ hinv hφint).2
    simp only [hshift, integral_const_mul] at key
    have h2 : (a - 1) * ∫ m in D, φ m ∂μM = 0 := by rw [sub_mul, one_mul, key, sub_self]
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha1)

  have hmean : ∀ h : N, ∫ m in D, (∑' i, F i ((m : N) * h)) ∂μM = 0 := by
    intro h
    have hm : ∀ c, Measurable fun m : M => G c ((m : N) * h) := fun c =>
      (hGm c).comp (measurable_subtype_coe.mul_const h)
    simp_rw [hsplit]
    rw [integral_tsum (fun c => (hm c).aestronglyMeasurable) ?_]
    · simp [hzero]
    · rw [← lintegral_tsum (fun c => (hm c).enorm.aemeasurable)]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := B)) hDf) ?_
      exact (lintegral_mono fun m => hGle _).trans_eq (setLIntegral_const D _)
  have hfin := GlobalTheory.UnfoldNormal.unfold_zero_mean N ν Γ M hΓc hMc
    (fun γ _ n hn => hMn.conj_mem n hn γ) μM D inferInstance (hD μM) hDf
    (fun _ => 1) (fun n => ∑' i, F i n) measurable_const hfm (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun γ hγ n => hΓ γ hγ n) hmean 𝓝 h𝓝
    (integrableOn_of_enorm_le h𝓝fin (measurable_const.mul hfm) B fun n => by
      simpa using enorm_tsum_le_tsum_enorm.trans (hB n))
  simpa using hfin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantIntegralInStages
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal
open Filter

noncomputable section

namespace GlobalTheory.Unf

open GlobalTheory.Tw

section InductionInStages
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

theorem lintegral_eq_cutoff_inner {T : Subgroup G} {μ : Measure G} {μT : Measure T}
    [SFinite μ] [μ.IsMulLeftInvariant] [SFinite μT] [μT.IsInvInvariant]
    {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x, H x ∂μ = ∫⁻ x, (β x : ℝ≥0∞) * ∫⁻ t : T, H (t * x) ∂μT ∂μ := by
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  have hmul : Measurable fun p : G × T => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => ((p.2⁻¹ : T) : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd.inv).mul measurable_fst
  have e1 : ∀ x, (β x : ℝ≥0∞) * ∫⁻ t : T, H (t * x) ∂μT = ∫⁻ t : T, β x * H (t * x) ∂μT := fun x =>
    (lintegral_const_mul' _ _ ENNReal.coe_ne_top).symm
  rw [lintegral_congr e1, lintegral_lintegral_swap ((hb.comp measurable_fst).mul (hH.comp hmul)).aemeasurable]
  have e2 : ∀ t : T, ∫⁻ x, β x * H (t * x) ∂μ = ∫⁻ x, β ((t⁻¹ : T) * x) * H x ∂μ := fun t => by
    rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => β ((t⁻¹ : T) * x) * H x) t]
    simp
  rw [lintegral_congr e2,
    ← lintegral_lintegral_swap (f := fun x (t : T) => β ((t⁻¹ : T) * x) * H x)
      ((hb.comp hmul').mul (hH.comp measurable_fst)).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mul_const _ (f := fun t : T => (β ((t⁻¹ : T) * x) : ℝ≥0∞)) (hb.comp (hmul'.comp measurable_prodMk_left)),
    lintegral_inv_eq_self (μ := μT) (fun t : T => (β (t * x) : ℝ≥0∞)), hβ.2, one_mul]

theorem map_val_eq_map_stages {R₀ R : Subgroup G} (μ₀ : Measure R₀) (μR : Measure R) [SFinite μ₀]
    {U : Type} [MeasurableSpace U] (ν : Measure U) {j : U → G} (hj : Measurable j)
    (hst : ∀ F : G → ℝ≥0∞, Measurable F → ∫⁻ r : R, F r ∂μR = ∫⁻ u, ∫⁻ r : R₀, F (r * j u) ∂μ₀ ∂ν) :
    μR.map Subtype.val = (ν.prod μ₀).map (fun p : U × R₀ => (p.2 : G) * j p.1) := by
  have hm : Measurable (fun p : U × R₀ => (p.2 : G) * j p.1) :=
    (measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst)
  have key : ∀ F : G → ℝ≥0∞, Measurable F →
      ∫⁻ y, F y ∂(μR.map Subtype.val) = ∫⁻ y, F y ∂((ν.prod μ₀).map (fun p : U × R₀ => (p.2 : G) * j p.1)) := by
    intro F hF
    rw [lintegral_map hF measurable_subtype_coe, lintegral_map hF hm, lintegral_prod (f := fun p : U × R₀ => F ((p.2 : G) * j p.1)) (hF.comp hm).aemeasurable]
    exact hst F hF
  ext A hA
  rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hA]
  exact key _ (measurable_one.indicator hA)

end InductionInStages

theorem invariant_integral_in_stages : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (R₀ R : Subgroup G), IsClosed (R₀ : Set G) → IsClosed (R : Set G) → ∀ (μ₀ : Measure R₀) (μR : Measure R), μ₀.IsHaarMeasure → μ₀.IsInvInvariant → μR.IsHaarMeasure → μR.IsInvInvariant → ∀ (U : Type) [MeasurableSpace U] (ν : Measure U) [SFinite ν] (j : U → G), Measurable j → (∀ F : G → ENNReal, Measurable F → ∫⁻ r : R, F r ∂μR = ∫⁻ u, ∫⁻ r : R₀, F (r * j u) ∂μ₀ ∂ν) → ∀ f : G → ℂ, Measurable f → (∀ r ∈ R₀, ∀ g, f (r * g) = f g) → (∀ g, Integrable (fun u => f (j u * g)) ν) → (∃ z', IsQuotIntL1 μR μ (fun g => ((∫ u, ‖f (j u * g)‖ ∂ν : ℝ) : ℂ)) z') → ∀ z, IsQuotIntL1 μR μ (fun g => ∫ u, f (j u * g) ∂ν) z → IsQuotIntL1 μ₀ μ f z := by
  intro G _ _ _ _ _ _ _ _ μ _ R₀ R hR₀ hR μ₀ μR _ _ _ _ U _ ν _ j hj hst f hf hinv hint hz' z hz
  obtain ⟨z', hz'⟩ := hz'
  have : LocallyCompactSpace R₀ := hR₀.locallyCompactSpace
  have : LocallyCompactSpace R := hR.locallyCompactSpace
  have : SecondCountableTopology R₀ := TopologicalSpace.Subtype.secondCountableTopology (R₀ : Set G)
  have : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology (R : Set G)
  obtain ⟨β₀, -, hβ₀⟩ := exists_isCosetCutoff (μT := μ₀) hR₀
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μR) hR
  obtain ⟨F, hF⟩ : ∃ F : G → ℂ, F = fun x => (β₀ x : ℝ) • f x := ⟨_, rfl⟩
  have hFm : Measurable F := by rw [hF]; exact hβ₀.1.coe_nnreal_real.smul hf
  have hc0 : ∀ y, Integrable (fun r : R₀ => (β₀ (r * y) : ℝ)) μ₀ ∧ ∫ r : R₀, (β₀ (r * y) : ℝ) ∂μ₀ = 1 :=
    fun y => integrable_of_lintegral_eq_one (hβ₀.1.comp (measurable_subtype_coe.mul_const y)) (hβ₀.2 y)
  have hFe : ∀ y, ∀ r : R₀, F (r * y) = (β₀ (r * y) : ℝ) • f y := fun y r => by
    rw [hF]
    show (β₀ (r * y) : ℝ) • f (r * y) = _
    rw [hinv r r.2 y]
  have hFr : ∀ y, Integrable (fun r : R₀ => F (r * y)) μ₀ ∧ ∫ r : R₀, F (r * y) ∂μ₀ = f y := fun y => by
    simp only [hFe y]
    exact ⟨(hc0 y).1.smul_const _, by rw [integral_smul_const, (hc0 y).2, one_smul]⟩
  have hFn : ∀ y, ∫ r : R₀, ‖F (r * y)‖ ∂μ₀ = ‖f y‖ := fun y => by
    simp only [hFe y, norm_smul, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
    rw [integral_mul_const, (hc0 y).2, one_mul]
  have hFn' : ∀ y, ∫⁻ r : R₀, ‖F (r * y)‖ₑ ∂μ₀ = ‖f y‖ₑ := fun y => by
    have e : ∀ r : R₀, ‖F (r * y)‖ₑ = (β₀ (r * y) : ℝ≥0∞) * ‖f y‖ₑ := fun r => by
      rw [hFe y r, enorm_smul]
      simp
    rw [lintegral_congr e, lintegral_mul_const' _ _ enorm_ne_top, hβ₀.2, one_mul]
  have hm : Measurable (fun p : U × R₀ => (p.2 : G) * j p.1) :=
    (measurable_subtype_coe.comp measurable_snd).mul (hj.comp measurable_fst)
  have hM := map_val_eq_map_stages μ₀ μR ν hj hst
  have hP : ∀ h, Integrable ((fun y => F (y * h)) ∘ fun p : U × R₀ => (p.2 : G) * j p.1) (ν.prod μ₀) := fun h => by
    refine (integrable_prod_iff ((hFm.comp (measurable_mul_const h)).comp hm).aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine Eventually.of_forall fun u => ?_
      simpa [Function.comp_def, mul_assoc] using (hFr (j u * h)).1
    · have e : ∀ u, ∫ r : R₀, ‖((fun y => F (y * h)) ∘ fun p : U × R₀ => (p.2 : G) * j p.1) (u, r)‖ ∂μ₀ = ‖f (j u * h)‖ :=
        fun u => by simpa [Function.comp_def, mul_assoc] using hFn (j u * h)
      exact (hint h).norm.congr (Eventually.of_forall fun u => (e u).symm)
  have hRint : ∀ h, Integrable (fun r : R => F (r * h)) μR := fun h => by
    have hi : Integrable (fun y => F (y * h)) (μR.map Subtype.val) := by
      rw [hM]
      exact (integrable_map_measure (hFm.comp (measurable_mul_const h)).aestronglyMeasurable hm.aemeasurable).2 (hP h)
    exact hi.comp_measurable measurable_subtype_coe
  have hRval : ∀ h, ∫ r : R, F (r * h) ∂μR = ∫ u, f (j u * h) ∂ν := fun h => by
    have e1 : ∫ r : R, F (r * h) ∂μR = ∫ y, F (y * h) ∂(μR.map Subtype.val) :=
      (integral_map measurable_subtype_coe.aemeasurable (hFm.comp (measurable_mul_const h)).aestronglyMeasurable).symm
    rw [e1, hM, integral_map (f := fun y => F (y * h)) hm.aemeasurable (hFm.comp (measurable_mul_const h)).aestronglyMeasurable]
    have e2 := integral_prod _ (hP h)
    simp only [Function.comp_def] at e2
    rw [e2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simpa [mul_assoc] using (hFr (j u * h)).2
  have hGint : Integrable F μ := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_eq_cutoff_inner hβ hFm.enorm]
    have e : ∀ x, ∫⁻ r : R, ‖F (r * x)‖ₑ ∂μR = ∫⁻ u, ‖f (j u * x)‖ₑ ∂ν := fun x => by
      rw [hst (fun y => ‖F (y * x)‖ₑ) (hFm.comp (measurable_mul_const x)).enorm]
      refine lintegral_congr fun u => ?_
      have h1 := hFn' (j u * x)
      simp only [mul_assoc] at h1 ⊢
      exact h1
    simp only [e]
    obtain ⟨hi, -⟩ := hz'.cutoff hβ
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) hi.2
    rw [enorm_smul, ← ofReal_integral_norm_eq_lintegral_enorm (hint x)]
    simp [Real.enorm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hq : IsQuotIntL1 μR μ (fun g => ∫ u, f (j u * g) ∂ν) (∫ x, F x ∂μ) :=
    ⟨F, hGint, hRint, fun h => (hRval h).symm, rfl⟩
  exact ⟨F, hGint, fun h => (hFr h).1, fun h => (hFr h).2.symm, hz.unique hR hq⟩

end GlobalTheory.Unf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFundamentalDomainProdOfKernelImage
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped Pointwise

namespace GlobalTheory

theorem isFundamentalDomain_prod_of_ker_image : ∀ (N G : Type) [Group N] [Group G] [MeasurableSpace N] [MeasurableSpace G] [MeasurableMul N] [MeasurableMul G] (ν : Measure N) (μ : Measure G) [SFinite ν] [SFinite μ] [ν.IsMulLeftInvariant] [μ.IsMulLeftInvariant] (Γ : Subgroup (N × G)) [Countable Γ] (𝓐 : Set N) (𝓑 : Set G), IsFundamentalDomain (Γ.comap (MonoidHom.inl N G)) 𝓐 ν → IsFundamentalDomain (Γ.map (MonoidHom.snd N G)) 𝓑 μ → IsFundamentalDomain Γ (𝓐 ×ˢ 𝓑) (ν.prod μ) := by
  intro N G _ _ _ _ _ _ ν μ _ _ _ _ Γ _ 𝓐 𝓑 hA hB
  classical

  have hKc : Countable (Γ.comap (MonoidHom.inl N G)) := by
    refine Function.Injective.countable (f := fun k : Γ.comap (MonoidHom.inl N G) =>
      (⟨MonoidHom.inl N G k, k.2⟩ : Γ)) ?_
    intro a b hab
    apply Subtype.ext
    have := congrArg (fun x : Γ => (x : N × G).1) hab
    simpa using this
  have hHc : Countable (Γ.map (MonoidHom.snd N G)) := by
    refine Function.Surjective.countable (f := fun γ : Γ =>
      (⟨(γ : N × G).2, Subgroup.mem_map_of_mem _ γ.2⟩ : Γ.map (MonoidHom.snd N G))) ?_
    rintro ⟨h, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

  have hlift : ∀ h : Γ.map (MonoidHom.snd N G), ∃ m : N, ((m, (h : G)) : N × G) ∈ Γ := by
    rintro ⟨h, x, hx, rfl⟩
    exact ⟨x.1, by simpa using hx⟩
  choose mm hmm using hlift

  have memS : ∀ (γ : Γ) (p : N × G), p ∈ γ • (𝓐 ×ˢ 𝓑) →
      ((γ : N × G).1⁻¹ * p.1 ∈ 𝓐 ∧ (γ : N × G).2⁻¹ * p.2 ∈ 𝓑) := by
    rintro γ p ⟨q, hq, rfl⟩
    simpa [Subgroup.smul_def] using hq
  refine
    { nullMeasurableSet := hA.nullMeasurableSet.prod hB.nullMeasurableSet
      ae_covers := ?_
      aedisjoint := ?_ }
  · have h2 : ∀ᵐ g ∂μ, ∃ h : Γ.map (MonoidHom.snd N G), h • g ∈ 𝓑 := hB.ae_covers
    have h1 : ∀ᵐ n ∂ν, ∀ h : Γ.map (MonoidHom.snd N G),
        ∃ k : Γ.comap (MonoidHom.inl N G), k • (mm h * n) ∈ 𝓐 := by
      rw [ae_all_iff]
      intro h
      exact (measurePreserving_mul_left ν (mm h)).quasiMeasurePreserving.ae hA.ae_covers
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1,
      Measure.quasiMeasurePreserving_snd.ae h2] with p hn hg
    obtain ⟨h, hh⟩ := hg
    obtain ⟨k, hk⟩ := hn h
    have hk' : (((k : N), (1 : G)) : N × G) ∈ Γ := k.2
    refine ⟨⟨((k : N), (1 : G)) * (mm h, (h : G)), Γ.mul_mem hk' (hmm h)⟩, ?_⟩
    refine ⟨?_, ?_⟩
    · simpa [Subgroup.smul_def, mul_assoc] using hk
    · simpa [Subgroup.smul_def] using hh
  · intro γ γ' hne
    change (ν.prod μ) ((γ • (𝓐 ×ˢ 𝓑)) ∩ (γ' • (𝓐 ×ˢ 𝓑))) = 0
    by_cases hh : (γ : N × G).2 = (γ' : N × G).2
    ·
      have hkmem : MonoidHom.inl N G ((γ' : N × G).1⁻¹ * (γ : N × G).1) ∈ Γ := by
        have e : MonoidHom.inl N G ((γ' : N × G).1⁻¹ * (γ : N × G).1) = ((γ'⁻¹ * γ : Γ) : N × G) := by
          ext <;> simp [hh]
        rw [e]; exact (γ'⁻¹ * γ).2
      let k : Γ.comap (MonoidHom.inl N G) := ⟨(γ' : N × G).1⁻¹ * (γ : N × G).1, hkmem⟩
      have hk1 : (1 : Γ.comap (MonoidHom.inl N G)) ≠ k⁻¹ := by
        intro h1
        apply hne
        have h1' : (γ' : N × G).1⁻¹ * (γ : N × G).1 = 1 := by
          have := congrArg (fun x : Γ.comap (MonoidHom.inl N G) => ((x⁻¹ : Γ.comap (MonoidHom.inl N G)) : N)) h1
          simpa [k] using this.symm
        apply Subtype.ext
        exact Prod.ext (inv_mul_eq_one.mp h1').symm hh
      have hnull : ν (𝓐 ∩ k⁻¹ • 𝓐) = 0 := by
        have := hA.aedisjoint hk1
        simpa [Function.onFun, AEDisjoint] using this
      refine measure_mono_null (t := Prod.fst ⁻¹' ((fun x => (γ : N × G).1⁻¹ * x) ⁻¹' (𝓐 ∩ k⁻¹ • 𝓐))) ?_
        (Measure.quasiMeasurePreserving_fst.preimage_null
          ((measurePreserving_mul_left ν (γ : N × G).1⁻¹).quasiMeasurePreserving.preimage_null hnull))
      rintro p ⟨hp, hp'⟩
      obtain ⟨a1, -⟩ := memS γ p hp
      obtain ⟨a2, -⟩ := memS γ' p hp'
      refine ⟨a1, ?_⟩
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Subgroup.smul_def, smul_eq_mul]
      show ((γ' : N × G).1⁻¹ * (γ : N × G).1) * ((γ : N × G).1⁻¹ * p.1) ∈ 𝓐
      simpa [mul_assoc] using a2
    ·
      let h : Γ.map (MonoidHom.snd N G) := ⟨(γ : N × G).2, Subgroup.mem_map_of_mem _ γ.2⟩
      let h' : Γ.map (MonoidHom.snd N G) := ⟨(γ' : N × G).2, Subgroup.mem_map_of_mem _ γ'.2⟩
      have hne' : h ≠ h' := fun e => hh (congrArg Subtype.val e)
      have hnull : μ ((h • 𝓑) ∩ (h' • 𝓑)) = 0 := hB.aedisjoint hne'
      refine measure_mono_null (t := Prod.snd ⁻¹' ((h • 𝓑) ∩ (h' • 𝓑))) ?_
        (Measure.quasiMeasurePreserving_snd.preimage_null hnull)
      rintro p ⟨hp, hp'⟩
      refine ⟨?_, ?_⟩
      · rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
        simpa [h] using (memS γ p hp).2
      · rw [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
        simpa [h'] using (memS γ' p hp').2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
section
set_option synthInstance.maxHeartbeats 400000
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatLatV

variable {D : D7}

def cut (P : Pl D → Prop) (u : Af D.host.F ⊗[D.host.F] D.host.E) : AE D :=
  Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift ((GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * u)

def cutHom (P : Pl D → Prop) : (Af D.host.F ⊗[D.host.F] D.host.E) →+ AE D where
  toFun := cut P
  map_zero' := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = 0
    rw [mul_zero]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_zero
  map_add' a b := by
    show Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ = Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _ + Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift _
    rw [mul_add]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.lift_add _ _

theorem cut_tmul (P : Pl D → Prop) (a : Af D.host.F) (x : D.host.E) :
    cut P (a ⊗ₜ[D.host.F] x) = pairA D.host.F 0 (GlobalTheory.SelfDualAt.indP P * a) ⊗ₜ[D.host.F] x := by
  unfold cut
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl


set_option maxHeartbeats 800000 in
theorem cut_finPart (P : Pl D → Prop) (u : AE D) (hu : u ∈ idAt D P) : cut P (finPart D u) = u := by
  unfold idAt at hu
  rw [Ideal.mem_inf] at hu
  obtain ⟨hinf, hfin⟩ := hu
  rw [RingHom.mem_ker] at hinf
  have hoff : ∀ w : Pl D, ¬ P w → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D u) = 0 := by
    intro w hw
    have := (Submodule.mem_iInf _).1 hfin ⟨w, hw⟩
    exact (RingHom.mem_ker).1 this
  have hcut : (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D u = finPart D u := by
    refine (sub_eq_zero.mp (GlobalTheory.SelfDualAt.eq_zero_of_compFin _ fun w => ?_)).symm
    rw [map_sub, map_mul]
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (GlobalTheory.SelfDualAt.indP P ⊗ₜ[D.host.F] (1 : D.host.E)) =
        evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
    rw [hc, GlobalTheory.SelfDualAt.evalV_indP]
    by_cases hw : P w
    · rw [if_pos hw, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [if_neg hw, TensorProduct.zero_tmul, zero_mul, sub_zero, hoff w hw]
  unfold cut
  rw [hcut]
  exact (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.eq_lift_of_infPart u hinf).symm

theorem mem_latV_of_hatL : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D),
    (∀ i, y i ∈ idAt D P) →
    (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  intro D S L P y hy hz
  have hlat : (fun i => finPart D (y i)) ∈ latHat D.host.F D.host.E (L : Set (Fin S.rank → D.host.E)) :=
    (GlobalTheory.LevSplit.latHat_iff L _).2 hz
  have key : y = AddMonoidHom.compLeft (cutHom P) (Fin S.rank) (fun i => finPart D (y i)) :=
    funext fun i => (cut_finPart P (y i) (hy i)).symm
  rw [key]
  refine AddSubgroup.closure_induction
    (p := fun u _ => AddMonoidHom.compLeft (cutHom P) (Fin S.rank) u ∈ latV S L P) ?_ ?_ ?_ ?_ hlat
  · rintro _ ⟨a, ha, x, hx, rfl⟩
    apply AddSubgroup.subset_closure
    refine ⟨GlobalTheory.SelfDualAt.indP P * a, ?_, ?_, 1, rfl, x, hx, ?_⟩
    · intro v
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP]
      split_ifs
      · rw [one_mul]; exact ha v
      · rw [zero_mul]; exact zero_mem _
    · intro v hv
      rw [map_mul, GlobalTheory.SelfDualAt.evalV_indP, if_neg hv, zero_mul]
    · funext i
      show cut P (a ⊗ₜ[D.host.F] x i) = _
      rw [cut_tmul, one_mul]
  · rw [map_zero]; exact zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact add_mem ha hb
  · intro a _ ha
    rw [map_neg]; exact neg_mem ha

end GlobalTheory.HatLatV

end
end

