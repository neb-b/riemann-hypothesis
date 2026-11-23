module

public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionOfLogGrowth
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0003
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPolynomialEqZeroOfEventually

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.ContAtOfHoloOn
section
noncomputable section

namespace RootFieldNumerics

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace Desc

variable {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem contAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) :
    ContinuousAt f x := by
  obtain ⟨k, hk⟩ := A.cover x
  have h1 := (hf k (A.chart k x) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k x) ∈ U
    rwa [(A.chart k).left_inv hk]⟩).continuousAt
  have h2 := h1.comp ((A.chart k).continuousAt hk)
  refine h2.congr ?_
  filter_upwards [(A.chart k).open_source.mem_nhds hk] with x' hx'
  simp [(A.chart k).left_inv hx']

theorem analytic_off {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} {S U : Set X} {f : Y → ℂ}
    (hh : HoloMap B A h) (hd : IsDegreeOff A B h 1 S) (hf : B.HoloOn (h ⁻¹' U) f) (σ : X → Y)
    (hσ : ∀ x ∉ S, h (σ x) = x) (hσ' : ∀ y, h y ∉ S → σ (h y) = y) (k : Fin A.n) {q : Fin e → ℂ}
    (hq : q ∈ (A.chart k).target) (hU : (A.chart k).symm q ∈ U) (hS : (A.chart k).symm q ∉ S) :
    AnalyticAt ℂ (fun t => f (σ ((A.chart k).symm t))) q := by
  have hSc : IsClosed S := isClosed_of_isAnalyticSubset' A hd.1
  set x := (A.chart k).symm q with hx
  obtain ⟨j, hj⟩ := B.cover (σ x)
  set p := B.chart j (σ x) with hp
  have hpt : p ∈ (B.chart j).target := (B.chart j).map_source hj
  have hsp : (B.chart j).symm p = σ x := (B.chart j).left_inv hj
  have hxs : x ∈ (A.chart k).source := (A.chart k).map_target hq
  have hhs : h ((B.chart j).symm p) ∈ (A.chart k).source := by rw [hsp, hσ x hS]; exact hxs
  let φ : (Fin e → ℂ) → Fin e → ℂ := A.chart k ∘ h ∘ (B.chart j).symm
  have hφ : AnalyticAt ℂ φ p := hh.2 j k p ⟨hpt, hhs⟩
  have hφp : φ p = q := by
    show A.chart k (h ((B.chart j).symm p)) = q
    rw [hsp, hσ x hS, hx, (A.chart k).right_inv hq]
  have hdet := hd.2.2.2.2.2 j k p hpt (by
    show h ((B.chart j).symm p) ∉ S
    rwa [hsp, hσ x hS]) hhs
  let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) := (fderiv ℂ φ p).toContinuousLinearEquivOfDetNeZero hdet
  have hL : HasFDerivAt φ (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) p := by
    have := hφ.differentiableAt.hasFDerivAt
    simpa [L] using this
  have hc : ContDiffAt ℂ ⊤ φ p := hφ.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  let ψ := hc.localInverse hL hn
  have hψ : AnalyticAt ℂ ψ q := by
    have := (hc.to_localInverse hL hn).analyticAt
    rwa [hφp] at this
  have hψq : ψ q = p := by
    rw [← hφp]
    exact hc.localInverse_apply_image hL hn
  have hri : ∀ᶠ t in 𝓝 q, φ (ψ t) = t := by
    have := (hc.hasStrictFDerivAt' hL hn).eventually_right_inverse
    rw [hφp] at this
    exact this
  have hfa : AnalyticAt ℂ (f ∘ (B.chart j).symm) (ψ q) := by
    rw [hψq]
    refine hf j p ⟨hpt, ?_⟩
    show h ((B.chart j).symm p) ∈ U
    rwa [hsp, hσ x hS]
  refine (hfa.comp hψ).congr ?_
  have c1 : ContinuousAt (fun t => h ((B.chart j).symm (ψ t))) q :=
    hh.1.continuousAt.comp (ContinuousAt.comp (by rw [hψq]; exact (B.chart j).continuousAt_symm hpt) hψ.continuousAt)
  have e1 : ∀ᶠ t in 𝓝 q, h ((B.chart j).symm (ψ t)) ∈ (A.chart k).source ∩ Sᶜ :=
    c1.eventually_mem (((A.chart k).open_source.inter hSc.isOpen_compl).mem_nhds (by
      show h ((B.chart j).symm (ψ q)) ∈ _
      rw [hψq, hsp, hσ x hS]
      exact ⟨hxs, hS⟩))
  filter_upwards [hri, e1] with t h1 h2
  have h3 : (A.chart k).symm t = h ((B.chart j).symm (ψ t)) := by
    rw [← (A.chart k).left_inv h2.1]
    exact congrArg _ h1.symm
  show f ((B.chart j).symm (ψ t)) = f (σ ((A.chart k).symm t))
  rw [h3, hσ' _ h2.2]

theorem local_ext {A : FinHolAtlas e X} {S U : Set X} {u : X → ℂ} (hS : A.IsAnalyticSubset S) (hi : interior S = ∅)
    (hU : IsOpen U) (k : Fin A.n)
    (ha : ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → (A.chart k).symm q ∉ S →
      AnalyticAt ℂ (fun t => u ((A.chart k).symm t)) q)
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ x' in 𝓝 x, x' ∉ S → ‖u x'‖ ≤ C) {q : Fin e → ℂ} (hq : q ∈ (A.chart k).target)
    (hqU : (A.chart k).symm q ∈ U) :
    ∃ w : (Fin e → ℂ) → ℂ, AnalyticAt ℂ w q ∧ ∀ᶠ t in 𝓝 q, (A.chart k).symm t ∉ S → w t = u ((A.chart k).symm t) := by
  by_cases hqS : (A.chart k).symm q ∈ S
  swap
  · exact ⟨_, ha q hq hqU hqS, Eventually.of_forall fun _ _ => rfl⟩
  obtain ⟨W, hW, hqW, hWc, φ, hφ, ⟨w₀, hw₀, hw₀'⟩, hz⟩ := analyticSubset_chart_local A hS hi k (z := q)
    ⟨_, ⟨hqS, (A.chart k).map_target hq⟩, (A.chart k).right_inv hq⟩
  let U' := W ∩ ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U)
  have hU' : IsOpen U' := hW.inter ((A.chart k).isOpen_inter_preimage_symm hU)
  have hns : ∀ b ∈ U', φ b ≠ 0 → (A.chart k).symm b ∉ S := fun b hb h0 hs =>
    h0 (hz b ⟨⟨_, ⟨hs, (A.chart k).map_target hb.2.1⟩, (A.chart k).right_inv hb.2.1⟩, hb.1⟩)
  have hden : U' ⊆ closure {b ∈ U' | φ b ≠ 0} := fun b hb => by
    by_contra hn
    have h1 : ∀ᶠ b' in 𝓝 b, b' ∉ {b ∈ U' | φ b ≠ 0} := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hn] with b' hb' h using hb' (subset_closure h)
    have h2 : φ =ᶠ[𝓝 b] 0 := by
      filter_upwards [h1, hU'.mem_nhds hb] with b' h h'
      by_contra h0
      exact h ⟨h', h0⟩
    exact hw₀' (hφ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWc hb.1 h2 hw₀)
  obtain ⟨u', hu', he⟩ := GlobalTheory.LogExt.riemann_extension_log _ U' φ (fun t => u ((A.chart k).symm t)) hU'
    (hφ.differentiableOn.mono Set.inter_subset_left)
    (fun b hb => (ha b hb.1.2.1 hb.1.2.2 (hns b hb.1 hb.2)).differentiableAt.differentiableWithinAt) hden
    (fun b hb' => by
      obtain ⟨C, hC⟩ := hb _ hb'.2.2
      refine ⟨C, 0, ?_⟩
      filter_upwards [((A.chart k).continuousAt_symm hb'.2.1).eventually hC, hU'.mem_nhds hb'] with t h1 h2 h0
      simpa using h1 (hns t h2 h0))
  have hq' : q ∈ U' := ⟨hqW, hq, hqU⟩
  refine ⟨u', GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hU' hu' q hq', ?_⟩
  filter_upwards [hU'.mem_nhds hq'] with t ht hts
  have : (𝓝[{b ∈ U' | φ b ≠ 0}] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hden ht)
  refine tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[{b ∈ U' | φ b ≠ 0}] t)
    ((hu'.continuousOn.continuousAt (hU'.mem_nhds ht)).tendsto.mono_left nhdsWithin_le_nhds)
    ((ha t ht.2.1 ht.2.2 hts).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with b hb using he hb

theorem ext_manifold {A : FinHolAtlas e X} {S U : Set X} {u : X → ℂ} (hS : A.IsAnalyticSubset S) (hi : interior S = ∅)
    (hU : IsOpen U)
    (ha : ∀ k, ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → (A.chart k).symm q ∉ S →
      AnalyticAt ℂ (fun t => u ((A.chart k).symm t)) q)
    (hb : ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ x' in 𝓝 x, x' ∉ S → ‖u x'‖ ≤ C) :
    ∃ F : X → ℂ, A.HoloOn U F ∧ ∀ x ∈ U, x ∉ S → F x = u x := by
  have hden : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hi
  let F : X → ℂ := fun x => limUnder (𝓝[Sᶜ] x) u
  have key : ∀ k, ∀ q ∈ (A.chart k).target, (A.chart k).symm q ∈ U → ∃ w : (Fin e → ℂ) → ℂ, AnalyticAt ℂ w q ∧
      (∀ᶠ t in 𝓝 q, (A.chart k).symm t ∉ S → w t = u ((A.chart k).symm t)) ∧
      ∀ᶠ t in 𝓝 q, w t = F ((A.chart k).symm t) := fun k q hq hqU => by
    obtain ⟨w, hw, he⟩ := local_ext hS hi hU k (ha k) hb hq hqU
    refine ⟨w, hw, he, ?_⟩
    filter_upwards [he.eventually_nhds, hw.eventually_analyticAt, (A.chart k).open_target.mem_nhds hq] with t h1 h2 h3
    have hs := (A.chart k).map_target h3
    have hr := (A.chart k).right_inv h3
    have : (𝓝[Sᶜ] ((A.chart k).symm t)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hden _)
    have hc : Tendsto (A.chart k) (𝓝 ((A.chart k).symm t)) (𝓝 t) := by
      have := ((A.chart k).continuousAt hs).tendsto
      rwa [hr] at this
    refine (Tendsto.limUnder_eq ?_).symm
    refine ((h2.continuousAt.tendsto.comp hc).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [nhdsWithin_le_nhds (hc.eventually h1), nhdsWithin_le_nhds ((A.chart k).open_source.mem_nhds hs),
      self_mem_nhdsWithin] with x h4 h5 h6
    have h7 : (A.chart k).symm (A.chart k x) ∉ S → w (A.chart k x) = u ((A.chart k).symm (A.chart k x)) := h4
    rw [(A.chart k).left_inv h5] at h7
    exact h7 h6
  refine ⟨F, fun k q hq => ?_, fun x hx hxS => ?_⟩
  · obtain ⟨w, hw, -, he⟩ := key k q hq.1 hq.2
    exact hw.congr he
  · obtain ⟨k, hk⟩ := A.cover x
    have hl := (A.chart k).left_inv hk
    obtain ⟨w, -, h1, h2⟩ := key k _ ((A.chart k).map_source hk) (by rwa [hl])
    have h3 := h1.self_of_nhds
    have h4 := h2.self_of_nhds
    rw [hl] at h3 h4
    rw [← h4, h3 hxS]

end Desc

open Desc in
theorem descend : Descend := by
  intro e X Y _ _ _ _ _ _ A B h S U f hh hd hU hf
  classical
  rcases isEmpty_or_nonempty Y with hY | hY
  · refine ⟨0, fun k => ?_, fun y => isEmptyElim y⟩
    exact analyticOnNhd_const
  have hex : ∀ x, ∃ y, x ∉ S → h ⁻¹' {x} = {y} := fun x => by
    by_cases hx : x ∈ S
    · exact ⟨hY.some, fun h' => (h' hx).elim⟩
    · obtain ⟨y, hy⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 x hx)
      exact ⟨y, fun _ => hy⟩
  choose σ hσ₀ using hex
  have hσ : ∀ x ∉ S, h (σ x) = x := fun x hx => by
    have : σ x ∈ h ⁻¹' {x} := by rw [hσ₀ x hx]; rfl
    exact this
  have hσ' : ∀ y, h y ∉ S → σ (h y) = y := fun y hy => by
    have : y ∈ h ⁻¹' {h y} := rfl
    rw [hσ₀ _ hy] at this
    exact this.symm
  have hfc : ContinuousOn f (h ⁻¹' U) := fun y hy => (contAt_of_holoOn B hf hy).continuousWithinAt
  obtain ⟨F, hF, he⟩ := ext_manifold (u := fun x => f (σ x)) hd.1 hd.2.1 hU
    (fun k q hq h1 h2 => analytic_off hh hd hf σ hσ hσ' k hq h1 h2) (fun x hx => by
      obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds (hU.mem_nhds hx)
      have hc : IsCompact (h ⁻¹' K) := (hKc.isClosed.preimage hh.1).isCompact
      obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (hfc.mono (Set.preimage_mono hKU))
      refine ⟨C, ?_⟩
      filter_upwards [hK] with x' h1 h2
      exact hC _ (by show h (σ x') ∈ K; rwa [hσ x' h2]))
  refine ⟨F, hF, fun y hy => ?_⟩
  have hden : Dense (h ⁻¹' S)ᶜ := interior_eq_empty_iff_dense_compl.1 hd.2.2.2.1
  have ho : IsOpen (h ⁻¹' U) := hU.preimage hh.1
  refine Set.EqOn.of_subset_closure (f := fun y => F (h y)) (g := f) (s := h ⁻¹' U ∩ (h ⁻¹' S)ᶜ) (t := h ⁻¹' U)
    (fun y' hy' => ?_) (fun y' hy' => ?_) hfc Set.inter_subset_left (hden.open_subset_closure_inter ho) hy
  · show F (h y') = f y'
    rw [he _ hy'.1 hy'.2, hσ' _ hy'.2]
  · exact ((contAt_of_holoOn A hF hy').comp hh.1.continuousAt).continuousWithinAt

end RootFieldNumerics
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.CoordsOrbit
section
noncomputable section

namespace RootFieldNumerics

open AlgebraicGeometry CategoryTheory NumberField Filter Topology Matrix
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.PB

namespace Pot

theorem log_norm_an {n : ℕ} {t₀ : Fin n → ℂ} {F : (Fin n → ℂ) → ℂ} (hF : AnalyticAt ℂ F t₀)
    (h0 : F t₀ ≠ 0) : ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, Real.log ‖F t‖ = (G t).re := by
  have hH : AnalyticAt ℂ (fun t => F t / F t₀) t₀ := hF.div analyticAt_const h0
  have e1 : F t₀ / F t₀ ∈ Complex.slitPlane := by rw [div_self h0]; exact Complex.one_mem_slitPlane
  refine ⟨fun t => Complex.log (F t / F t₀) + (Real.log ‖F t₀‖ : ℂ), (hH.clog e1).add analyticAt_const, ?_⟩
  filter_upwards [hF.continuousAt.eventually_ne h0] with t ht
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 ht) (norm_ne_zero_iff.2 h0)]
  ring

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem val_an {n : ℕ} {B : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo B z)
    (hall : ∀ q : X, genPt ξ ⤳ q) {t₀ : Fin n → ℂ} (ht : t₀ ∈ B) {a : Ω} {r : ℂ} (h : ValAt ξ (z t₀) a r) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u t₀ ∧ ∀ᶠ t in 𝓝 t₀, ValAt ξ (z t) a (u t) := by
  obtain ⟨h0, s, rfl, -⟩ := h
  obtain ⟨U, hU, f, rfl⟩ := X.presheaf.exists_germ_eq s
  have hg : centre ξ ∈ U := h0.mem_open U.isOpen hU
  have hn : {b ∈ B | ⊤ ≤ z b ⁻¹ᵁ U} ∈ 𝓝 t₀ := (hz U f).1.mem_nhds ⟨ht, (SheetDecomposition.CovSch.top_le_iff _ _).2 hU⟩
  refine ⟨fun b => valAt' (z b) U f, GlobalTheory.SCV.analyticAt_of_differentiableOn (hz U f).2 hn, ?_⟩
  filter_upwards [hn] with t h1
  have h2 := (SheetDecomposition.CovSch.top_le_iff _ _).1 h1.2
  rw [SheetDecomposition.CovSch.valAt'_eq _ _ h2, SheetDecomposition.CovSch.genMap_germ' ⟨centre (z t₀), h0⟩ U hU hg f]
  exact SheetDecomposition.CovSch.valAt_sec (hall _) U h2 hg f

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem coords_orbit {z : Sp ℂ ⟶ X} {w w' : (Σ k, J k) → ℂ} (h : CoordsAt ξ y z w') (hs : SameOrbit w w') :
    CoordsAt ξ y z w := by
  obtain ⟨a, ha, rfl⟩ := hs
  refine ⟨fun k => (h.1 k).imp fun i hi => (IsUnit.mk0 _ (ha k)).mul hi, fun k i hi => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 k i (isUnit_of_mul_isUnit_right hi)
  refine ⟨h1, fun j => (h2 j).imp fun r hr => ⟨hr.1, ?_⟩⟩
  show a k * w' ⟨k, j⟩ = r * (a k * w' ⟨k, i⟩)
  rw [hr.2]
  ring

theorem log_h_smul (A : HermLine J) (a : K → ℂ) (ha : ∀ k, a k ≠ 0) {w : (Σ k, J k) → ℂ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => a p.1 * w p) = ∑ k, (A.a k : ℝ) * Real.log ‖a k‖ + Real.log (A.h w) := by
  have h1 : ∀ k, ‖a k‖ ^ A.a k ≠ 0 := fun k => zpow_ne_zero _ (norm_ne_zero_iff.2 (ha k))
  rw [A.smul a w ha, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => h1 k) (A.pos w hw).ne',
    Real.log_prod fun k _ => h1 k]
  simp only [Real.log_zpow]

theorem log_orbit {I : Type} (s : Finset I) (A : HermLine J) (B : I → HermLine J) (hd : A.a = -∑ i ∈ s, (B i).a)
    {w w' : (Σ k, J k) → ℂ} (hs : SameOrbit w w') (hw : ∀ k, ∃ i, w' ⟨k, i⟩ ≠ 0) :
    Real.log (A.h w) + ∑ i ∈ s, Real.log ((B i).h w) = Real.log (A.h w') + ∑ i ∈ s, Real.log ((B i).h w') := by
  obtain ⟨a, ha, rfl⟩ := hs
  simp only [log_h_smul _ a ha hw, hd, Finset.sum_add_distrib, Pi.neg_apply, Finset.sum_apply, Int.cast_neg, Int.cast_sum,
    neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]
  ring

theorem log_h_an {n : ℕ} {B : Set (Fin n → ℂ)} {z : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (hz : IsHolTo B z)
    (hall : ∀ q : X, genPt ξ ⤳ q) {t₀ : Fin n → ℂ} (ht : t₀ ∈ B) (A : HermLine J) (e₀ T : Ω)
    {γ : (Fin n → ℂ) → (Σ k, J k) → ℂ} (hγ : ∀ p, AnalyticAt ℂ (fun t => γ t p) t₀) {ν : (Fin n → ℂ) → ℝ}
    (hν : ∀ᶠ t in 𝓝 t₀, 0 < ν t ∧ SecNorm ξ y A e₀ (z t) (γ t) T (ν t)) :
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t₀ ∧ ∀ᶠ t in 𝓝 t₀, -Real.log (A.h (γ t)) = Real.log (ν t) + (G t).re := by
  obtain ⟨p0, h0⟩ := hν.self_of_nhds
  obtain ⟨c, hc⟩ := h0.exists_chart
  obtain ⟨u₀, hu₀, e0⟩ := h0.2.2 c hc
  obtain ⟨u, hu, hue⟩ := val_an hz hall ht hu₀
  let F : (Fin n → ℂ) → ℂ := fun t => u t * ∏ k, γ t ⟨k, c k⟩ ^ A.a k
  have hF : AnalyticAt ℂ F t₀ := hu.mul (Finset.analyticAt_fun_prod _ fun k _ => (hγ _).zpow (hc k))
  have hcn : ∀ᶠ t in 𝓝 t₀, ∀ k, γ t ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hγ _).continuousAt.eventually_ne (hc k)
  have hev : ∀ᶠ t in 𝓝 t₀, ν t * A.h (γ t) = ‖F t‖ := by
    filter_upwards [hν, hue, hcn] with t h1 h2 h3
    obtain ⟨u', hu', e⟩ := h1.2.2.2 c h3
    rw [e, CxVal.unique hu' h2]
    simp only [F, norm_mul, norm_prod, norm_zpow]
  have hF0 : F t₀ ≠ 0 := by
    rw [← norm_ne_zero_iff, ← hev.self_of_nhds]
    exact (mul_pos p0 (A.pos _ fun k => ⟨c k, hc k⟩)).ne'
  obtain ⟨G, hG, hGe⟩ := log_norm_an hF hF0
  refine ⟨fun t => -G t, hG.neg, ?_⟩
  filter_upwards [hν, hev, hcn, hGe] with t h1 h2 h3 h4
  rw [Complex.neg_re, ← h4, ← h2, Real.log_mul h1.1.ne' (A.pos _ fun k => ⟨c k, h3 k⟩).ne']
  ring

theorem holo_comp {e e' : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N] {A : FinHolAtlas e M}
    {B : FinHolAtlas e' N} {ψ : M → N} (hψ : HoloMap A B ψ) (k : Fin A.n) {t : Fin e → ℂ} (ht : t ∈ (A.chart k).target)
    {W : Set N} {f : N → ℂ} (hf : B.HoloOn W f) (hW : ψ ((A.chart k).symm t) ∈ W) :
    AnalyticAt ℂ (fun t' => f (ψ ((A.chart k).symm t'))) t := by
  obtain ⟨j, hj⟩ := B.cover (ψ ((A.chart k).symm t))
  have h1 := hψ.2 k j t ⟨ht, hj⟩
  have h2 := hf j (B.chart j (ψ ((A.chart k).symm t))) ⟨(B.chart j).map_source hj, by
    show (B.chart j).symm _ ∈ W
    rwa [(B.chart j).left_inv hj]⟩
  have h3 := AnalyticAt.comp (f := B.chart j ∘ ψ ∘ (A.chart k).symm) (x := t) h2 h1
  refine h3.congr ?_
  have hc : ContinuousAt (fun t' => ψ ((A.chart k).symm t')) t :=
    hψ.1.continuousAt.comp ((A.chart k).continuousAt_symm ht)
  filter_upwards [hc.eventually_mem ((B.chart j).open_source.mem_nhds hj)] with t' h
  simp only [Function.comp_apply, (B.chart j).left_inv h]

end Pot

open Pot in
theorem potLoc : PotLoc := by
  intro E _ _ _ H D l Xo c Y S RM Sys Fx Or ψ k V z tr ν hψ hπ hV hVt hpt t₁ ht₁ p
  classical
  obtain ⟨τ, i⟩ := p
  let w : _ → Or.Re.R.X := fun t => ψ ((Sys.A.chart k).symm t)
  let γ : _ → (Σ k, RM.ι k) → ℂ := fun t => Or.Re.R.lift (w t₁) (w t)
  have hwc : ∀ t ∈ V, ContinuousAt w t := fun t ht =>
    hψ.1.continuousAt.comp ((Sys.A.chart k).continuousAt_symm (hVt ht))
  let B := V ∩ w ⁻¹' Or.Re.R.U (w t₁)
  have hB : IsOpen B := (continuousOn_of_forall_continuousAt hwc).isOpen_inter_preimage hV (Or.Re.R.isOpen_U _)
  have ht₁B : t₁ ∈ B := ⟨ht₁, Or.Re.R.mem_U _⟩
  have hγ : ∀ t ∈ B, ∀ q, AnalyticAt ℂ (fun t => γ t q) t := fun t ht q =>
    holo_comp hψ k (hVt ht.1) (Or.Re.R.holo (w t₁) q) ht.2
  have horb : ∀ t ∈ B, SameOrbit (γ t) (Or.Re.R.lift (w t) (w t)) := fun t ht => Or.Re.R.compat _ _ _ ⟨ht.2, Or.Re.R.mem_U _⟩
  have hco : ∀ t ∈ B, CoordsAt Or.𝔐.ξ RM.y (z t) (γ t) := fun t ht => coords_orbit (hpt t ht.1).2.1 (horb t ht)
  have hz : IsHolTo B z := _root_.GlobalTheory.CompanionTheory.Ar.PeriodsHol.isHolTo_of_coordsAt_family _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie Or.𝔐.all _ B γ z hB
    (differentiableOn_pi.2 fun q t ht => (hγ t ht q).differentiableAt.differentiableWithinAt) hco
  have hop : ∀ t ∈ V, Or.Re.π (w t) ∈ Sys.open' := fun t ht => by
    rw [hπ]
    exact (hpt t ht).1
  have hin : ∀ t ∈ V, Or.𝔐.Interior (z t) := fun t ht => (Or.interior (w t) (z t) (hpt t ht).2.1).2 (hop t ht)
  have hroot : ∀ r : RootIx D, ∃ G : _ → ℂ, AnalyticAt ℂ G t₁ ∧ ∀ᶠ t in 𝓝 t₁,
      -Real.log ((Or.sing r).h (γ t)) = Real.log (ν r t ^ HodgeCpt.rootSgn D r) + (G t).re := fun r => by
    refine log_h_an (y := RM.y) hz Or.𝔐.all ht₁B (Or.sing r) (Or.e r) (tr r ^ HodgeCpt.rootSgn D r) (hγ t₁ ht₁B) ?_
    filter_upwards [hB.mem_nhds ht₁B] with t ht
    exact ⟨zpow_pos ((hpt t ht.1).2.2 r).pos _, Or.hodge r (z t) (γ t) (hco t ht) (hin t ht.1) _ _ ((hpt t ht.1).2.2 r)⟩
  choose G hG hGe using hroot
  obtain ⟨W, hW, hwW, G₀, hG₀, e₀⟩ := Or.Re.ref_pot (some (τ, i)) (w t₁) trivial
  have hG₀a : AnalyticAt ℂ (fun t => G₀ (w t)) t₁ := holo_comp hψ k (hVt ht₁) hG₀ hwW
  refine ⟨fun t => ∑ j ∈ Finset.Iic i, G (τ, j) t - G₀ (w t),
    (Finset.analyticAt_fun_sum _ fun j _ => hG _).sub hG₀a, ?_⟩
  filter_upwards [hB.mem_nhds ht₁B, (hwc t₁ ht₁).eventually_mem (hW.mem_nhds hwW),
    (Filter.eventually_all_finset (Finset.Iic i)).2 fun j _ => hGe (τ, j)] with t ht htW h3
  have e1 : Real.log ((Or.Re.ref (some (τ, i))).h (γ t)) -
      (Sys.th (some (τ, i))).φ (Or.Re.π (w t₁)) (Or.Re.π (w t)) = (G₀ (w t)).re := e₀ (w t) htW
  have e2 := Or.fund_sing τ i (w t) (hop t ht.1)
  have e3 := log_orbit (Finset.Iic i) (Or.Re.ref (some (τ, i))) (fun j => Or.sing (τ, j))
    (by rw [Or.fund_deg]; simp only [Or.sing_deg]) (horb t ht) (Or.Re.R.mem _ _ (Or.Re.R.mem_U _)).1
  have e4 : ∑ j ∈ Finset.Iic i, -Real.log ((Or.sing (τ, j)).h (γ t)) =
      ∑ j ∈ Finset.Iic i, ((HodgeCpt.rootSgn D (τ, j) : ℝ) * Real.log (ν (τ, j) t) + (G (τ, j) t).re) :=
    Finset.sum_congr rfl fun j hj => by rw [h3 j hj, Real.log_zpow]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at e4
  simp only [w, hπ] at e1 e2
  show (Sys.th (some (τ, i))).φ _ _ + Sys.ph (some (τ, i)) _ = _
  rw [Complex.sub_re, Complex.re_sum]
  simp only [w] at e3 ⊢
  linarith

end RootFieldNumerics
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.ExistsInverse
section
noncomputable section

namespace RootFieldNumerics.Bh

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo

theorem contAt_of_holoOn {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {U : Set X} {f : X → ℂ}
    (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 := (hf j (A.chart j x) ⟨(A.chart j).map_source hj, by
    show (A.chart j).symm (A.chart j x) ∈ U
    rwa [(A.chart j).left_inv hj]⟩).continuousAt
  have h2 := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem surj_of_degree {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [CompactSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {h : Y → X} {S : Set X} (hc : Continuous h) (hd : IsDegreeOff A B h 1 S) :
    Function.Surjective h := by
  have h1 : IsClosed (Set.range h) := (isCompact_range hc).isClosed
  have h2 : Dense Sᶜ := interior_eq_empty_iff_dense_compl.1 hd.2.1
  have h3 : Sᶜ ⊆ Set.range h := fun x hx => by
    obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero (s := h ⁻¹' {x}) (by rw [hd.2.2.2.2.1 x hx]; exact one_ne_zero)
    exact ⟨y, hy⟩
  rw [← Set.range_eq_univ, ← h1.closure_eq]
  exact (h2.mono h3).closure_eq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SO_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), funext fun p => by rw [inv_mul_cancel_left₀ (hc _)]⟩

theorem SO_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') : SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), funext fun p => (mul_assoc _ _ _).symm⟩

theorem SO_ne {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (q : Σ k, ι k) : z q ≠ 0 ↔ z' q ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  simp [hc q.1]

theorem isOpen_lift_ne {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (q : Σ k, ι k) :
    IsOpen {w : R.X | R.lift w w q ≠ 0} := by
  refine isOpen_iff_mem_nhds.2 fun w hw => ?_
  filter_upwards [(R.isOpen_U w).mem_nhds (R.mem_U w),
    (contAt_of_holoOn (R.holo w q) (R.mem_U w)).eventually_ne hw] with w' h1 h2
  exact (SO_ne (R.compat w' w w' ⟨R.mem_U w', h1⟩) q).2 h2

theorem exists_inverse {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (hJ : J = ⊤) {X : Type} [TopologicalSpace X]
    (A : FinHolAtlas e X) (π : R.X → X) (hs : Function.Surjective π)
    (key : ∀ w₁, ∃ (O : Set X) (μ : X → (Σ k, ι k) → ℂ), IsOpen O ∧ π w₁ ∈ O ∧ (∀ q, A.HoloOn O fun x => μ x q) ∧
      ∀ w, π w ∈ O → SameOrbit (R.lift w w) (μ (π w))) :
    ∃ ψ : X → R.X, HoloMap A R.A ψ ∧ (∀ x, π (ψ x) = x) ∧ ∀ w, ψ (π w) = w := by
  have hinj : Function.Injective π := fun w w₁ e₀ => by
    obtain ⟨O, μ, -, h1, -, h2⟩ := key w₁
    have a1 := h2 w (e₀ ▸ h1)
    rw [e₀] at a1
    refine R.inj w w₁ (fun h => ?_) (SO_trans a1 (SO_symm (h2 w₁ h1)))
    simpa using h.2 1 (hJ ▸ Submodule.mem_top)
  let ψ := Function.surjInv hs
  have r : ∀ x, π (ψ x) = x := Function.surjInv_eq hs
  have loc : ∀ j, ∀ t ∈ (A.chart j).target, ∃ V, IsOpen V ∧ t ∈ V ∧ ContinuousOn (ψ ∘ (A.chart j).symm) V ∧
      ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ (ψ ∘ (A.chart j).symm)) (V ∩ (ψ ∘ (A.chart j).symm) ⁻¹' (R.A.chart k).source) := by
    intro j t ht
    obtain ⟨O, μ, hO, h1, h2, h3⟩ := key (ψ ((A.chart j).symm t))
    rw [r] at h1
    have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' O) := (A.chart j).isOpen_inter_preimage_symm hO
    refine ⟨_, hV, ⟨ht, h1⟩, _root_.GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift K ι P J e e R hJ _ (fun u => μ ((A.chart j).symm u)) _ hV (fun q => h2 q j)
      fun u hu => ?_⟩
    have := h3 (ψ ((A.chart j).symm u)) (by rw [r]; exact hu.2)
    rwa [r] at this
  refine ⟨ψ, ⟨continuous_iff_continuousAt.2 fun x => ?_, fun j k t ht => ?_⟩, r, fun w => hinj (r _)⟩
  · obtain ⟨j, hj⟩ := A.cover x
    obtain ⟨V, hV, h1, h2, -⟩ := loc j _ ((A.chart j).map_source hj)
    refine ((h2.continuousAt (hV.mem_nhds h1)).comp ((A.chart j).continuousAt hj)).congr ?_
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  · obtain ⟨V, -, h1, -, h2⟩ := loc j t ht.1
    exact h2 k t ⟨h1, ht.2⟩

end RootFieldNumerics.Bh
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.RankLem
section
namespace RootFieldNumerics

theorem rankLem : RankLem := fun _ _ _ _ hV hne hΦ hc =>
  GlobalTheory.CountableFibres.exists_injective_fderiv hV hne (fun z hz => (hΦ z hz).contDiffAt) hc

end RootFieldNumerics
end

