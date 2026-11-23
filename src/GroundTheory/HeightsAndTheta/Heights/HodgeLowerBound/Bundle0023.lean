module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0021
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRefAlongSheet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem analyticAt_holoOn_comp_chartSymm {e m : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : ReciprocityTheory.AnForm.M.IsCompatChart A ψ) {V : Set X}
    {F : X → ℂ} (hF : A.HoloOn V F) {g : (Fin m → ℂ) → Fin e → ℂ} {y : Fin m → ℂ} (hg : AnalyticAt ℂ g y)
    (hgy : g y ∈ ψ.target) (hV : ψ.symm (g y) ∈ V) :
    AnalyticAt ℂ (fun y' => F (ψ.symm (g y'))) y := by
  obtain ⟨i, hi⟩ := A.cover (ψ.symm (g y))
  have hτ : AnalyticAt ℂ (A.chart i ∘ ψ.symm) (g y) := (hψ i).2 (g y) ⟨hgy, hi⟩
  have hFi : AnalyticAt ℂ (F ∘ (A.chart i).symm) ((A.chart i ∘ ψ.symm) (g y)) := by
    refine hF i _ ⟨(A.chart i).map_source hi, ?_⟩
    show (A.chart i).symm (A.chart i (ψ.symm (g y))) ∈ V
    rw [(A.chart i).left_inv hi]
    exact hV
  refine ((hFi.comp hτ).comp hg).congr ?_
  have hc : ContinuousAt (fun y' => ψ.symm (g y')) y := (ψ.continuousAt_symm hgy).comp hg.continuousAt
  filter_upwards [hc.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)] with y' hy'
  simp only [Function.comp_apply, (A.chart i).left_inv hy']

theorem RefAlongSheet.proof : RefAlongSheet.Statement := by
  intro K _ ι _ P n M Xo A S γ y j hγ hsrc hev
  classical
  obtain ⟨g, hg'⟩ : ∃ g : (Fin n → ℂ) → Fin n → ℂ, g = fun y'' => S.R.chart j (M.proj (γ y'')) := ⟨_, rfl⟩
  have hg : AnalyticAt ℂ g y := by
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hev.mono fun _ h => h.2)
    refine AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => g w i) hVo (fun z hz => ?_) y hyV
    rw [hg']
    exact (differentiableAt_pi.mp (hV z hz) i).differentiableWithinAt
  have hγc : ∀ p, AnalyticAt ℂ (fun w => γ w p) y := by
    intro p
    obtain ⟨V, hV, hVo, hyV⟩ := eventually_nhds_iff.1 (hγ.mono fun _ h => h.1)
    exact ReciprocityTheory.AnForm.Osgood.osgood n V (fun w => γ w p) hVo
      (fun z hz => (differentiableAt_pi.mp (hV z hz) p).differentiableWithinAt) y hyV
  have hgy : g y ∈ (S.R.chart j).target := by rw [hg']; exact (S.R.chart j).map_source hsrc
  have hxy : (S.R.chart j).symm (g y) = M.proj (γ y) := by rw [hg']; exact (S.R.chart j).left_inv hsrc
  obtain ⟨U, hUo, hx0U, hUth, s, hs, hsh, G1, hG1, hG1eq⟩ :=
    S.th_ref (M.proj (γ y)) (M.proj (γ y)) (S.R.th.mem_U _)
  obtain ⟨W, hWo, hx0W, G2, hG2, hG2eq⟩ := S.R.q_th j (M.proj (γ y)) (M.proj (γ y)) ⟨S.R.th.mem_U _, hsrc⟩
  obtain ⟨x', hx'⟩ : ∃ x' : (Fin n → ℂ) → M.Xc, x' = fun y' => (S.R.chart j).symm (g y') := ⟨_, rfl⟩
  have hsxy : x' y = M.proj (γ y) := by rw [hx']; exact hxy
  have hx'c : ContinuousAt x' y := by
    rw [hx']; exact ((S.R.chart j).continuousAt_symm hgy).comp hg.continuousAt
  have hsc : ∀ p, AnalyticAt ℂ (fun y' => s (x' y') p) y := fun p => by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) (hsh p) hg hgy (by rw [hxy]; exact hx0U)
  have hG1x : AnalyticAt ℂ (fun y' => G1 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG1 hg hgy (by rw [hxy]; exact hx0U)
  have hG2x : AnalyticAt ℂ (fun y' => G2 (x' y')) y := by
    rw [hx']
    exact analyticAt_holoOn_comp_chartSymm (S.R.compat j) hG2 hg hgy (by rw [hxy]; exact hx0W)
  have hs0 : s (M.proj (γ y)) ∈ mcPts P := (hs _ hx0U).1
  choose i hi using hs0.1
  obtain ⟨cf, hcf⟩ : ∃ cf : K → (Fin n → ℂ) → ℂ,
      cf = fun k y' => γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ := ⟨_, rfl⟩
  have hsi : ∀ k, s (x' y) ⟨k, i k⟩ ≠ 0 := fun k => by rw [hsxy]; exact hi k
  have hcfa : ∀ k, AnalyticAt ℂ (cf k) y := fun k => by
    rw [hcf]; exact (hγc _).div (hsc _) (hsi k)
  have hne : ∀ᶠ y' in 𝓝 y, ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (hsc _).continuousAt.eventually_ne (hsi k)
  have hUWn : U ∩ W ∈ 𝓝 (x' y) := (hUo.inter hWo).mem_nhds (by rw [hsxy]; exact ⟨hx0U, hx0W⟩)
  have hgood : ∀ᶠ y' in 𝓝 y, (x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0 := by
    filter_upwards [hx'c.preimage_mem_nhds hUWn, hev, hγ, hne] with y' h1 h2 h3 h4
    exact ⟨⟨h1, h2.1, h3.2⟩, h4⟩
  have key : ∀ y', ((x' y' ∈ U ∩ W ∧ M.proj (γ y') ∈ (S.R.chart j).source ∧ γ y' ∈ mcPts P) ∧
      ∀ k, s (x' y') ⟨k, i k⟩ ≠ 0) →
      (∀ k, cf k y' ≠ 0) ∧ Real.log (S.ref.h (γ y')) = ∑ k, (S.ref.a k : ℝ) * Real.log ‖cf k y'‖ +
        (S.R.q j (S.R.chart j (M.proj (γ y'))) - (G2 (x' y')).re - (G1 (x' y')).re) := by
    rintro y' ⟨⟨⟨hU', hW'⟩, hsrc', hγ'⟩, hne'⟩
    have hxp : x' y' = M.proj (γ y') := by rw [hx', hg']; exact (S.R.chart j).left_inv hsrc'
    obtain ⟨hsm, hsp⟩ := hs _ hU'
    obtain ⟨c, hc, hγc'⟩ := (M.fibre _ hsm _ hγ').1 (by rw [hsp, hxp])
    have hck : ∀ k, cf k y' = c k := fun k => by
      have h := congrFun hγc' ⟨k, i k⟩
      rw [hcf]
      show γ y' ⟨k, i k⟩ / s (x' y') ⟨k, i k⟩ = c k
      rw [h]
      exact mul_div_cancel_right₀ (c k) (hne' k)
    have hh : S.ref.h (γ y') = (∏ k, ‖c k‖ ^ S.ref.a k) * S.ref.h (s (x' y')) := by
      rw [hγc']; exact S.ref.smul c _ hc
    have hpos : ∀ k, 0 < ‖c k‖ := fun k => norm_pos_iff.2 (hc k)
    have hlog : Real.log (S.ref.h (γ y')) =
        ∑ k, (S.ref.a k : ℝ) * Real.log ‖c k‖ + Real.log (S.ref.h (s (x' y'))) := by
      rw [hh, Real.log_mul (Finset.prod_pos fun k _ => zpow_pos (hpos k) _).ne' (S.ref.pos _ hsm.1).ne',
        Real.log_prod fun k _ => (zpow_pos (hpos k) _).ne']
      simp only [Real.log_zpow]
    have h1 := hG1eq _ hU'
    have hsrc'' : x' y' ∈ (S.R.chart j).source := by rw [hxp]; exact hsrc'
    have h2 := hG2eq _ ⟨⟨hW', hUth hU'⟩, hsrc''⟩
    refine ⟨fun k => by rw [hck]; exact hc k, ?_⟩
    rw [hlog, ← hxp]
    simp only [hck]
    linarith
  have hcy : ∀ k, cf k y ≠ 0 := (key y hgood.self_of_nhds).1
  refine ⟨fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) * (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ)) -
    (G1 (x' y') + G2 (x' y')), ?_, ?_⟩
  · have hterm : ∀ k, AnalyticAt ℂ (fun y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := fun k => by
      have hl : AnalyticAt ℂ (fun y' => Complex.log (cf k y' / cf k y)) y := by
        refine ((hcfa k).div analyticAt_const (hcy k)).clog ?_
        show cf k y / cf k y ∈ Complex.slitPlane
        rw [div_self (hcy k)]
        exact Complex.one_mem_slitPlane
      exact analyticAt_const.mul (hl.add analyticAt_const)
    have hsum : AnalyticAt ℂ (fun y' => ∑ k, ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) y := by
      have h := Finset.analyticAt_sum (𝕜 := ℂ) (f := fun k y' => ((S.ref.a k : ℝ) : ℂ) *
        (Complex.log (cf k y' / cf k y) + (Real.log ‖cf k y‖ : ℂ))) Finset.univ fun k _ => hterm k
      convert h using 1
      ext y'
      simp [Finset.sum_apply]
    have hG12 : AnalyticAt ℂ (fun y' => G1 (x' y') + G2 (x' y')) y := hG1x.add hG2x
    exact hsum.sub hG12
  · filter_upwards [hgood] with y' hy'
    obtain ⟨hnz, heq⟩ := key y' hy'
    rw [heq]
    have hl : ∀ k, Real.log ‖cf k y' / cf k y‖ = Real.log ‖cf k y'‖ - Real.log ‖cf k y‖ := fun k => by
      rw [norm_div, Real.log_div (norm_ne_zero_iff.2 (hnz k)) (norm_ne_zero_iff.2 (hcy k))]
    simp only [Complex.sub_re, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re,
      Complex.ofReal_re, hl, sub_add_cancel]
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PSheetChartHolo
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.Regular (RegChartData)
open ReciprocityTheory.AnForm.A (coordDiv)
open ReciprocityTheory.AnForm.M (IsCompatChart)

namespace SheetChartHolo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem segre_torusSmul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    segre (torusSmul c z) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem coordDiv_null {n : ℕ} (S : Finset (Fin n)) : volume (coordDiv S) = 0 := by
  have hsub : coordDiv S ⊆ ⋃ i ∈ (S : Set (Fin n)),
      ((LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℝ] ℂ) : Submodule ℝ (Fin n → ℂ)) :
        Set (Fin n → ℂ)) := by
    rintro z ⟨i, hi, hz⟩
    exact Set.mem_biUnion hi (by simp [hz])
  refine measure_mono_null hsub ((measure_biUnion_null_iff S.countable_toSet).2 fun i _ => ?_)
  refine Measure.addHaar_submodule _ _ fun htop => ?_
  have : (Pi.single i (1 : ℂ) : Fin n → ℂ) ∈
      LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℝ] ℂ) := by
    rw [htop]; trivial
  simp at this

def patchMap {n : ℕ} (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {X : Type}
    [TopologicalSpace X] (ψ : OpenPartialHomeomorph X (Fin n → ℂ)) (s : X → (Σ k, ι k) → ℂ)
    (ξ : Fin n → ℂ) : Fin n → ℂ :=
  fun i => Q (segre (s (ψ.symm ξ))) i.succ / Q (segre (s (ψ.symm ξ))) 0


omit [∀ k, Fintype (ι k)] in
theorem patchMap_eq {P : Ideal (MRing ι)} {n : ℕ} (M : CxModel P n)
    (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (ψ : OpenPartialHomeomorph M.Xc (Fin n → ℂ)) (s : M.Xc → (Σ k, ι k) → ℂ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {x' : M.Xc} (hzx : M.proj z = x')
    (hsrc : x' ∈ ψ.source) (hs : s x' ∈ mcPts P ∧ M.proj (s x') = x') {y : Fin n → ℂ}
    (hQ : Q (segre z) = Fin.cons 1 y) :
    Q (segre (s (ψ.symm (ψ x')))) 0 ≠ 0 ∧ patchMap Q ψ s (ψ x') = y := by
  rw [ψ.left_inv hsrc]
  obtain ⟨c, -, hc⟩ := (M.fibre _ hs.1 z hz).1 (hs.2.trans hzx.symm)
  have hQ' : Q (segre z) = (∏ k, c k) • Q (segre (s x')) := by
    rw [congrArg (fun w => Q (segre w)) hc, segre_torusSmul, map_smul]
  have h0 := congrFun hQ' 0
  rw [hQ] at h0
  simp only [Fin.cons_zero, Pi.smul_apply, smul_eq_mul] at h0
  have hne : Q (segre (s x')) 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at h0
    exact one_ne_zero h0
  refine ⟨hne, funext fun i => ?_⟩
  have hi := congrFun hQ' i.succ
  rw [hQ] at hi
  simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul] at hi
  simp only [patchMap]
  rw [ψ.left_inv hsrc, div_eq_iff hne, hi]
  linear_combination (Q (segre (s x')) i.succ) * h0

theorem patchMap_analyticAt {P : Ideal (MRing ι)} {n : ℕ} (M : CxModel P n)
    (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
    (ψ : OpenPartialHomeomorph M.Xc (Fin n → ℂ)) (hψ : IsCompatChart M.atlas ψ) (U : Set M.Xc)
    (s : M.Xc → (Σ k, ι k) → ℂ) (hsh : ∀ p, M.atlas.HoloOn U fun y => s y p) {ξ : Fin n → ℂ}
    (hξ : ξ ∈ ψ.target) (hU : ψ.symm ξ ∈ U) (h0 : Q (segre (s (ψ.symm ξ))) 0 ≠ 0) :
    AnalyticAt ℂ (patchMap Q ψ s) ξ := by
  classical
  have hcoord : ∀ p, AnalyticAt ℂ (fun ξ' => s (ψ.symm ξ') p) ξ := by
    intro p
    obtain ⟨i, hi⟩ := M.atlas.cover (ψ.symm ξ)
    have hg : AnalyticAt ℂ ((fun y => s y p) ∘ (M.atlas.chart i).symm)
        (M.atlas.chart i (ψ.symm ξ)) :=
      hsh p i _ ⟨(M.atlas.chart i).map_source hi, by
        rw [Set.mem_preimage, (M.atlas.chart i).left_inv hi]; exact hU⟩
    have hh : AnalyticAt ℂ (M.atlas.chart i ∘ ψ.symm) ξ := (hψ i).2 ξ ⟨hξ, hi⟩
    refine (AnalyticAt.comp (g := (fun y => s y p) ∘ (M.atlas.chart i).symm)
      (f := M.atlas.chart i ∘ ψ.symm) hg hh).congr ?_
    have hev : ∀ᶠ ξ' in 𝓝 ξ, ψ.symm ξ' ∈ (M.atlas.chart i).source :=
      (ψ.continuousAt_symm hξ).preimage_mem_nhds ((M.atlas.chart i).open_source.mem_nhds hi)
    filter_upwards [hev] with ξ' h'
    simp [Function.comp_def, (M.atlas.chart i).left_inv h']
  have hseg : AnalyticAt ℂ (fun ξ' => segre (s (ψ.symm ξ'))) ξ :=
    AnalyticAt.pi fun m => Finset.univ.analyticAt_fun_prod fun k _ => hcoord ⟨k, m k⟩
  have hQa : AnalyticAt ℂ (fun ξ' => Q (segre (s (ψ.symm ξ')))) ξ :=
    ((LinearMap.toContinuousLinearMap Q).analyticAt _).comp hseg
  have hQm : ∀ m, AnalyticAt ℂ (fun ξ' => Q (segre (s (ψ.symm ξ'))) m) ξ := fun m =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) m).analyticAt _).comp hQa
  exact AnalyticAt.pi fun i => (hQm i.succ).div (hQm 0) h0

theorem proof : SheetChartHolo.Statement := by
  intro K _ ι _ P n M R Q
  classical

  have hpatch : ∀ x : M.Xc, ∃ (j : Fin R.N) (U : Set M.Xc) (s : M.Xc → (Σ k, ι k) → ℂ),
      IsOpen U ∧ x ∈ U ∧ x ∈ (R.chart j).source ∧ (∀ y ∈ U, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧
        ∀ p, M.atlas.HoloOn U fun y => s y p := by
    intro x
    obtain ⟨j, hj⟩ := R.cover x
    obtain ⟨U, hU, hxU, s, hs, hsh⟩ := M.sections x
    exact ⟨j, U, s, hU, hxU, R.mid_subset_source j (R.inner_subset_mid j hj), hs, hsh⟩
  choose j U s hU hxU hxj hs hsh using hpatch

  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x => U x ∩ (R.chart (j x)).source)
    (fun x => (hU x).inter (R.chart (j x)).open_source)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x, hxj x⟩)
  let F : M.Xc → (Fin n → ℂ) → (Fin n → ℂ) := fun x => patchMap Q (R.chart (j x)) (s x)
  let V : M.Xc → Set (Fin n → ℂ) := fun x => {ξ | ξ ∈ (R.chart (j x)).target ∧
    (R.chart (j x)).symm ξ ∈ U x ∧ Q (segre (s x ((R.chart (j x)).symm ξ))) 0 ≠ 0}
  have hF : ∀ x, ∀ ξ ∈ V x, AnalyticAt ℂ (F x) ξ := fun x ξ hξ =>
    patchMap_analyticAt M Q _ (R.compat (j x)) (U x) (s x) (hsh x) hξ.1 hξ.2.1 hξ.2.2
  let f' : M.Xc → (Fin n → ℂ) → ((Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) := fun x ξ =>
    (fderiv ℂ (F x) ξ).restrictScalars ℝ
  let Crit : M.Xc → Set (Fin n → ℂ) := fun x => {ξ | ξ ∈ V x ∧ (f' x ξ).det = 0}

  let B : Set (Fin n → ℂ) :=
    ⋃ x ∈ (t : Set M.Xc), (F x '' (V x ∩ coordDiv (R.S (j x))) ∪ F x '' Crit x)
  have hB : volume B = 0 := by
    refine (measure_biUnion_null_iff t.countable_toSet).2 fun x _ => measure_union_null ?_ ?_
    · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
        (measure_mono_null Set.inter_subset_right (coordDiv_null _))
      intro ξ hξ
      exact ((hF x ξ hξ.1).differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := f' x)
        (fun ξ hξ => ?_) (fun ξ hξ => hξ.2)
      exact ((hF x ξ hξ.1).differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [ae_iff]
  refine measure_mono_null ?_ hB
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy
  by_contra hyB
  apply hy
  intro w γ hγ
  obtain ⟨-, hev⟩ := hγ
  have hev0 := hev.self_of_nhds

  obtain ⟨x, hxt, hxU', hxsrc⟩ : ∃ x ∈ t, M.proj (γ y) ∈ U x ∧
      M.proj (γ y) ∈ (R.chart (j x)).source := by
    have h := ht (Set.mem_univ (M.proj (γ y)))
    simp only [Set.mem_iUnion] at h
    obtain ⟨x, hx, h⟩ := h
    exact ⟨x, hx, h⟩
  set ψ := R.chart (j x) with hψ
  set ξ0 := ψ (M.proj (γ y)) with hξ0
  obtain ⟨hne0, hFy⟩ := patchMap_eq M Q ψ (s x) hev0.2.1 rfl hxsrc (hs x _ hxU') hev0.2.2
  have hξ0V : ξ0 ∈ V x := ⟨ψ.map_source hxsrc, by rw [ψ.left_inv hxsrc]; exact hxU', hne0⟩
  have hξ0div : ξ0 ∉ coordDiv (R.S (j x)) := fun h =>
    hyB (Set.mem_biUnion hxt (Or.inl ⟨ξ0, ⟨hξ0V, h⟩, hFy⟩))
  have hξ0crit : (f' x ξ0).det ≠ 0 := fun h =>
    hyB (Set.mem_biUnion hxt (Or.inr ⟨ξ0, ⟨hξ0V, h⟩, hFy⟩))
  have hYo : M.proj (γ y) ∈ R.Yo := (R.mem_Yo (j x) _ hxsrc).2 hξ0div
  refine ⟨j x, hxsrc, hYo, ?_⟩

  have hbij : Function.Bijective (fderiv ℂ (F x) ξ0) := by
    have hu : IsUnit (LinearMap.det ((f' x ξ0 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) :
        (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))) := isUnit_iff_ne_zero.2 hξ0crit
    have h2 := (Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det
      ((f' x ξ0 : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ))).2 hu)
    exact h2
  let e : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ (F x) ξ0)
      (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have hcd : ContDiffAt ℂ 1 (F x) ξ0 := (hF x ξ0 hξ0V).contDiffAt
  have hder : HasFDerivAt (F x) (e : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) ξ0 := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact (hF x ξ0 hξ0V).differentiableAt.hasFDerivAt
  have hn1 : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero

  set G := hcd.localInverse hder hn1 with hGdef
  have hG : ContDiffAt ℂ 1 G y := by
    have := hcd.to_localInverse hder hn1
    have hFy' : F x ξ0 = y := hFy
    rwa [hFy'] at this
  have hleft : ∀ᶠ ξ in 𝓝 ξ0, G (F x ξ) = ξ :=
    (hcd.hasStrictFDerivAt' hder hn1).eventually_left_inverse

  have hmem : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := hev.mono fun _ h => h.2.1
  have hpc : Tendsto (fun y' => M.proj (γ y')) (𝓝 y) (𝓝 (M.proj (γ y))) :=
    (M.cont _ hev0.2.1).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hev0.1.continuousAt, hmem⟩)
  have hsrc_ev : ∀ᶠ y' in 𝓝 y, M.proj (γ y') ∈ U x ∩ ψ.source :=
    hpc (((hU x).inter ψ.open_source).mem_nhds ⟨hxU', hxsrc⟩)
  have hφc : Tendsto (fun y' => ψ (M.proj (γ y'))) (𝓝 y) (𝓝 ξ0) :=
    (ψ.continuousAt hxsrc).tendsto.comp hpc
  have heq : ∀ᶠ y' in 𝓝 y, ψ (M.proj (γ y')) = G y' := by
    filter_upwards [hsrc_ev, hev, hφc.eventually hleft] with y' h1 h2 h3
    have h4 := (patchMap_eq M Q ψ (s x) h2.2.1 rfl h1.2 (hs x _ h1.1) h2.2.2).2
    rw [← h3]
    exact congrArg G h4
  have hGd : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ G y' :=
    (hG.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero
  filter_upwards [hsrc_ev, heq.eventually_nhds, hGd] with y' h1 h2 h3
  exact ⟨h1.2, h3.congr_of_eventuallyEq h2⟩

end SheetChartHolo

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

