module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import Lemmata.CharacterDirections.Cdir

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxD
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem isOpen_ovl (j i : ι) : IsOpen (ovl A.chart j i) :=
  (A.chart j).isOpen_inter_preimage_symm (A.chart i).open_source

theorem trans_contDiffOn (j i : ι) :
    ContDiffOn ℂ ∞ ((A.chart i) ∘ (A.chart j).symm) (ovl A.chart j i) := by
  refine contDiffOn_piLp' 2 fun k => ?_
  have h : DifferentiableOn ℂ (fun x => ((A.chart i) ((A.chart j).symm x)) k) (ovl A.chart j i) :=
    (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn (A.holo_trans j i)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.isOpen_ovl j i) h

def chiC (i : ι) (β : V n → ℝ) (y : Y) : ℝ :=
  open Classical in if y ∈ (A.chart i).source then β (A.chart i y) else 0

theorem chiC_of_mem {i : ι} {β : V n → ℝ} {y : Y} (hy : y ∈ (A.chart i).source) :
    A.chiC i β y = β (A.chart i y) := by simp [chiC, hy]

theorem chiC_eq_zero {i : ι} {β : V n → ℝ} {K0 : Set (V n)} (hβs : ∀ u, β u ≠ 0 → u ∈ K0)
    {y : Y} (hy : y ∉ (A.chart i).symm '' K0) : A.chiC i β y = 0 := by
  unfold chiC
  split_ifs with h
  · by_contra hne
    exact hy ⟨_, hβs _ hne, (A.chart i).left_inv h⟩
  · rfl

theorem isCompact_chartImage {i : ι} {K0 : Set (V n)} (hK0 : IsCompact K0)
    (hK0t : K0 ⊆ (A.chart i).target) : IsCompact ((A.chart i).symm '' K0) :=
  hK0.image_of_continuousOn ((A.chart i).continuousOn_symm.mono hK0t)

theorem chartImage_subset {i : ι} {K0 : Set (V n)} (hK0t : K0 ⊆ (A.chart i).target) :
    (A.chart i).symm '' K0 ⊆ (A.chart i).source := by
  rintro _ ⟨u, hu, rfl⟩; exact (A.chart i).map_target (hK0t hu)

theorem chiC_smooth {i : ι} {β : V n → ℝ} (hβ : ContDiff ℝ ∞ β) {K0 : Set (V n)}
    (hβs : ∀ u, β u ≠ 0 → u ∈ K0) (hK0 : IsCompact K0) (hK0t : K0 ⊆ (A.chart i).target) :
    A.SmoothFn (A.chiC i β) := by
  intro j
  refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
  by_cases hx : (A.chart j).symm v ∈ (A.chart i).source
  · refine ⟨ovl A.chart j i, A.isOpen_ovl j i, ⟨hv, hx⟩, ?_⟩
    refine (hβ.comp_contDiffOn (((A.trans_contDiffOn j i).restrict_scalars ℝ).mono
      Set.inter_subset_right)).congr fun v' hv' => ?_
    simp only [Function.comp]
    exact A.chiC_of_mem hv'.2.2
  · have hKc := (A.isCompact_chartImage hK0 hK0t).isClosed
    have hxK : (A.chart j).symm v ∉ (A.chart i).symm '' K0 :=
      fun h => hx (A.chartImage_subset hK0t h)
    refine ⟨(A.chart j).target ∩ (A.chart j).symm ⁻¹' ((A.chart i).symm '' K0)ᶜ,
      (A.chart j).isOpen_inter_preimage_symm hKc.isOpen_compl, ⟨hv, hxK⟩, ?_⟩
    refine (contDiffOn_const (c := (0 : ℝ))).congr fun v' hv' => ?_
    simp only [Function.comp]
    exact A.chiC_eq_zero hβs hv'.2.2

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaCHessComp
section
open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ}

theorem cmpa_cHess_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) :
    cHess n (h ∘ τ) x = (Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).transpose * cHess n h (τ x) *
      (Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).map conj := by
  ext j k
  simp only [cHess, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [cmpa_hess_comp hU hxU hτ hh j k]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem cmpa_det_jac (L : V n →L[ℂ] V n) :
    (Matrix.of fun l j => (L (bas n j)) l).det = L.det := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  congr 1

theorem cmpa_det_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) :
    (cHess n (h ∘ τ) x).det = (((‖(fderiv ℂ τ x).det‖ ^ 2 : ℝ)) : ℂ) * (cHess n h (τ x)).det := by
  rw [cmpa_cHess_comp hU hxU hτ hh, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hc : ((Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).map conj).det =
      conj ((Matrix.of fun l j => (fderiv ℂ τ x (bas n j)) l).det) :=
    (RingHom.map_det (starRingEnd ℂ) _).symm
  rw [hc, cmpa_det_jac, Complex.sq_norm, ← Complex.mul_conj]
  ring

theorem cmpa_wdb_log {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℂ 2 g y) (hy : g y ≠ 0) (k : Fin n) :
    wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) y = conj (fderiv ℂ g y (bas n k) / g y) := by
  have hgd : DifferentiableAt ℂ g y := hg.differentiableAt (by simp)
  have hgR : HasFDerivAt g ((fderiv ℂ g y).restrictScalars ℝ) y := hgd.hasFDerivAt.restrictScalars ℝ
  have hN := hgR.norm_sq
  have hpos : ‖g y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy)
  have hL := hN.log hpos
  have hF := Complex.ofRealCLM.hasFDerivAt.comp y hL
  unfold wdb
  rw [show (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) =
    ⇑Complex.ofRealCLM ∘ fun v => Real.log (‖g v‖ ^ 2) from rfl, hF.fderiv]
  have hG : (g y).re * (g y).re + (g y).im * (g y).im ≠ 0 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm]; exact hpos
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_restrictScalars', map_smul, innerSL_apply_apply, Complex.ofRealCLM_apply,
    smul_eq_mul, nsmul_eq_mul, Complex.inner, Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq_apply] <;>
    field_simp <;>
    ring

private theorem wd_conj_of_complex_differentiableAt_eq_zero {h : V n → ℂ} {y : V n} (hh : DifferentiableAt ℂ h y) (j : Fin n) :
    wd n j (fun v => (starRingEnd ℂ) (h v)) y = 0 := by
  have H := (hh.hasFDerivAt.restrictScalars ℝ).star
  have H2 : fderiv ℝ (fun v => (starRingEnd ℂ) (h v)) y =
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ h y).restrictScalars ℝ) := H.fderiv
  simp only [wd, H2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  try simp only [Complex.I_sq]
  try ring

theorem cmpa_hess_log {g : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U) (hxU : x ∈ U)
    (hg : DifferentiableOn ℂ g U) (hne : ∀ v ∈ U, g v ≠ 0) (j k : Fin n) :
    wd n j (wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ))) x = 0 := by
  have hgs : ContDiffOn ℂ ∞ g U := contDiffOn_of_differentiableOn n g U hU hg
  have ev : wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun v => conj (fderiv ℂ g v (bas n k) / g v) := by
    filter_upwards [hU.mem_nhds hxU] with v hv
    exact cmpa_wdb_log ((contDiffOn_infty.1 hgs 2).contDiffAt (hU.mem_nhds hv)) (hne v hv) k
  have e1 : wd n j (wdb n k (fun v => ((Real.log (‖g v‖ ^ 2) : ℝ) : ℂ))) x =
      wd n j (fun v => conj (fderiv ℂ g v (bas n k) / g v)) x := by
    simp only [wd, ev.fderiv_eq]
  rw [e1]
  apply wd_conj_of_complex_differentiableAt_eq_zero
  have hD : ContDiffOn ℂ ∞ (fderiv ℂ g) U := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hgs).2
  have h1 := (((hD.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)).clm_apply
    (differentiableAt_const (bas n k))).mul ((hg.differentiableAt (hU.mem_nhds hxU)).inv (hne x hxU))
  exact h1

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IteratedFDerivEqZeroOfIsBigO
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics Metric Set
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem fderiv_isBigO_of_isBigO_pow {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) {m : ℕ}
    (hO : f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1 + 1)) :
    fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by
  first | exact Bl.CoprimeDirections.goal1 .. | (apply Bl.CoprimeDirections.goal1 <;> assumption) | (intros; apply Bl.CoprimeDirections.goal1 <;> assumption)

theorem isBigO_succ_of_fderiv_isBigO {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : V n → F} {U : Set (V n)} {x : V n} (hU : IsOpen U) (hx : x ∈ U)
    (hf : DifferentiableOn ℂ f U) (h0 : f x = 0) {m : ℕ}
    (hO : fderiv ℂ f =O[𝓝 x] fun v => ‖v - x‖ ^ m) :
    f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1) := by
  obtain ⟨c, hc0, hc⟩ := hO.exists_pos
  rw [isBigOWith_iff] at hc
  obtain ⟨ε, hε0, hε⟩ := Metric.eventually_nhds_iff_ball.1 (hc.and (hU.mem_nhds hx))
  rw [isBigO_iff]
  refine ⟨c, ?_⟩
  filter_upwards [ball_mem_nhds x hε0] with v hv
  rw [norm_pow, norm_norm]
  have hvx : ‖v - x‖ < ε := by rwa [mem_ball, dist_eq_norm] at hv
  have hsub : closedBall x ‖v - x‖ ⊆ ball x ε := closedBall_subset_ball hvx
  have hmv := (convex_closedBall x ‖v - x‖).norm_image_sub_le_of_norm_fderiv_le
    (f := f) (C := c * ‖v - x‖ ^ m)
    (fun w hw => (hf w (hε _ (hsub hw)).2).differentiableAt (hU.mem_nhds (hε _ (hsub hw)).2))
    (fun w hw => by
      calc ‖fderiv ℂ f w‖ ≤ c * ‖‖w - x‖ ^ m‖ := (hε _ (hsub hw)).1
        _ = c * ‖w - x‖ ^ m := by rw [norm_pow, norm_norm]
        _ ≤ c * ‖v - x‖ ^ m := by
          gcongr
          rw [mem_closedBall, dist_eq_norm] at hw; exact hw)
    (mem_closedBall_self (norm_nonneg _)) (mem_closedBall.2 (by rw [dist_eq_norm]))
  rw [h0, sub_zero] at hmv
  calc ‖f v‖ ≤ c * ‖v - x‖ ^ m * ‖v - x‖ := hmv
    _ = c * ‖v - x‖ ^ (m + 1) := by ring

theorem top_ne_zero_withTop : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  exact_mod_cast (show (⊤ : ℕ∞) ≠ 0 by simp)

theorem top_add_one_le_top :
    ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤)

theorem iteratedFDeriv_eq_zero_of_isBigO_alt {n : ℕ} (m : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : V n → F) (U : Set (V n)) (x : V n), IsOpen U → x ∈ U →
    ContDiffOn ℂ ∞ f U → (f =O[𝓝 x] fun v => ‖v - x‖ ^ (m + 1)) →
    ∀ k ≤ m, iteratedFDeriv ℂ k f x = 0 := by
  induction m with
  | zero =>
    intro F _ _ f U x hU hx hf hO k hk
    obtain rfl : k = 0 := by omega
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero]
    exact hO.eq_zero_of_norm_pow (by omega)
  | succ m ih =>
    intro F _ _ f U x hU hx hf hO k hk
    rcases k with _ | k
    · rw [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero]
      exact hO.eq_zero_of_norm_pow (by omega)
    · have hd : ContDiffOn ℂ ∞ (fderiv ℂ f) U := hf.fderiv_of_isOpen hU top_add_one_le_top
      have hO' := fderiv_isBigO_of_isBigO_pow hU hx (hf.differentiableOn top_ne_zero_withTop) hO
      rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, norm_eq_zero]
      exact ih (fderiv ℂ f) U x hU hx hd hO' k (by omega)

theorem isBigO_pow_of_iteratedFDeriv_zero {n : ℕ} (m : ℕ) : ∀ {F : Type u} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : V n → F) (U : Set (V n)) (x : V n), IsOpen U → x ∈ U →
    ContDiffOn ℂ ∞ f U → (∀ k < m, iteratedFDeriv ℂ k f x = 0) →
    f =O[𝓝 x] fun v => ‖v - x‖ ^ m := by
  induction m with
  | zero =>
    intro F _ _ f U x hU hx hf _
    simp only [pow_zero]
    exact (hf.continuousOn.continuousAt (hU.mem_nhds hx)).tendsto.isBigO_one ℝ
  | succ m ih =>
    intro F _ _ f U x hU hx hf h
    have h0 : f x = 0 := by
      have := h 0 (by omega)
      rwa [← norm_eq_zero, norm_iteratedFDeriv_zero, norm_eq_zero] at this
    have hd : ContDiffOn ℂ ∞ (fderiv ℂ f) U := hf.fderiv_of_isOpen hU top_add_one_le_top
    have hO := ih (fderiv ℂ f) U x hU hx hd (fun k hk => by
      rw [← norm_eq_zero, norm_iteratedFDeriv_fderiv, norm_eq_zero]
      exact h (k + 1) (by omega))
    exact isBigO_succ_of_fderiv_isBigO hU hx (hf.differentiableOn top_ne_zero_withTop) h0 hO

theorem iteratedFDeriv_eq_zero_of_bound {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (hO : ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1)) :
    ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0 := by
  intro k hk
  have hc := contDiffOn_of_differentiableOn n g U hU hg
  obtain ⟨C, hC⟩ := hO
  have hO' : g =O[𝓝 v0] fun v => ‖v - v0‖ ^ (m + 1) := by
    rw [isBigO_iff]
    exact ⟨C, hC.mono fun v hv => by rwa [norm_pow, norm_norm]⟩
  exact iteratedFDeriv_eq_zero_of_isBigO_alt m g U v0 hU hv hc hO' k hk

theorem bound_of_iteratedFDeriv_eq_zero {n : ℕ} (g : V n → ℂ) (U : Set (V n)) (v0 : V n)
    (hU : IsOpen U) (hv : v0 ∈ U) (hg : DifferentiableOn ℂ g U) (m : ℕ)
    (h : ∀ k ≤ m, iteratedFDeriv ℂ k g v0 = 0) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 v0, ‖g v‖ ≤ C * ‖v - v0‖ ^ (m + 1) := by
  have hc := contDiffOn_of_differentiableOn n g U hU hg
  have hb := isBigO_pow_of_iteratedFDeriv_zero (m + 1) g U v0 hU hv hc (fun k hk => h k (by omega))
  obtain ⟨C, hC⟩ := isBigO_iff.1 hb
  exact ⟨C, hC.mono fun v hv => by rwa [norm_pow, norm_norm] at hv⟩

end

end ReciprocityTheory.L2DbarEstimates.Y
end

