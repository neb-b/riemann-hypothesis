module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.AnalyticForms.AnalyticCharts.ExistsAnalyticGraphChartMvPolynomial
section
namespace ReciprocityTheory.AnForm

open Function

theorem hasFDerivAt_mvPolynomial_eval {n : ℕ} (Q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun y => MvPolynomial.eval y Q)
      (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j Q) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) x := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const a x
  | add p q hp hq =>
    simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hXi : HasFDerivAt (fun y : Fin n → ℂ => y i)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i) x := hasFDerivAt_apply i x
    have h2 := hp.mul hXi
    have hfun : (fun y : Fin n → ℂ => MvPolynomial.eval y (p * MvPolynomial.X i)) =
        (fun y => MvPolynomial.eval y p) * (fun y => y i) := by
      funext y
      simp
    have hder : (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X i)) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) =
        MvPolynomial.eval x p • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i +
          x i • ∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j p) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
        Derivation.leibniz, MvPolynomial.pderiv_X, map_add, MvPolynomial.smul_eval, MvPolynomial.eval_X,
        Pi.single_apply]
      simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      have hs : ∑ j, MvPolynomial.eval x (if i = j then p else 0) * v j = MvPolynomial.eval x p * v i := by
        simp [apply_ite, ite_mul, Finset.sum_ite_eq]
      rw [hs]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hfun, hder]
    exact h2

end ReciprocityTheory.AnForm
end

-- bundled from ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
section
namespace ReciprocityTheory.AnForm

open MeasureTheory Metric Filter Topology

open MeasureTheory Metric Filter Topology

private theorem analyticAt_cons_right {D : ℕ} (t : ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun v : Fin D → ℂ => (Fin.cons t v : Fin (D + 1) → ℂ)) w := by
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact analyticAt_const
  · simp only [Fin.cons_succ]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) j).analyticAt w

private theorem analyticAt_cons_left {D : ℕ} (t : ℂ) (w : Fin D → ℂ) :
    AnalyticAt ℂ (fun s : ℂ => (Fin.cons s w : Fin (D + 1) → ℂ)) t := by
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact analyticAt_id
  · simp only [Fin.cons_succ]
    exact analyticAt_const

private theorem cons_mem_ball {D : ℕ} {c : Fin (D + 1) → ℂ} {r : ℝ} (hr : 0 < r) (t : ℂ)
    (w : Fin D → ℂ) :
    (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ↔ t ∈ ball (c 0) r ∧ w ∈ ball (Fin.tail c) r := by
  simp only [ball_pi _ hr, Set.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.tail]

private theorem measurableSet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {U : Set E} (hU : IsOpen U) {f : E → ℂ}
    (hf : AnalyticOnNhd ℂ f U) : MeasurableSet {z | z ∈ U ∧ f z = 0} := by
  have h1 : IsOpen (U ∩ f ⁻¹' {0}ᶜ) :=
    hf.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  have h2 : {z | z ∈ U ∧ f z = 0} = U \ (U ∩ f ⁻¹' {0}ᶜ) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff]
    tauto
  rw [h2]
  exact hU.measurableSet.diff h1.measurableSet

private theorem nz_one {U : Set ℂ} (hc : IsPreconnected U) {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U)
    (hne : ∃ z ∈ U, g z ≠ 0) : volume {z | z ∈ U ∧ g z = 0} = 0 := by
  apply measure_null_of_locally_null
  rintro z ⟨hzU, -⟩
  rcases (hg z hzU).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨w, hwU, hgw⟩ := hne
    exact hgw (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU h hwU)
  · refine ⟨{z}, ?_, measure_singleton z⟩
    rw [mem_nhdsWithin_iff_eventually]
    rw [eventually_nhdsWithin_iff] at h
    filter_upwards [h] with x hx hxZ
    by_contra hxz
    exact hx hxz hxZ.2

private theorem nz_ball : ∀ (D : ℕ) (c : Fin D → ℂ) (r : ℝ) (f : (Fin D → ℂ) → ℂ),
    AnalyticOnNhd ℂ f (ball c r) → (∃ z ∈ ball c r, f z ≠ 0) →
    volume {z | z ∈ ball c r ∧ f z = 0} = 0 := by
  intro D
  induction D with
  | zero =>
    intro c r f _ hne
    obtain ⟨z₀, _, hz₀⟩ := hne
    have h1 : {z | z ∈ ball c r ∧ f z = 0} = ∅ := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hz
      exact hz₀ (Subsingleton.elim z z₀ ▸ hz)
    rw [h1, measure_empty]
  | succ D ih =>
    intro c r f hf hne
    obtain ⟨z₀, hz₀b, hz₀⟩ := hne
    have hr : 0 < r := pos_of_mem_ball hz₀b
    have hZm : MeasurableSet {z | z ∈ ball c r ∧ f z = 0} := measurableSet_zero isOpen_ball hf
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0
    have he : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ : Fin (D + 1) => ℂ) 0
    have h1 := (MeasurePreserving.symm e he).measure_preimage hZm.nullMeasurableSet
    rw [← h1, Measure.volume_eq_prod, Measure.prod_apply_symm (e.symm.measurable hZm)]
    have hslice : ∀ w : Fin D → ℂ, (fun t => (t, w)) ⁻¹' (e.symm ⁻¹' {z | z ∈ ball c r ∧ f z = 0}) =
        {t | (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ∧ f (Fin.cons t w) = 0} := by
      intro w
      ext t
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp_rw [hslice]
    set t₀ := z₀ 0 with ht₀_def
    have hz₀' : (Fin.cons t₀ (Fin.tail z₀) : Fin (D + 1) → ℂ) = z₀ := Fin.cons_self_tail z₀
    have hmem₀ := (cons_mem_ball hr t₀ (Fin.tail z₀)).1 (by rw [hz₀']; exact hz₀b)
    have hf' : AnalyticOnNhd ℂ (fun w => f (Fin.cons t₀ w)) (ball (Fin.tail c) r) := fun w hw =>
      (hf _ ((cons_mem_ball hr t₀ w).2 ⟨hmem₀.1, hw⟩)).comp (analyticAt_cons_right t₀ w)
    have hW0 := ih (Fin.tail c) r _ hf' ⟨Fin.tail z₀, hmem₀.2, by simpa [hz₀'] using hz₀⟩
    have hae : ∀ᵐ w ∂(volume : Measure (Fin D → ℂ)),
        volume {t | (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ∧ f (Fin.cons t w) = 0} = 0 := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hW0] with w hw
      by_cases hwb : w ∈ ball (Fin.tail c) r
      · have hw' : f (Fin.cons t₀ w) ≠ 0 := fun h0 => hw ⟨hwb, h0⟩
        have hg : AnalyticOnNhd ℂ (fun t => f (Fin.cons t w)) (ball (c 0) r) := fun t ht =>
          AnalyticAt.comp (g := f) (f := fun s => (Fin.cons s w : Fin (D + 1) → ℂ))
            (hf _ ((cons_mem_ball hr t w).2 ⟨ht, hwb⟩)) (analyticAt_cons_left t w)
        have h2 := nz_one (convex_ball (c 0) r).isPreconnected hg ⟨t₀, hmem₀.1, hw'⟩
        have hset : {t | (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ∧ f (Fin.cons t w) = 0} =
            {t | t ∈ ball (c 0) r ∧ f (Fin.cons t w) = 0} := by
          ext t
          simp only [Set.mem_ofPred_eq, cons_mem_ball hr, hwb, and_true]
        rw [hset]
        exact h2
      · have hset : {t | (Fin.cons t w : Fin (D + 1) → ℂ) ∈ ball c r ∧ f (Fin.cons t w) = 0} = ∅ := by
          ext t
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, cons_mem_ball hr]
          tauto
        rw [hset, measure_empty]
    rw [lintegral_congr_ae hae, lintegral_zero]

theorem volume_zero_set_of_analyticOnNhd {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U)
    (hc : IsPreconnected U) {f : (Fin D → ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hne : ∃ z ∈ U, f z ≠ 0) :
    volume {z | z ∈ U ∧ f z = 0} = 0 := by
  apply measure_null_of_locally_null
  rintro z ⟨hzU, -⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hzU
  refine ⟨{x | x ∈ ball z ε ∧ f x = 0}, ?_, ?_⟩
  · rw [mem_nhdsWithin_iff_eventually]
    filter_upwards [ball_mem_nhds z hε] with x hx hxZ using ⟨hx, hxZ.2⟩
  · apply nz_ball D z ε f (hf.mono hball)
    by_contra hall
    push Not at hall
    obtain ⟨w, hwU, hfw⟩ := hne
    have h1 : f =ᶠ[𝓝 z] 0 := by
      filter_upwards [ball_mem_nhds z hε] with x hx using hall x hx
    exact hfw (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU h1 hwU)

theorem volume_eq_zero_of_locally_in_analytic_zero_set {D : ℕ} (S : Set (Fin D → ℂ))
    (h : ∀ z ∈ S, ∃ W : Set (Fin D → ℂ), IsOpen W ∧ z ∈ W ∧ IsPreconnected W ∧
      ∃ f : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ f W ∧ (∃ w ∈ W, f w ≠ 0) ∧
        ∀ w ∈ S ∩ W, f w = 0) :
    volume S = 0 := by
  apply measure_null_of_locally_null
  intro z hz
  obtain ⟨W, hWo, hzW, hWc, f, hf, hne, hS⟩ := h z hz
  refine ⟨S ∩ W, inter_mem_nhdsWithin S (hWo.mem_nhds hzW), ?_⟩
  refine measure_mono_null (fun w hw => ?_) (volume_zero_set_of_analyticOnNhd hWo hWc hf hne)
  exact ⟨hw.2, hS w hw⟩

end ReciprocityTheory.AnForm
end

-- bundled from ReciprocityTheory.AnalyticForms.AnalyticCharts.OsgoodA
section
noncomputable section

namespace ReciprocityTheory.AnForm.Osgood

open Complex Metric MeasureTheory Set Filter Topology

open scoped Real

theorem differentiable_cons_right {n : ℕ} (x : ℂ) :
    Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_const x
  · simp only [Fin.cons_succ]
    exact differentiable_pi.1 differentiable_id j

theorem differentiable_cons_left {n : ℕ} (y : Fin n → ℂ) :
    Differentiable ℂ (fun x : ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact differentiable_id
  · simp only [Fin.cons_succ]
    exact differentiable_const _

theorem mem_closedBall_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    z ∈ closedBall c r ↔ ∀ i, z i ∈ closedBall (c i) r := by
  rw [closedBall_pi c hr, Set.mem_univ_pi]

theorem mem_ball_pi_iff {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) :
    z ∈ ball c r ↔ ∀ i, z i ∈ ball (c i) r := by
  rw [ball_pi c hr, Set.mem_univ_pi]

theorem norm_torusMap_sub {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => r) θ i - c i‖ = r := by
  have h : torusMap c (fun _ => r) θ i - c i = (r : ℂ) * exp ((θ i : ℂ) * I) := by
    simp only [torusMap]
    ring
  have h1 : ‖exp ((θ i : ℂ) * I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖(r : ℂ)‖ = r := by
    exact Complex.norm_of_nonneg hr
  rw [h, norm_mul, h1, h2, mul_one]

theorem torusMap_mem_closedBall {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) :
    torusMap c (fun _ => r) θ ∈ closedBall c r := by
  refine (mem_closedBall_pi_iff hr).2 fun i => ?_
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_torusMap_sub c hr θ i).le

theorem torusMap_sub_ne {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r)
    (θ : Fin n → ℝ) (i : Fin n) : torusMap c (fun _ => r) θ i - z i ≠ 0 := by
  intro h
  have h1 := (mem_ball_pi_iff hr).1 hz i
  rw [mem_ball, dist_eq_norm] at h1
  have h2 := norm_torusMap_sub c hr.le θ i
  rw [sub_eq_zero] at h
  rw [h] at h2
  linarith

theorem continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (r : ℝ) :
    Continuous (torusMap c (fun _ => r)) := by
  refine continuous_pi fun i => ?_
  simp only [torusMap]
  fun_prop

theorem continuous_comp_torusMap {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) := by
  refine continuous_iff_continuousAt.2 fun θ => ?_
  exact (hf _ (torusMap_mem_closedBall c hr θ)).continuousAt.comp
    (continuous_torusMap c r).continuousAt

theorem torusIntegrable_kernel {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) (hz : z ∈ ball c r) :
    TorusIntegrable (fun ζ => (∏ i, (ζ i - z i)⁻¹) * f ζ) c (fun _ => r) := by
  have hK : Continuous fun θ => ∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹ := by
    refine continuous_finsetProd Finset.univ fun i _ => ?_
    refine Continuous.inv₀ ?_ ?_
    · exact ((continuous_apply i).comp (continuous_torusMap c r)).sub continuous_const
    · intro θ
      exact torusMap_sub_ne hr hz θ i
  have hcont : Continuous fun θ =>
      (∏ i, (torusMap c (fun _ => r) θ i - z i)⁻¹) * f (torusMap c (fun _ => r) θ) :=
    hK.mul (continuous_comp_torusMap hr.le hf)
  unfold TorusIntegrable
  exact hcont.continuousOn.integrableOn_compact isCompact_Icc

theorem cauchy_polydisc : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : ℝ), 0 < r →
    (∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * f ζ) = (2 * π * I) ^ n * f z
  | 0, f, c, r, _, _, z, _ => by
    rw [torusIntegral_dim0]
    simp [Subsingleton.elim z c]
  | n + 1, f, c, r, hr, hf, z, hz => by
    rw [torusIntegral_succ (torusIntegrable_kernel hr hf hz)]
    have hz0 : z 0 ∈ ball (c 0) r := (mem_ball_pi_iff hr).mp hz 0
    have hz' : Fin.tail z ∈ ball (c ∘ Fin.succ) r :=
      (mem_ball_pi_iff (c := c ∘ Fin.succ) (z := Fin.tail z) hr).mpr fun i =>
        (mem_ball_pi_iff hr).mp hz i.succ
    have hcons : ∀ x ∈ closedBall (c 0) r, ∀ y ∈ closedBall (fun i => c (Fin.succ i)) r,
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c r := by
      intro x hx y hy
      refine (mem_closedBall_pi_iff hr.le).mpr fun i => ?_
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using (mem_closedBall_pi_iff hr.le).mp hy j
    have key : EqOn (fun x => ∯ y in T(c ∘ Fin.succ, (fun _ => r) ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) * f (Fin.cons x y))
        (fun x => (2 * π * I) ^ n * ((x - z 0)⁻¹ * f (Fin.cons x (Fin.tail z)))) (sphere (c 0) r) := by
      intro x hx
      have hxc : x ∈ closedBall (c 0) r := sphere_subset_closedBall hx
      have ih := cauchy_polydisc n (fun y => f (Fin.cons x y)) (fun i => c (Fin.succ i)) r hr
        (fun ζ hζ => (hf _ (hcons x hxc ζ hζ)).comp ζ (differentiable_cons_right x ζ)) (Fin.tail z) hz'
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Function.comp_def, mul_assoc]
      rw [torusIntegral_const_mul]
      simp only [Fin.tail] at ih
      rw [ih]
      ring
    rw [circleIntegral.integral_congr hr.le key, circleIntegral.integral_const_mul]
    have hd : DifferentiableOn ℂ (fun x => f (Fin.cons x (Fin.tail z))) (closedBall (c 0) r) :=
      fun x hx => ((hf _ (hcons x hx _ (ball_subset_closedBall hz'))).comp x
        (differentiable_cons_left (Fin.tail z) x)).differentiableWithinAt
    have h1 := hd.circleIntegral_sub_inv_smul hz0
    simp only [smul_eq_mul] at h1
    rw [h1, Fin.cons_self_tail, pow_succ]
    ring

end ReciprocityTheory.AnForm.Osgood
end
end

-- bundled from ReciprocityTheory.AnalyticForms.AnalyticCharts.Partition
section
namespace ReciprocityTheory.AnForm

open scoped ContDiff
open Set Metric

theorem exists_chart_partition {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {D m : ℕ} (e : Fin m → OpenPartialHomeomorph X (Fin D → ℂ))
    (hcov : ∀ x, ∃ i, x ∈ (e i).source)
    (htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) :
    ∃ χ : Fin m → X → ℝ, (∀ i x, 0 ≤ χ i x) ∧ (∀ x, ∑ i, χ i x = 1) ∧
      (∀ i, tsupport (χ i) ⊆ (e i).source) ∧
      (∀ i j, ContDiffOn ℝ ∞ (χ i ∘ (e j).symm) (e j).target) := by
  classical
  have hext : ∀ (k : Fin m) (g : (Fin D → ℂ) → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ (e k).target →
      tsupport (fun p => if p ∈ (e k).source then g (e k p) else 0) ⊆ (e k).source ∧
      ∀ j, ContDiffOn ℝ ∞ ((fun p => if p ∈ (e k).source then g (e k p) else 0) ∘ (e j).symm)
        (e j).target := by
    intro k g hg hgc hgt
    set G : X → ℝ := fun p => if p ∈ (e k).source then g (e k p) else 0 with hG
    set T : Set X := (e k).symm '' tsupport g with hT
    have hTc : IsCompact T :=
      (show IsCompact (tsupport g) from hgc).image_of_continuousOn ((e k).continuousOn_symm.mono hgt)
    have hTs : T ⊆ (e k).source := by
      rintro _ ⟨y, hy, rfl⟩
      exact (e k).map_target (hgt hy)
    have hsupp : Function.support G ⊆ T := by
      intro p hp
      rw [Function.mem_support] at hp
      by_cases hps : p ∈ (e k).source
      · simp only [hG, if_pos hps] at hp
        exact ⟨e k p, subset_tsupport g hp, (e k).left_inv hps⟩
      · simp only [hG, if_neg hps] at hp
        exact absurd rfl hp
    have hts : tsupport G ⊆ T := closure_minimal hsupp hTc.isClosed
    refine ⟨hts.trans hTs, fun j => ?_⟩
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    by_cases hp : (e j).symm y ∈ (e k).source
    · refine ⟨(e j).target ∩ (e j).symm ⁻¹' (e k).source,
        (e j).isOpen_inter_preimage_symm (e k).open_source, ⟨hy, hp⟩, ?_⟩
      have h1 : ContDiffOn ℝ ∞ (g ∘ (e k ∘ (e j).symm))
          ((e j).target ∩ (e j).symm ⁻¹' (e k).source) := hg.comp_contDiffOn (htr j k)
      refine (h1.mono Set.inter_subset_right).congr ?_
      intro y' hy'
      have hc : (e j).symm y' ∈ (e k).source := hy'.2.2
      simp only [Function.comp, hG, if_pos hc]
    · refine ⟨(e j).target ∩ (e j).symm ⁻¹' Tᶜ,
        (e j).isOpen_inter_preimage_symm hTc.isClosed.isOpen_compl,
        ⟨hy, fun hT' => hp (hTs hT')⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr ?_
      intro y' hy'
      have h2 : ¬ G ((e j).symm y') ≠ 0 := fun h => hy'.2.2 (hsupp h)
      exact not_not.mp h2
  have hb : ∀ x : X, ∃ k : Fin m, ∃ g : (Fin D → ℂ) → ℝ, x ∈ (e k).source ∧
      tsupport g ⊆ (e k).target ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      Set.range g ⊆ Set.Icc 0 1 ∧ g (e k x) = 1 := by
    intro x
    obtain ⟨k, hk⟩ := hcov x
    obtain ⟨g, h1, h2, h3, h4, h5⟩ :=
      exists_contDiff_tsupport_subset (n := ⊤) ((e k).open_target.mem_nhds ((e k).map_source hk))
    exact ⟨k, g, hk, h1, h2, h3, h4, h5⟩
  choose κ g hxs hgt hgc hgs hgr hg1 using hb
  let ψ : X → X → ℝ := fun x p => if p ∈ (e (κ x)).source then g x (e (κ x) p) else 0
  have hψ0 : ∀ x p, 0 ≤ ψ x p := by
    intro x p
    simp only [ψ]
    split_ifs
    · exact (hgr x ⟨_, rfl⟩).1
    · exact le_rfl
  have hψext := fun x => hext (κ x) (g x) (hgs x) (hgc x) (hgt x)
  let O : X → Set X := fun x => (e (κ x)).source ∩ (e (κ x)) ⁻¹' {v | 1 / 2 < g x v}
  have hO : ∀ x, IsOpen (O x) := fun x =>
    (e (κ x)).continuousOn.isOpen_inter_preimage (e (κ x)).open_source
      (isOpen_lt continuous_const (hgs x).continuous)
  have hxO : ∀ x, x ∈ O x := by
    intro x
    refine ⟨hxs x, ?_⟩
    show (1 : ℝ) / 2 < g x (e (κ x) x)
    rw [hg1 x]
    norm_num
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => Set.mem_iUnion.mpr ⟨p, hxO p⟩)
  have hOψ : ∀ x p, p ∈ O x → 1 / 2 < ψ x p := by
    intro x p hp
    simp only [ψ, if_pos hp.1]
    exact hp.2
  have hS : ∀ p, 0 < ∑ x ∈ t, ψ x p := by
    intro p
    have hp := ht (Set.mem_univ p)
    simp only [Set.mem_iUnion] at hp
    obtain ⟨x, hx, hpx⟩ := hp
    have h1 := hOψ x p hpx
    have h2 := Finset.single_le_sum (fun y _ => hψ0 y p) hx
    linarith
  refine ⟨fun k p => (∑ x ∈ t.filter (fun x => κ x = k), ψ x p) / ∑ x ∈ t, ψ x p, ?_, ?_, ?_, ?_⟩
  · intro k p
    exact div_nonneg (Finset.sum_nonneg fun x _ => hψ0 x p) (hS p).le
  · intro p
    rw [← Finset.sum_div, Finset.sum_fiberwise]
    exact div_self (hS p).ne'
  · intro k
    have hC : IsClosed (⋃ x ∈ t.filter (fun x => κ x = k), tsupport (ψ x)) :=
      isClosed_biUnion_finset fun x _ => isClosed_tsupport _
    refine (closure_minimal ?_ hC).trans ?_
    · intro p hp
      rw [Function.mem_support] at hp
      have hnum : ∑ x ∈ t.filter (fun x => κ x = k), ψ x p ≠ 0 := fun h => hp (by simp only [h, zero_div])
      obtain ⟨x, hx, hxp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnum
      exact Set.mem_biUnion hx (subset_tsupport _ hxp)
    · intro p hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨x, hx, hpx⟩ := hp
      have hk : κ x = k := (Finset.mem_filter.mp hx).2
      have hsrc := (hψext x).1 hpx
      rw [hk] at hsrc
      exact hsrc
  · intro k j
    have hnum : ContDiffOn ℝ ∞ (fun y => ∑ x ∈ t.filter (fun x => κ x = k), ψ x ((e j).symm y))
        (e j).target := ContDiffOn.sum fun x _ => (hψext x).2 j
    have hden : ContDiffOn ℝ ∞ (fun y => ∑ x ∈ t, ψ x ((e j).symm y)) (e j).target :=
      ContDiffOn.sum fun x _ => (hψext x).2 j
    exact hnum.div hden fun y _ => (hS _).ne'

end ReciprocityTheory.AnForm
end

