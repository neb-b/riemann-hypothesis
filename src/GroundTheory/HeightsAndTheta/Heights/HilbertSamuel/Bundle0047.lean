module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartTaylorCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Metric ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights
open scoped ContDiff

noncomputable section

namespace ChartTaylorCover

theorem inv_sum_pos {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    0 < (∑ k ∈ t, 1 / a k + 1)⁻¹ := by
  have : 0 ≤ ∑ k ∈ t, 1 / a k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le
  positivity

theorem inv_sum_le {ι : Type*} (t : Finset ι) (a : ι → ℝ) (ha : ∀ i, 0 < a i) {i : ι}
    (hi : i ∈ t) : (∑ k ∈ t, 1 / a k + 1)⁻¹ ≤ a i := by
  have h1 : 1 / a i ≤ ∑ k ∈ t, 1 / a k :=
    Finset.single_le_sum (f := fun k => 1 / a k) (fun k _ => (one_div_pos.2 (ha k)).le) hi
  have h0 : 0 < ∑ k ∈ t, 1 / a k + 1 := by
    have : 0 ≤ ∑ k ∈ t, 1 / a k := Finset.sum_nonneg fun k _ => (one_div_pos.2 (ha k)).le
    linarith
  rw [inv_le_comm₀ h0 (ha i), ← one_div]
  linarith

theorem norm_sq_le_sum {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ i, ‖z i‖ ^ 2 := by
  have hS : 0 ≤ ∑ i, ‖z i‖ ^ 2 := by positivity
  have h : ‖z‖ ≤ √(∑ i, ‖z i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    exact (Real.le_sqrt (norm_nonneg _) hS).2
      (Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun k _ => by positivity)
        (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ (√(∑ i, ‖z i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ i, ‖z i‖ ^ 2 := Real.sq_sqrt hS

theorem taylor_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) {y z : E} {M : ℝ}
    (hB : closedBall y ‖z‖ ⊆ U) (hM : ∀ w ∈ closedBall y ‖z‖, ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ M) :
    f (y + z) ≤ f y + fderiv ℝ f y z + M * ‖z‖ ^ 2 := by
  set s := closedBall y ‖z‖ with hs
  have hconv : Convex ℝ s := convex_closedBall _ _
  have hys : y ∈ s := mem_closedBall_self (norm_nonneg z)
  have hyzs : y + z ∈ s := by
    rw [hs, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ f) y)) (hM y hys)
  have hca : ∀ w ∈ U, ContDiffAt ℝ 2 f w := fun w hw => hf.contDiffAt (hU.mem_nhds hw)
  have hd1 : ∀ w ∈ s, DifferentiableAt ℝ f w := fun w hw =>
    (hca w (hB hw)).differentiableAt (by norm_num)
  have hd2 : ∀ w ∈ s, DifferentiableAt ℝ (fderiv ℝ f) w := fun w hw =>
    ((hca w (hB hw)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set ℓ := fderiv ℝ f y with hℓ
  have h1 : ∀ w ∈ s, ‖fderiv ℝ f w - ℓ‖ ≤ M * ‖z‖ := by
    intro w hw
    have := hconv.norm_image_sub_le_of_norm_fderiv_le hd2 hM hys hw
    have hw' : ‖w - y‖ ≤ ‖z‖ := by rwa [hs, mem_closedBall, dist_eq_norm] at hw
    exact this.trans (mul_le_mul_of_nonneg_left hw' hM0)
  have hh : ∀ w ∈ s, HasFDerivWithinAt (fun w => f w - ℓ w) (fderiv ℝ f w - ℓ) s w :=
    fun w hw => ((hd1 w hw).hasFDerivAt.sub ℓ.hasFDerivAt).hasFDerivWithinAt
  have h2 := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le hh h1 hys hyzs
  have h3 := (Real.le_norm_self _).trans h2
  rw [map_add (f := _), add_sub_cancel_left] at h3
  have h4 : M * ‖z‖ * ‖z‖ = M * ‖z‖ ^ 2 := by ring
  linarith

theorem weight_contDiffOn {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
    {L : HolLineBundle A} (W : Weight L) (j : Fin A.n) :
    ContDiffOn ℝ 2 (W.φ j ∘ (A.chart j).symm) (A.chart j).target :=
  ((W.smooth j j).of_le (by norm_cast : (2 : WithTop ℕ∞) ≤ ∞)).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩

theorem proof : ChartTaylorCover.Statement := by
  intro D X _ _ _ _ _ A L W₀ W₁ dV
  classical
  have hsrc : ∀ p, p ∈ (A.chart (chartIdx A p)).source := fun p =>
    Classical.choose_spec (A.cover p)

  have hrad : ∀ p : X, ∃ ρ : ℝ, 0 < ρ ∧
      closedBall (A.chart (chartIdx A p) p) (2 * ρ) ⊆ (A.chart (chartIdx A p)).target := by
    intro p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (A.chart (chartIdx A p)).open_target _
      ((A.chart _).map_source (hsrc p))
    exact ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hball⟩
  choose ρ hρ hρB using hrad

  have hdens : ∀ p : X, ∃ c : ℝ, 0 < c ∧
      ∀ y ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p), c ≤ dV.dens (chartIdx A p) y := by
    intro p
    have hne : (closedBall (A.chart (chartIdx A p) p) (2 * ρ p)).Nonempty :=
      nonempty_closedBall.2 (by linarith [hρ p])
    obtain ⟨y₀, hy₀, hmin⟩ := (isCompact_closedBall _ _).exists_isMinOn hne
      ((dV.smooth _).continuousOn.mono (hρB p))
    exact ⟨dV.dens _ y₀, dV.pos _ _ (hρB p hy₀), fun y hy => isMinOn_iff.1 hmin y hy⟩
  choose c hc hcB using hdens

  have hsec : ∀ (W : Weight L) (p : X), ∃ M : ℝ,
      ∀ w ∈ closedBall (A.chart (chartIdx A p) p) (2 * ρ p),
        ‖fderiv ℝ (fderiv ℝ (W.φ (chartIdx A p) ∘ (A.chart (chartIdx A p)).symm)) w‖ ≤ M := by
    intro W p
    have hop := (A.chart (chartIdx A p)).open_target
    have h1 := (weight_contDiffOn W (chartIdx A p)).fderiv_of_isOpen hop (m := 1) (by norm_num)
    exact (isCompact_closedBall _ _).exists_bound_of_continuousOn
      ((h1.continuousOn_fderiv_of_isOpen hop le_rfl).mono (hρB p))
  choose M hM using hsec

  let V : X → Set X := fun p => (A.chart (chartIdx A p)).source ∩
    (A.chart (chartIdx A p)) ⁻¹' ball (A.chart (chartIdx A p) p) (ρ p)
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (A.chart _).continuousOn.isOpen_inter_preimage (A.chart _).open_source isOpen_ball
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun p _ => mem_iUnion.2 ⟨p, hsrc p, by exact Set.mem_preimage.mpr (mem_ball_self (hρ p))⟩)
  set Mt := ∑ p ∈ t, (|M W₀ p| + |M W₁ p|) with hMt
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun p _ => by positivity
  refine ⟨(∑ p ∈ t, 1 / ρ p + 1)⁻¹, inv_sum_pos t ρ hρ, Mt, (∑ p ∈ t, 1 / c p + 1)⁻¹,
    inv_sum_pos t c hc, ?_⟩
  intro x
  obtain ⟨p, hpt, hxV⟩ : ∃ p ∈ t, x ∈ V p := by simpa using ht (mem_univ x)
  set j := chartIdx A p with hj
  have hxs : x ∈ (A.chart j).source := hxV.1
  have hxb : A.chart j x ∈ ball (A.chart j p) (ρ p) := hxV.2
  have hr := inv_sum_le t ρ hρ hpt
  have hsub : closedBall (A.chart j x) (∑ p ∈ t, 1 / ρ p + 1)⁻¹ ⊆
      closedBall (A.chart j p) (2 * ρ p) := by
    refine closedBall_subset_closedBall' ?_
    have := mem_ball.1 hxb
    linarith
  refine ⟨j, hxs, hsub.trans (hρB p), fun y hy => (inv_sum_le t c hc hpt).trans (hcB p y (hsub hy)),
    ?_⟩

  have key : ∀ W : Weight L, |M W p| ≤ Mt → ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ,
      ‖z‖ ≤ (∑ p ∈ t, 1 / ρ p + 1)⁻¹ →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + Mt * ∑ i, ‖z i‖ ^ 2 := by
    intro W hWM
    refine ⟨fderiv ℝ (W.φ j ∘ (A.chart j).symm) (A.chart j x), fun z hz => ?_⟩
    have hzB : closedBall (A.chart j x) ‖z‖ ⊆ closedBall (A.chart j p) (2 * ρ p) :=
      (closedBall_subset_closedBall hz).trans hsub
    have hT := taylor_le (A.chart j).open_target (weight_contDiffOn W j) (hzB.trans (hρB p))
      (fun w hw => (hM W p w (hzB hw)).trans (le_abs_self _))
    have hx' : (W.φ j ∘ (A.chart j).symm) (A.chart j x) = W.φ j x := by
      simp only [Function.comp_apply, (A.chart j).left_inv hxs]
    rw [hx'] at hT
    have h1 : |M W p| * ‖z‖ ^ 2 ≤ Mt * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right hWM (by positivity)
    have h2 : Mt * ‖z‖ ^ 2 ≤ Mt * ∑ i, ‖z i‖ ^ 2 := mul_le_mul_of_nonneg_left (norm_sq_le_sum z) hMt0
    simp only [Function.comp_apply] at hT
    linarith
  intro W hW
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hW
  rcases hW with rfl | rfl
  · refine key _ ?_
    calc |M W p| ≤ |M W p| + |M W₁ p| := le_add_of_nonneg_right (abs_nonneg _)
      _ ≤ Mt := Finset.single_le_sum (f := fun p => |M W p| + |M W₁ p|)
          (fun k _ => by positivity) hpt
  · refine key _ ?_
    calc |M W p| ≤ |M W₀ p| + |M W p| := le_add_of_nonneg_left (abs_nonneg _)
      _ ≤ Mt := Finset.single_le_sum (f := fun p => |M W₀ p| + |M W p|)
          (fun k _ => by positivity) hpt

end ChartTaylorCover

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace Conductor

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) : Ω := ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹

theorem invMon_add (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ ε : K → ℕ) :
    invMon y c (δ + ε) = invMon y c δ * invMon y c ε := by
  rw [invMon, invMon, invMon, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add, mul_inv]

theorem invMon_sum {β : Type} (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (s : Finset β) (δ : β → K → ℕ) :
    ∏ b ∈ s, invMon y c (δ b) = invMon y c (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [invMon]
  | insert b s hb ih => rw [Finset.prod_insert hb, Finset.sum_insert hb, ih, invMon_add]

theorem prod_zpow_eq_invMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (δ : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(δ k : ℤ)) = invMon y c δ := by
  simp [invMon, zpow_neg, zpow_natCast]

theorem form_mul_invMon_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {δ : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g δ) : aeval y g * invMon y c δ ∈ chartRingZ y c := by
  rw [← prod_zpow_eq_invMon, NmSectionsRationalProof.aeval_mul_prod_zpow y c hg, chartRingZ,
    Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem isFractionRing_chartRingZ (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : IsFractionRing (chartRingZ y c) Ω := by
  refine IsFractionRing.of_field (chartRingZ y c) Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : invMon y c d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => inv_ne_zero (pow_ne_zero _ (hc k))
  refine ⟨⟨_, form_mul_invMon_mem y c hg⟩, ⟨_, form_mul_invMon_mem y c hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

theorem exists_chart_conductor (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (δ : K → ℕ) (F : MRing ι), IsMultiHomog F δ ∧ aeval y F ≠ 0 ∧
      ∀ x ∈ integralClosure (chartRingZ y c) Ω, aeval y F * invMon y c δ * x ∈ chartRingZ y c := by
  classical
  set A := chartRingZ y c
  have := isFractionRing_chartRingZ y hbir c hc
  have : Algebra.FiniteType ℤ A := .adjoin_of_finite (Set.finite_range _)
  have hfin : Module.Finite A (integralClosure A Ω) := Model.FiniteIntegralClosure.proof A Ω Ω
  obtain ⟨s, hs⟩ := hfin.fg_top
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.image fun z : integralClosure A Ω => (z : Ω))
  have key : ∀ z : integralClosure A Ω, ((b : A) : Ω) * (z : Ω) ∈ A := by
    intro z
    have hz : z ∈ Submodule.span A (s : Set (integralClosure A Ω)) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨u, hu⟩ := hb _ (Finset.mem_image_of_mem _ hw)
      have : (u : Ω) = ((b : A) : Ω) * (w : Ω) := by rw [Algebra.smul_def] at hu; exact hu
      rw [← this]; exact u.2
    | zero => simp
    | add w v _ _ hw hv => rw [Subalgebra.coe_add, mul_add]; exact add_mem hw hv
    | smul r w _ hw =>
      rw [Subalgebra.coe_smul, Algebra.smul_def, mul_left_comm]
      exact mul_mem r.2 hw
  have hb0 : ((b : A) : Ω) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero b (Subtype.ext h)
  obtain ⟨δ, e, he, hv⟩ := SectionBounded.exists_form_of_mem_chartRingZ y c hc (b : A).2
  have hm : (∏ k, y ⟨k, c k⟩ ^ δ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hbv : aeval y e * invMon y c δ = ((b : A) : Ω) := by
    rw [hv, invMon, Finset.prod_inv_distrib, mul_assoc, mul_inv_cancel₀ hm, mul_one]
  refine ⟨δ, e, he, by rw [hv]; exact mul_ne_zero hb0 hm, fun x hx => ?_⟩
  rw [hbv]
  exact key ⟨x, hx⟩

theorem homog_prod {β : Type} (s : Finset β) (F : β → MRing ι) (δ : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (F b) (δ b)) : IsMultiHomog (∏ b ∈ s, F b) (∑ b ∈ s, δ b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SectionBounded.homog_one (ι := ι))
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact SectionBounded.homog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

end Conductor

theorem Conductor.proof (hS : SecEq.Statement) : KH.CondStatement := by
  classical
  intro K _ ι _ Ω _ y a ha hy hbir
  obtain ⟨τ₀, hτ₀⟩ := hS K ι Ω y a ha hy
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  choose i0 hi0 using hy
  set Δ : K → ℕ := ∑ c : C, δ c
  set k' : ℕ := τ₀ + ∑ κ, Δ κ
  have hΔ : ∀ κ, Δ κ ≤ k' * a κ := fun κ =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ κ)).trans
      ((Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_right _ (ha κ)))
  set e : K → ℕ := fun κ => k' * a κ - Δ κ
  set Φ : MRing ι := (∏ c : C, F c) * SectionBounded.chartMon i0 e
  have hΦ : IsMultiHomog Φ (fun κ => k' * a κ) :=
    SectionBounded.homog_congr (SectionBounded.homog_mul
      (Conductor.homog_prod Finset.univ F δ fun c _ => hF c) (SectionBounded.homog_chartMon i0 e))
      fun κ => by simp only [Pi.add_apply, e]; exact Nat.add_sub_cancel' (hΔ κ)
  have hM : aeval y (SectionBounded.chartMon i0 e) ≠ 0 := by
    rw [SectionBounded.aeval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun κ _ => pow_ne_zero _ (hi0 κ)
  have hΦ0 : aeval y Φ ≠ 0 := by
    rw [map_mul, map_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c) hM
  refine ⟨k', Φ, hΦ, hΦ0, fun τ s hs => ?_⟩
  rw [← hτ₀ (τ + k') (by omega)]
  intro c' hc'
  set c : C := ⟨c', hc'⟩
  have hx := hs c' hc'
  have hτ : (fun κ => τ * a κ) + Δ + e = fun κ => (τ + k') * a κ := by
    funext κ
    simp only [Pi.add_apply, e]
    rw [add_assoc, Nat.add_sub_cancel' (hΔ κ)]
    ring
  have hexp : ∀ n : K → ℕ, (∏ κ, y ⟨κ, c' κ⟩ ^ (-((n κ : ℕ) : ℤ))) = Conductor.invMon y c' n :=
    Conductor.prod_zpow_eq_invMon y c'
  beta_reduce at hx ⊢
  have e1 : ∀ κ, -((τ : ℤ) * (a κ : ℤ)) = -(((τ * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  have e2 : ∀ κ, -(((τ + k' : ℕ) : ℤ) * (a κ : ℤ)) = -((((τ + k') * a κ : ℕ)) : ℤ) := fun κ => by push_cast; ring
  simp only [e1] at hx
  simp only [e2]
  rw [hexp (fun κ => τ * a κ)] at hx
  rw [hexp (fun κ => (τ + k') * a κ), ← hτ, Conductor.invMon_add, Conductor.invMon_add,
    ← Conductor.invMon_sum y c' Finset.univ δ]
  have hsplit : aeval y Φ * s * (Conductor.invMon y c' (fun κ => τ * a κ) *
      (∏ b : C, Conductor.invMon y c' (δ b)) * Conductor.invMon y c' e) =
      (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
        (aeval y (SectionBounded.chartMon i0 e) * Conductor.invMon y c' e) *
        (aeval y (F c) * Conductor.invMon y c' (δ c) * (s * Conductor.invMon y c' (fun κ => τ * a κ))) := by
    rw [map_mul, map_prod]
    rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
      ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
      Finset.prod_mul_distrib]
    ring
  rw [hsplit]
  refine mul_mem (mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b))
    (Conductor.form_mul_invMon_mem y c' (SectionBounded.homog_chartMon i0 e))) ?_
  exact hcond c _ hx

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsRegular
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

theorem ConstantsRegular.proof (hD : ConstantsDescend.Statement)
    (hC : ChartConstantsDetermined.Statement) : ConstantsRegular.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y hy
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hfin : Module.Finite ℤ (intsIn F Ω) :=
    Module.Finite.of_surjective
      ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.rangeRestrict.toLinearMap
      (AlgHom.rangeRestrict_surjective _)
  have key : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ t ∈ intsIn F Ω, (m : Ω) * t ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · have hfg : (chartRingZ y c).FG :=
        ⟨Finset.univ.image fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩, by
          simp [chartRingZ, Set.image_univ]⟩
      obtain ⟨m, hm, h⟩ := hD Ω (chartRingZ y c) (intsIn F Ω) hfg hfin (hC K ι Ω F y hy c hc)
      exact ⟨m, hm, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hc⟩
  choose m hm hmem using key
  refine ⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
    fun c _ => Nat.one_le_iff_ne_zero.mp (hm c)), ?_⟩
  intro θ c hc
  have ht : algebraMap F Ω (θ : F) ∈ intsIn F Ω := (AlgHom.mem_range _).mpr ⟨θ, rfl⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), Nat.cast_mul, mul_assoc]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hmem c hc _ ht)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFrameChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace FrameChange

section Matrices

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem matAct_matAct (A A' : Matrix J J ℚ) (x : J → Ω) : matAct A (matAct A' x) = matAct (A * A') x := by
  funext i
  simp only [matAct, Matrix.mul_apply, Rat.cast_sum, Rat.cast_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem isInvMat_mul {A A' : Matrix J J ℚ} (hA : IsInvMat A) (hA' : IsInvMat A') : IsInvMat (A * A') := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨C', hC'⟩ := hA'
  refine ⟨C' * C, fun v => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC' (C.mulVec v)).1, (hC v).1]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hC (A'.mulVec v)).2, (hC' v).2]


open Classical in
def scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) : Matrix J J ℚ :=
  Matrix.diagonal fun i => if i ∈ Set.range e then 1 else (m : ℚ)


open Classical in
theorem matAct_scaleMat {D : ℕ} (e : Fin (D + 1) → J) (m : ℕ) (y : J → Ω) :
    matAct (scaleMat e m) y = scaleOff e m y := by
  funext i
  simp only [matAct, scaleMat, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  rw [if_pos rfl]
  unfold scaleOff
  split_ifs <;> simp


open Classical in
theorem isInvMat_scaleMat {D : ℕ} (e : Fin (D + 1) → J) {m : ℕ} (hm : 0 < m) : IsInvMat (scaleMat e m) := by
  have hc : ∀ i, (if i ∈ Set.range e then 1 else (m : ℚ)) ≠ 0 := fun i => by
    split_ifs
    · exact one_ne_zero
    · exact_mod_cast hm.ne'
  refine ⟨Matrix.diagonal fun i => (if i ∈ Set.range e then 1 else (m : ℚ))⁻¹, fun v => ⟨?_, ?_⟩⟩
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, mul_inv_cancel₀ (hc i), one_mul]
  · funext i
    simp only [scaleMat, Matrix.mulVec_diagonal]
    rw [← mul_assoc, inv_mul_cancel₀ (hc i), one_mul]

end Matrices

theorem proof (hN : RatNoetherFrame.Statement) (hT : HSMTransport.Statement) (hI : ResChiIndex.Statement) :
    FrameChange.Statement := by
  intro D Ω _ _ κ _ d
  obtain ⟨B₀, e, hB₀, hfr⟩ := hN D Ω κ d.x d.arith
  obtain ⟨m, hm, hfr'⟩ := exists_scaleOff_isProjFrame (matAct B₀ d.x) e hfr
  have hB : IsInvMat (scaleMat e m * B₀) := isInvMat_mul (isInvMat_scaleMat e hm) hB₀
  obtain ⟨d', hx', hm', hG⟩ := hT D Ω κ d _ hB
  have hx'' : d'.x = scaleOff e m (matAct B₀ d.x) := by
    rw [hx', ← matAct_matAct, matAct_scaleMat]
  refine ⟨_, d', e, hB, hx', hm', by rw [hx'']; exact hfr', ?_⟩
  have h0 := hI D Ω κ d d' _ hB hx' hG
  have hz : (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) = fun _ => (0 : ℝ) :=
    funext fun n => by rw [h0 n, sub_self]
  rw [hz]
  exact isLittleO_zero _ _

end FrameChange

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreSectionLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def FibreSectionLift.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D p : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime →
    Subsingleton (KH.cechHc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) a 1) →
    ∀ z ∈ KH.cechZc ι (KH.quotPart (ZMod p) (fibreIdeal p y)) a 0,
      ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch (y := y) (S := ZMod p) s a = z

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

