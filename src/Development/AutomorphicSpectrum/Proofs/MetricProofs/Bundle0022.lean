module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0020
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalRegularizationGradientBound
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

lemma near_small (a c K' : ℝ) :
    ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ t, 0 < t → t ≤ t₁ →
      c * (Real.log (1 / t) + K') ^ a * t ^ ((1 : ℝ) / 2) ≤ t ^ ((1 : ℝ) / 3) / 2 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero a (1 / 6 : ℝ) (by norm_num)
  have h2 : Tendsto (fun y : ℝ => (c * Real.exp (K' / 6)) * (y ^ a * Real.exp (-(1 / 6) * y)))
      atTop (nhds 0) := by
    simpa [neg_mul] using h.const_mul (c * Real.exp (K' / 6))
  have h3 := h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨Y, hY⟩ := eventually_atTop.1 h3
  refine ⟨Real.exp (K' - Y), Real.exp_pos _, fun t ht htle => ?_⟩
  set y := Real.log (1 / t) + K' with hy
  have hlog : Real.log t = K' - y := by
    rw [hy, one_div, Real.log_inv]; ring
  have hYy : Y ≤ y := by
    have := Real.log_le_log ht htle
    rw [Real.log_exp, hlog] at this
    linarith
  have hs := (hY y hYy).le
  have e1 : t ^ ((1 : ℝ) / 2) =
      t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y)) := by
    have : Real.exp (K' / 6) * Real.exp (-(1 / 6) * y) = t ^ ((1 : ℝ) / 6) := by
      rw [← Real.exp_add, Real.rpow_def_of_pos ht, hlog]; congr 1; ring
    rw [this, ← Real.rpow_add ht]; norm_num
  have hp : 0 < t ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos ht _
  rw [e1]
  calc c * y ^ a * (t ^ ((1 : ℝ) / 3) * (Real.exp (K' / 6) * Real.exp (-(1 / 6) * y)))
      = t ^ ((1 : ℝ) / 3) * (c * Real.exp (K' / 6) * (y ^ a * Real.exp (-(1 / 6) * y))) := by ring
    _ ≤ t ^ ((1 : ℝ) / 3) * (1 / 2) := mul_le_mul_of_nonneg_left hs hp.le
    _ = t ^ ((1 : ℝ) / 3) / 2 := by ring

theorem polyMaxOff_le_of_rLoc_le :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ K : ℝ), (∀ i ∈ S, 1 ≤ m i) → DifferentiableOn ℝ u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, ‖fderiv ℝ u z‖ ≤ C₅ * rLoc S m z ^ C₅ * Real.exp (rLoc S m z / 2)) → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ → ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, rLoc S m z ≤ Real.log (1 / t) + K → polyMaxOff S u z t ≤ u z + t ^ ((1 : ℝ) / 3) / 2 := by
  intro D S m u C₅ K hm hd hg
  have hclosed : IsClosed (ReciprocityTheory.AnForm.A.coordDiv S) := by
    have : ReciprocityTheory.AnForm.A.coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
      ext z; simp [ReciprocityTheory.AnForm.A.coordDiv]
    rw [this]
    exact S.finite_toSet.isClosed_biUnion
      (fun i _ => isClosed_eq (continuous_apply i) continuous_const)
  have hopen : IsOpen (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) :=
    isOpen_ball.sdiff hclosed
  set a := |C₅| with ha
  set K' := K + RegularChartScaling.mTot S m * Real.log 4 with hK'
  obtain ⟨t₁, ht₁, hsm⟩ := near_small a (a * Real.exp (K' / 2)) K'
  refine ⟨min (min (1 / 4) (Real.exp (-K))) t₁, by positivity, fun t ht htle z hz hr => ?_⟩
  have ht4 : t ≤ 1 / 4 := htle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have htK : t ≤ Real.exp (-K) := htle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have ht1 : t ≤ t₁ := htle.trans (min_le_right _ _)
  obtain ⟨hzB, hzD⟩ := hz
  have hzn : ∀ i, ‖z i‖ ≤ 2 :=
    RegularChartScaling.norm_coord_le_of_ball (by norm_num : (5 / 4 : ℝ) ≤ 2) hzB
  have hzi : ∀ i ∈ S, z i ≠ 0 := fun i hi h0 => hzD ⟨i, hi, h0⟩
  have hcoord : ∀ i ∈ S, 2 * t ≤ ‖z i‖ := by
    intro i hi
    have hpos : 0 < ‖z i‖ := norm_pos_iff.2 (hzi i hi)
    have hterm : Real.log (4 / ‖z i‖ ^ 2) ≤ Real.log (1 / t) + K := by
      have h1 : (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) ≤
          ∑ j ∈ S, (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2) :=
        Finset.single_le_sum (f := fun j => (m j : ℝ) * Real.log (4 / ‖z j‖ ^ 2))
          (fun j _ => mul_nonneg (Nat.cast_nonneg _) (RegularChartScaling.log_term_nonneg (hzn j))) hi
      have h2 : Real.log (4 / ‖z i‖ ^ 2) ≤ (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) :=
        le_mul_of_one_le_left (RegularChartScaling.log_term_nonneg (hzn i)) (by exact_mod_cast hm i hi)
      have h3 := Real.exp_pos 1
      unfold rLoc at hr
      linarith
    have hEK : Real.exp K ≤ 1 / t := by
      rw [Real.exp_neg] at htK
      rw [le_div_iff₀ ht]
      have := mul_le_mul_of_nonneg_left htK (Real.exp_pos K).le
      rwa [mul_inv_cancel₀ (Real.exp_pos K).ne'] at this
    have hE : Real.exp (Real.log (1 / t) + K) ≤ 1 / t ^ 2 := by
      rw [Real.exp_add, Real.exp_log (by positivity)]
      calc 1 / t * Real.exp K ≤ 1 / t * (1 / t) :=
            mul_le_mul_of_nonneg_left hEK (by positivity)
        _ = 1 / t ^ 2 := by field_simp
    have h4 : 4 / ‖z i‖ ^ 2 ≤ 1 / t ^ 2 :=
      ((Real.log_le_iff_le_exp (by positivity)).1 hterm).trans hE
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h4
    by_contra hlt
    push_neg at hlt
    nlinarith
  set y := Real.log (1 / t) + K' with hy
  have hfar : ∀ x ∈ closedBall z t, ∀ i ∈ S, ‖z i‖ / 2 ≤ ‖x i‖ ∧ 0 < ‖x i‖ := by
    intro x hx i hi
    have h1 : ‖x i - z i‖ ≤ t :=
      (norm_le_pi_norm (x - z) i).trans (mem_closedBall_iff_norm.1 hx)
    have h2 := norm_sub_norm_le (z i) (x i)
    rw [norm_sub_rev] at h2
    have h3 := hcoord i hi
    constructor <;> linarith
  have hmem : ∀ x ∈ closedBall z t,
      x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S := by
    intro x hx
    refine ⟨RegularChartScaling.closedBall_sub_of hzB (by linarith) hx, ?_⟩
    rintro ⟨i, hi, h0⟩
    have := (hfar x hx i hi).2
    rw [h0, norm_zero] at this
    exact lt_irrefl _ this
  have hrx : ∀ x ∈ closedBall z t, rLoc S m x ≤ y := by
    intro x hx
    have key : ∀ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤
        (m i : ℝ) * Real.log (4 / ‖z i‖ ^ 2) + (m i : ℝ) * Real.log 4 := by
      intro i hi
      obtain ⟨h1, h2⟩ := hfar x hx i hi
      have hzp : 0 < ‖z i‖ := norm_pos_iff.2 (hzi i hi)
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      rw [← Real.log_mul (by positivity) (by norm_num)]
      refine Real.log_le_log (by positivity) ?_
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_self_le_mul_self (by positivity) h1]
    have hsum := Finset.sum_le_sum key
    rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
    unfold rLoc at hr ⊢
    simp only [hy, hK', RegularChartScaling.mTot]
    linarith
  set B := a * y ^ a * Real.exp (y / 2) with hB
  have hfd : ∀ x ∈ closedBall z t, ‖fderiv ℝ u x‖ ≤ B := by
    intro x hx
    have hxm := hmem x hx
    have hxn : ∀ i, ‖x i‖ ≤ 2 :=
      RegularChartScaling.norm_coord_le_of_ball (by norm_num : (3 / 2 : ℝ) ≤ 2) hxm.1
    have hr1 : 1 ≤ rLoc S m x := by
      have := RegularChartScaling.rLoc_ge S m hxn
      linarith [Real.add_one_le_exp (1 : ℝ)]
    have hry := hrx x hx
    have hy0 : 0 ≤ y := by linarith
    have hp : rLoc S m x ^ C₅ ≤ y ^ a :=
      (Real.rpow_le_rpow_of_exponent_le hr1 (le_abs_self C₅)).trans
        (Real.rpow_le_rpow (by linarith) hry (abs_nonneg _))
    refine (hg x hxm).trans ?_
    refine mul_le_mul (mul_le_mul (le_abs_self C₅) hp (Real.rpow_nonneg (by linarith) _)
      (abs_nonneg _)) (Real.exp_le_exp.2 (by linarith)) (Real.exp_pos _).le
      (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hy0 _))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hfd z (mem_closedBall_self ht.le))
  have hBt : B * t ≤ t ^ ((1 : ℝ) / 3) / 2 := by
    have hlog : Real.log t = K' - y := by
      rw [hy, one_div, Real.log_inv]; ring
    have e : Real.exp (y / 2) * t = Real.exp (K' / 2) * t ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos ht, hlog]
      nth_rewrite 1 [← Real.exp_log ht]
      rw [hlog, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    calc B * t = a * y ^ a * (Real.exp (y / 2) * t) := by rw [hB]; ring
      _ = a * Real.exp (K' / 2) * y ^ a * t ^ ((1 : ℝ) / 2) := by rw [e]; ring
      _ ≤ t ^ ((1 : ℝ) / 3) / 2 := hsm t ht ht1
  unfold polyMaxOff
  refine csSup_le ⟨u z, z, ⟨mem_closedBall_self ht.le, hzD⟩, rfl⟩ ?_
  rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := u) (s := closedBall z t)
    (x := z) (y := x) (C := B)
    (fun w hw => (hd w (hmem w hw)).differentiableAt (hopen.mem_nhds (hmem w hw)))
    hfd (convex_closedBall z t) (mem_closedBall_self ht.le) hx
  have h1 : ‖x - z‖ ≤ t := mem_closedBall_iff_norm.1 hx
  have h2 : u x - u z ≤ ‖u x - u z‖ := Real.le_norm_self _
  have h3 : B * ‖x - z‖ ≤ B * t := mul_le_mul_of_nonneg_left h1 hB0
  linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBoundTransferBetweenRadii
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.BoundConv

theorem bound_conv_local (C₅ M : ℝ) : ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) := by
  set A := |C₅| with hA
  set M' := |M| with hM'
  have hA0 : 0 ≤ A := abs_nonneg _
  have hM0 : 0 ≤ M' := abs_nonneg _
  have hB1 : 1 ≤ (1 + M') ^ A := Real.one_le_rpow (by linarith) hA0
  have hE1 : 1 + M' ≤ Real.exp M' := by linarith [Real.add_one_le_exp M']
  have hE1' : 1 ≤ Real.exp M' := Real.one_le_exp hM0
  set K := A * (1 + M') ^ A * Real.exp M' with hK
  have hK0 : 0 ≤ K := by positivity
  have hKA : A ≤ K := by
    have : A * 1 * 1 ≤ A * (1 + M') ^ A * Real.exp M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1' (by norm_num) (by positivity)
    simpa using this
  have hKA' : A * (1 + M') ≤ K := by
    have : A * 1 * (1 + M') ≤ A * (1 + M') ^ A * Real.exp M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1 (by linarith) (by positivity)
    simpa using this
  refine ⟨K, hK0, ?_⟩
  intro x y p d hx hy hxy
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hy1 : 1 ≤ y := le_trans he1 hy
  have hx1 : 1 ≤ x := le_trans he1 hx
  have hlogy : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hy
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hx
  have hxle : x ≤ y + M' := by
    have := (abs_le.mp (le_trans hxy (le_abs_self M))).2
    linarith
  have hxle2 : x ≤ y * (1 + M') := by nlinarith
  constructor
  · intro hp1 hp2
    refine ⟨?_, le_trans hp2 (le_trans (le_abs_self C₅) hKA)⟩
    rcases le_or_gt C₅ 0 with hC | hC
    · have h1 : 0 ≤ -C₅ * Real.log x := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ K * Real.log y := mul_nonneg hK0 (by linarith)
      linarith
    · have hAC : A = C₅ := abs_of_pos hC
      have hl1 : Real.log x ≤ Real.log (y * (1 + M')) := Real.log_le_log (by linarith) hxle2
      rw [Real.log_mul (by linarith) (by linarith)] at hl1
      have hl2 : Real.log (1 + M') ≤ M' := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + M' by linarith); linarith
      have hl3 : Real.log x ≤ Real.log y * (1 + M') := by nlinarith
      have hl4 : C₅ * Real.log x ≤ C₅ * (1 + M') * Real.log y := by
        have := mul_le_mul_of_nonneg_left hl3 hC.le; linarith
      have hl5 : C₅ * (1 + M') * Real.log y ≤ K * Real.log y :=
        mul_le_mul_of_nonneg_right (by rw [← hAC]; exact hKA') (by linarith)
      linarith
  · intro hd
    have h1 : x ^ A ≤ (y * (1 + M')) ^ A := Real.rpow_le_rpow (by linarith) hxle2 hA0
    rw [Real.mul_rpow (by linarith) (by linarith)] at h1
    have h2 : Real.exp (x / 2) ≤ Real.exp (y / 2) * Real.exp M' := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have h3 : y ^ A ≤ y ^ K := Real.rpow_le_rpow_of_exponent_le hy1 hKA
    have hxA : 0 ≤ x ^ A := Real.rpow_nonneg (by linarith) _
    have hyK : 0 ≤ y ^ K := Real.rpow_nonneg (by linarith) _
    have hB0 : 0 ≤ (1 + M') ^ A := by linarith
    calc d ≤ A * x ^ A * Real.exp (x / 2) := hd
      _ ≤ A * (y ^ A * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hA0) h2 (Real.exp_pos _).le
          positivity
      _ ≤ A * (y ^ K * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hB0) hA0
      _ = K * y ^ K * Real.exp (y / 2) := by rw [hK]; ring

theorem bound_conv : ∀ (C₅ M : ℝ), ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) :=
  bound_conv_local

end GlobalTheory.CompanionTheory.Metric.BoundConv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansionStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_integral_multilinear_expansion : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (σ : Type) [Fintype σ] (U : Set X) (P : σ → LocPot X) (c : Fin e → σ → ℝ) (g : X → ℝ), IsNull A Uᶜ → (∀ a, ∀ x ∈ U, IsTwiceDifferentiableAt A (P a) x) → (∀ w : Fin e → σ, MIntegrable A (fun i => P (w i)) g) → MIntegrable A (fun i => sumPot (c i) P) g ∧ mInt A (fun i => sumPot (c i) P) g = ∑ w : Fin e → σ, (∏ i, c i (w i)) * mInt A (fun i => P (w i)) g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.mInt_sumPot_expand | exact GlobalTheory.CompanionTheory.Ar.PB.mInt_sumPot_expand | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.mInt_sumPot_expand <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizationGlueBounds
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.RegFin

theorem isPsh_of_posPot {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (h : IsPosPot A Θ) : IsPsh A Θ := by
  intro x j y hy w
  by_cases hw : w = 0
  · subst hw; rw [levi_zero]
  · exact (h x j y hy w hw).le

theorem quot_mem_unit {t : ℝ} (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    0 ≤ Real.log (Real.log (1 / t)) / Real.log (1 / t) ∧
      Real.log (Real.log (1 / t)) / Real.log (1 / t) ≤ 1 := by
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  have hl : 0 < Real.log (1 / t) := lt_of_lt_of_le (Real.exp_pos 1) h1
  refine ⟨div_nonneg (by linarith) hl.le, ?_⟩
  rw [div_le_one hl]
  have := Real.log_le_sub_one_of_pos hl
  linarith

theorem quot_mono {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t') (hte : t' ≤ Real.exp (-Real.exp 1)) :
    Real.log (Real.log (1 / t)) / Real.log (1 / t) ≤
      Real.log (Real.log (1 / t')) / Real.log (1 / t') := by
  have ht' := ht.trans_le htt
  have h1 := (GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht' hte).1
  have hle : Real.log (1 / t') ≤ Real.log (1 / t) :=
    Real.log_le_log (by positivity) (one_div_le_one_div_of_le ht htt)
  exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 h1) (Set.mem_Ici.2 (h1.trans hle)) hle

theorem isRegFamily_of_glue : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (Θ L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ K Cl t₀ : ℝ) (f : ℝ → Fin B.n → X → ℝ) (F : ℝ → X → ℝ), IsPotential A Θ → IsPosPot A Θ → IsPotential A th → (∀ y, logNormSec L s y ≤ 0) → (∀ y, ∃ j, y ∈ chartBall B j 1) → (∀ y ∉ bdry s, -C₅ * Real.log (rW L s y) ≤ ph y) → 0 < K → 1 ≤ Cl → 0 < t₀ → t₀ ≤ Real.exp (-Real.exp 1) → (∀ t, 0 < t → t ≤ t₀ → A.Smooth (F t) ∧ IsPsh A (th + LocPot.ofFun (F t) + Θ.rsmul (K * epsT Cl t)) ∧ ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ F t y ∧ F t y ≤ f t j y + K * epsT Cl t) → (∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ f t j y ∧ (y ∉ bdry s → ph y ≤ f t j y ∧ (rW L s y ≤ Real.log (1 / t) → f t j y ≤ ph y + t ^ ((1 : ℝ) / 3)))) → (∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B j (5 / 4), f t j y ≤ f t' j y + epsT Cl t') → ∃ C : ℝ, IsRegFamily A Θ L s th ph F C t₀ := by
  intro e X _ A B Θ L th s ph C₅ K Cl t₀ f F hΘ hΘp hth hs hcov hph hK hCl ht₀ ht₀e hF hf hmono
  have hΘpsh := isPsh_of_posPot A Θ hΘp
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Cl * (1 + K) + |C₅| + 1 := ⟨_, rfl⟩
  have hC5 := abs_nonneg C₅
  have hClK : 0 ≤ Cl * K := by positivity
  have hC1 : 1 ≤ C := by nlinarith
  have hCK : Cl * (1 + K) ≤ C := by linarith
  have hCl' : Cl ≤ C := by nlinarith
  have hKCl : K * Cl ≤ C := by nlinarith
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpt : ∀ y, ∃ j, y ∈ chartBall B j (5 / 4) := fun y => by
    obtain ⟨j, hj⟩ := hcov y
    exact ⟨j, chartBall_mono B j (by norm_num) hj⟩
  have ht₀1 : t₀ < 1 :=
    lt_of_le_of_lt ht₀e (by
      have := Real.exp_lt_exp.2 (show -Real.exp 1 < 0 by linarith [Real.exp_pos 1])
      rwa [Real.exp_zero] at this)
  refine ⟨C, ht₀, ht₀1, fun t ht htt => ?_⟩
  have hte := htt.trans ht₀e
  obtain ⟨hl1, hll⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  obtain ⟨hg0, hg1⟩ := quot_mem_unit ht hte
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = Real.log (Real.log (1 / t)) / Real.log (1 / t) := ⟨_, rfl⟩
  rw [← hgdef] at hg0 hg1
  have hεC : epsT C t = C * g := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef]
  have hεl : epsT Cl t = Cl * g := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef]
  obtain ⟨hsm, hpsh, hFf⟩ := hF t ht htt
  have hKg : K * (Cl * g) ≤ K * Cl := by
    have := mul_le_mul_of_nonneg_left hg1 (by linarith : (0 : ℝ) ≤ Cl)
    nlinarith
  have hKg0 : 0 ≤ K * (Cl * g) := by positivity
  have hFC : ∀ y, F t y ≤ Cl * (1 + K) := fun y => by
    obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := (hf t ht htt j y hj).1
    rw [hεl] at h1
    nlinarith
  refine ⟨hsm, fun y => (hFC y).trans hCK, fun y hy => ?_, fun y => ?_, ?_,
    fun y hy hyr => ?_, fun y hy => ?_, fun t' htt' ht' y => ?_⟩
  · obtain ⟨j, hj⟩ := hpt y
    exact ((hf t ht htt j y hj).2.2 hy).1.trans (hFf j y hj).1
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).1
    have h2 := (hf t ht htt j y hj).2.1
    have : Cl * Real.log (Real.log (1 / t)) ≤ C * Real.log (Real.log (1 / t)) :=
      mul_le_mul_of_nonneg_right hCl' (by linarith)
    linarith
  · refine GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono A Θ th (F t) hΘ hΘpsh hth hsm ?_ hpsh
    rw [hεl, hεC]
    have := mul_le_mul_of_nonneg_right hKCl hg0
    nlinarith
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := ((hf t ht htt j y hj).2.2 hy).2 hyr
    rw [hεl] at h1
    rw [hεC]
    have := mul_le_mul_of_nonneg_right hKCl hg0
    nlinarith
  · obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have hfj := hf t ht htt j y hj
    rw [hεl] at h1
    rw [hεC]
    have hry := hr y
    have hrpos : 0 < rW L s y := by linarith
    have ht3 : 0 ≤ t ^ ((1 : ℝ) / 3) := by positivity
    have hCg0 : 0 ≤ C * g := by positivity
    by_cases hyr : rW L s y ≤ Real.log (1 / t)
    · have h2 := (hfj.2.2 hy).2 hyr
      have h3 : C * g ≤ C * g * rW L s y := le_mul_of_one_le_right hCg0 (by linarith)
      have := mul_le_mul_of_nonneg_right hKCl hg0
      nlinarith
    · push_neg at hyr
      have hlog : Real.log (rW L s y) / rW L s y ≤ g := by
        rw [hgdef]
        exact Real.log_div_self_antitoneOn (Set.mem_Ici.2 hl1) (Set.mem_Ici.2 hry) hyr.le
      have hlog' : Real.log (rW L s y) ≤ g * rW L s y := by
        rw [div_le_iff₀ hrpos] at hlog
        linarith
      have hlpos : 0 < Real.log (1 / t) := by linarith [Real.exp_pos 1]
      have hgr : 1 ≤ g * rW L s y := by
        have e1 : g * rW L s y = Real.log (Real.log (1 / t)) * (rW L s y / Real.log (1 / t)) := by
          rw [hgdef]; ring
        have e2 : 1 ≤ rW L s y / Real.log (1 / t) := by
          rw [le_div_iff₀ hlpos]; linarith
        rw [e1]
        nlinarith
      have hlr0 : 0 ≤ Real.log (rW L s y) := Real.log_nonneg (by linarith)
      have hph1 := hph y hy
      have hph2 : -|C₅| * Real.log (rW L s y) ≤ -C₅ * Real.log (rW L s y) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C₅]) hlr0
      have h4 : |C₅| * Real.log (rW L s y) ≤ |C₅| * (g * rW L s y) :=
        mul_le_mul_of_nonneg_left hlog' hC5
      have h5 : Cl * (1 + K) ≤ Cl * (1 + K) * (g * rW L s y) :=
        le_mul_of_one_le_right (by positivity) hgr
      have hCg : C * g * rW L s y = (Cl * (1 + K) + |C₅| + 1) * (g * rW L s y) := by
        rw [hCdef]; ring
      have := hFC y
      nlinarith
  · have ht'0 : 0 < t' := ht.trans_le htt'
    have hte' := ht'.trans ht₀e
    obtain ⟨hg0', hg1'⟩ := quot_mem_unit ht'0 hte'
    have hgm := quot_mono ht htt' hte'
    obtain ⟨g', hgdef'⟩ : ∃ g' : ℝ, g' = Real.log (Real.log (1 / t')) / Real.log (1 / t') :=
      ⟨_, rfl⟩
    rw [← hgdef'] at hg0' hg1'
    rw [← hgdef, ← hgdef'] at hgm
    have hεC' : epsT C t' = C * g' := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef']
    have hεl' : epsT Cl t' = Cl * g' := by rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, hgdef']
    obtain ⟨j, hj⟩ := hpt y
    have h1 := (hFf j y hj).2
    have h2 := hmono t t' ht htt' ht' j y hj
    have h3 := ((hF t' ht'0 ht').2.2 j y hj).1
    rw [hεl] at h1
    rw [hεl'] at h2
    rw [hεC']
    have h4 : K * (Cl * g) ≤ K * (Cl * g') :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgm (by linarith)) hK.le
    have h5 : Cl * (1 + K) * g' ≤ C * g' := mul_le_mul_of_nonneg_right hCK hg0'
    have h6 : C * g' ≤ C * (C * g') := le_mul_of_one_le_left (by positivity) hC1
    linarith

end GlobalTheory.CompanionTheory.Ar.RegFin
end

