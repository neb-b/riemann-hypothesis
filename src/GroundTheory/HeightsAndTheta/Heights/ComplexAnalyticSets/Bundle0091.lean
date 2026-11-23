module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormFullBranchConstant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

theorem monic_root_branch_eventuallyEq {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (s : Fin d → ℂ)
    (u v : (Fin d → ℂ) → ℂ) (ha : ∀ j, ContinuousAt (a j) s) (hu : ContinuousAt u s)
    (hv : ContinuousAt v s) (huv : u s = v s)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hru : ∀ᶠ t in 𝓝 s, u t ^ N + ∑ j, a j t * u t ^ (j : ℕ) = 0)
    (hrv : ∀ᶠ t in 𝓝 s, v t ^ N + ∑ j, a j t * v t ^ (j : ℕ) = 0) : u =ᶠ[𝓝 s] v := by
  set Q : (Fin d → ℂ) → ℂ → ℂ → ℂ := fun t x y =>
    ∑ i ∈ Finset.range N, x ^ i * y ^ (N - 1 - i) +
      ∑ j : Fin N, a j t * ∑ i ∈ Finset.range j, x ^ i * y ^ ((j : ℕ) - 1 - i) with hQdef
  have hQ : ∀ t x y, (x ^ N + ∑ j, a j t * x ^ (j : ℕ)) - (y ^ N + ∑ j, a j t * y ^ (j : ℕ)) =
      Q t x y * (x - y) := by
    intro t x y
    rw [hQdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hQs : Q s (u s) (u s) ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := u s)
      (by simpa [Polynomial.eval₂_id, Polynomial.eval_finsetSum] using hru.self_of_nhds)
    convert h using 1
    simp [hQdef, Polynomial.eval₂_id, Polynomial.eval_finsetSum, geom_sum₂_self, Polynomial.derivative_X_pow]
  have hc : ContinuousAt (fun t => Q t (u t) (v t)) s := by
    simp only [hQdef]
    fun_prop
  have hne : ∀ᶠ t in 𝓝 s, Q t (u t) (v t) ≠ 0 := hc.eventually_ne (by rw [← huv]; exact hQs)
  filter_upwards [hru, hrv, hne] with t h1 h2 h3
  have h := hQ t (u t) (v t)
  rw [h1, h2, sub_self] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h.symm).resolve_left h3)

theorem PrimitiveFormFullBranchConstant.proof : PrimitiveFormFullBranchConstant.Statement := by
  intro σ _ X W N' k f d A ℓ N a δ q B O r hW hN' hWN' hf hXN' hXW hP hB ha hδ hq hO hOc hOB hδO hsep hr hrO
  set G : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hGdef
  set P : (Fin d → ℂ) → Prop := fun u => G u ∈ X ∩ W ∧ A (G u) = u ∧ ℓ (G u) = r u with hPdef
  have hG : AnalyticOnNhd ℂ G O := fun u hu => analyticAt_pi_iff.2 fun i =>
    (Finset.analyticAt_fun_sum _ fun j _ => (hq i j u (hOB hu)).mul ((hr u hu).pow _)).div
      (hδ u (hOB hu)) (hδO u hu)

  have hfull : ∀ s ∈ O, (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ ∀ᶠ u in 𝓝 s, P u) := by
    intro s hs
    constructor
    · rintro ⟨O', r', hO', hsO', hr', hrs, hw⟩
      have hroot' : ∀ᶠ u in 𝓝 s, r' u ^ N + ∑ j, a j u * r' u ^ (j : ℕ) = 0 := by
        filter_upwards [hO'.mem_nhds hsO'] with u hu
        obtain ⟨hX, hA, hℓ⟩ := hw u hu
        have h := hP _ hX
        rwa [hA, hℓ] at h
      have heq : r' =ᶠ[𝓝 s] r := monic_root_branch_eventuallyEq a s r' r
        (fun j => (ha j s (hOB hs)).continuousAt) (hr' s hsO').continuousAt (hr s hs).continuousAt hrs
        (hsep s hs) hroot' (Filter.mem_of_superset (hO.mem_nhds hs) hrO)
      filter_upwards [hO'.mem_nhds hsO', heq] with u hu hru
      have h := hw u hu
      simp only [hru] at h
      exact h
    · intro hev
      obtain ⟨U, hUs, hUo, hsU⟩ := mem_nhds_iff.1 hev
      exact ⟨U ∩ O, r, hUo.inter hO, ⟨hsU, hs⟩, hr.mono Set.inter_subset_right, rfl, fun u hu => hUs hu.1⟩

  set S : Set (Fin d → ℂ) := {s | ∀ᶠ u in 𝓝 s, P u} with hSdef
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hSc : closure S ∩ O ⊆ S := by
    rintro s ⟨hsc, hs⟩
    have hGs : ContinuousAt G s := (hG s hs).continuousAt
    have hGW : G s ∈ closure W := closure_mono (by rintro _ ⟨u, hu, rfl⟩; exact hu.self_of_nhds.1.2)
      (mem_closure_image hGs hsc)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
      (Filter.inter_mem (hO.mem_nhds hs) (hGs.preimage_mem_nhds (hN'.mem_nhds (hWN' hGW))))

    set Φ : (Fin d → ℂ) → (Fin k → ℂ) × (Fin d → ℂ) × ℂ :=
      fun u => (fun i => f i (G u), A (G u) - u, ℓ (G u) - r u) with hΦdef
    have hΦ : AnalyticOnNhd ℂ Φ (Metric.ball s ε) := fun u hu => by
      have hu' := hball hu
      exact (analyticAt_pi_iff.2 fun i => (hf i _ hu'.2).comp (hG u hu'.1)).prod
        ((((A.analyticAt _).comp (hG u hu'.1)).sub analyticAt_id).prod
          (((ℓ.analyticAt _).comp (hG u hu'.1)).sub (hr u hu'.1)))
    obtain ⟨u₀, hu₀U, hu₀S⟩ := mem_closure_iff.1 hsc _ Metric.isOpen_ball (Metric.mem_ball_self hε)
    have hΦ0 : Set.EqOn Φ 0 (Metric.ball s ε) :=
      hΦ.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball s ε).isPreconnected hu₀U (by
        filter_upwards [hu₀S] with u hu
        obtain ⟨⟨hX, hWu⟩, hA, hℓ⟩ := hu
        have hXN : G u ∈ X ∩ N' := ⟨hX, hWN' (subset_closure hWu)⟩
        rw [hXN'] at hXN
        simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, hA, hℓ, sub_self, and_true]
        exact funext fun i => hXN.2 i)
    have hU : ∀ u ∈ Metric.ball s ε, G u ∈ X ∧ A (G u) = u ∧ ℓ (G u) = r u := by
      intro u hu
      have h := hΦ0 hu
      simp only [hΦdef, Pi.zero_apply, Prod.mk_eq_zero, sub_eq_zero] at h
      refine ⟨?_, h.2.1, h.2.2⟩
      have hXN : G u ∈ X ∩ N' := by rw [hXN']; exact ⟨(hball hu).2, fun i => congr_fun h.1 i⟩
      exact hXN.1
    obtain ⟨hXs, hAs, -⟩ := hU s (Metric.mem_ball_self hε)
    have hGsW : G s ∈ W := hXW _ ⟨hXs, hGW⟩ (by rw [hAs]; exact hOB hs)
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε),
      hGs.preimage_mem_nhds (hW.mem_nhds hGsW)] with u hu hu'
    obtain ⟨h1, h2, h3⟩ := hU u hu
    exact ⟨⟨h1, hu'⟩, h2, h3⟩

  have key : ∀ s ∈ O, ∀ s' ∈ O, PrimitiveFormRootFull X W A ℓ δ q s (r s) →
      PrimitiveFormRootFull X W A ℓ δ q s' (r s') := by
    intro s hs s' hs' h
    have hsub : O ⊆ S := hOc.subset_of_closure_inter_subset hSo ⟨s, hs, (hfull s hs).1 h⟩ hSc
    exact (hfull s' hs').2 (hsub hs')
  intro s hs s' hs'
  exact ⟨key s hs s' hs', key s' hs' s hs⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormSheetedLocusCutOut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem PrimitiveFormSheetedLocusCutOut.proof (hfac : PrimitiveFormFullRootFactor.Statement)
    (hiff : PrimitiveFormSheetedIffRootFull.Statement) : PrimitiveFormSheetedLocusCutOut.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  obtain ⟨W, B, C, E, hW, hwW, hB, hwB, han, hCE, hroot⟩ :=
    hfac σ X w d A hX hiso ℓ N a δ q ha hδ hq hδ0 hP hsep hQ
  have hBn : ∀ᶠ z in 𝓝 w, A z ∈ B := A.continuous.continuousAt.preimage_mem_nhds (hB.mem_nhds hwB)
  have hc : ∀ F : (Fin d → ℂ) → ℂ → ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F u.1 u.2) (A w, ℓ w) →
      AnalyticAt ℂ (fun z => F (A z) (ℓ z)) w := fun F hF =>
    (show AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => F u.1 u.2) ((A.prod ℓ) w) from hF).comp
      ((A.prod ℓ).analyticAt w)
  refine ⟨fun z => C (A z) (ℓ z), fun z => E (A z) (ℓ z), hc C (han _ hwB _).1, hc E (han _ hwB _).2, ?_, ?_⟩
  · filter_upwards [hBn, hP] with z hz hPz hzX
    rw [hCE _ hz]
    exact hPz hzX
  · filter_upwards [hBn, hP, hiff σ X w d A ℓ N a δ q ha hδ hq hP hsep hQ, hW.mem_nhds hwW] with
      z hz hPz hsh hzW hzX hzδ
    have hr := hroot _ hz hzδ (ℓ z) (hPz hzX)
    have hs := hsh hzX hzδ W hW hzW
    exact ⟨hs.trans hr.1.symm, fun h h0 => hr.2.mp h0 (hs.mp h)⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegBallMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegBallMass

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_indicator_mono (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S S' : Set (Fin n → ℂ)} (hS : S ⊆ S') (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ∧
      chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ≤
        chartDens J A (S'.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  have key : ∀ x ∈ fibre J A y, ∀ h : ∃ s, IsSheetAt J A x s,
      0 ≤ ReciprocityTheory.AnForm.maDens (fun k => (vecCons (logReg u ε) fun _ => euclPot :
        Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ h.choose) y := by
    intro x hx h
    have := hN n d J A u ε x h.choose hε h.choose_spec
    rwa [hx.2] at this
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  constructor
  · refine Finset.sum_nonneg fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (key x hx h)
    · exact le_rfl
  · refine Finset.sum_le_sum fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right
        (Set.indicator_le_indicator_of_subset hS (fun _ => zero_le_one) x) (key x hx h)
    · exact le_rfl

theorem measurable_chartDens_indicator (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) :
    Measurable (chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot)) := by
  refine (SheetSumMeasurable.proof n (d + 1) J A _ _ hJ hdim hA (measurable_const.indicator hS)
    fun k => ?_).1
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_euclPot n)

end RegBallMass


open RegBallMass in
theorem RegBallMass.proof (hF : RegFixedBallMass.Statement) (hM : RegLelongMono.Statement)
    (hN : RegDensNonneg.Statement) : RegBallMass.Statement := by
  intro n d J A u K hJ hdim hA hu hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set c : ℝ := Real.sqrt (n + 1) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  obtain ⟨M, hMb⟩ := hF n d J A u (R₀ + c) hJ hdim hA hu
  refine ⟨max M 0, le_max_right _ _, fun ε hε x hx r hr => ?_⟩
  set F : Set (Fin n → ℂ) → (Fin (d + 1) → ℂ) → ℝ := fun S =>
    chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) with hFdef
  have h1 : Metric.ball x r ⊆ euclBall x (c * r) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr.1] at hy
    show Real.sqrt (euclPot (y - x)) < c * r
    rw [Real.sqrt_lt' (mul_pos hc0 hr.1), mul_pow, hc2]
    calc euclPot (y - x) = ∑ j, ‖(y - x) j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin n, r ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hy j).le 2
      _ = n * r ^ 2 := by simp
      _ < (n + 1) * r ^ 2 := by nlinarith [pow_pos hr.1 2]
  have h2 : euclBall x c ⊆ Metric.closedBall 0 (R₀ + c) := by
    intro y hy
    have hy' : euclPot (y - x) < c ^ 2 := (Real.sqrt_lt' hc0).1 hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hyx : ‖y - x‖ ≤ c := by
      refine (pi_norm_le_iff_of_nonneg hc0.le).2 fun j => ?_
      have hj : ‖(y - x) j‖ ^ 2 ≤ euclPot (y - x) :=
        Finset.single_le_sum (f := fun j => ‖(y - x) j‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc0.le two_ne_zero).1 (by linarith)
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ R₀ + c := add_le_add (hR₀ x hx) hyx
  have h3 : euclBall x (c * r) ⊆ euclBall x c := fun y hy =>
    show Real.sqrt (euclPot (y - x)) < c from
      lt_of_lt_of_le (show Real.sqrt (euclPot (y - x)) < c * r from hy)
        (mul_le_of_le_one_right hc0.le hr.2)
  have hpos : ∀ {S S' : Set (Fin n → ℂ)}, S ⊆ S' → ∀ y, 0 ≤ F S y ∧ F S y ≤ F S' y :=
    fun hS y => chartDens_indicator_mono hN hA u hε.1 hS y
  have hEm : ∀ ρ, MeasurableSet (euclBall x ρ) := fun ρ =>
    (isOpen_lt (((contDiff_euclPot n).continuous.comp
      (continuous_id.sub continuous_const)).sqrt) continuous_const).measurableSet
  obtain ⟨hIR, hIRle⟩ := hMb ε hε
  have hint : ∀ S, MeasurableSet S → S ⊆ Metric.closedBall 0 (R₀ + c) → Integrable (F S) :=
    fun S hS hSR => hIR.mono' (measurable_chartDens_indicator hJ hdim hA u hε.1 hS).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpos hSR y).1]; exact (hpos hSR y).2)
  have hBI := hint _ Metric.isOpen_ball.measurableSet (h1.trans (h3.trans h2))
  refine ⟨hBI, ?_⟩
  have hmono := hM n d J A u ε x (c * r) c hJ hdim hA hε.1 (mul_pos hc0 hr.1)
    (mul_le_of_le_one_right hc0.le hr.2)
  have hI1 : ∫ y, F (Metric.ball x r) y ≤ ∫ y, F (euclBall x (c * r)) y :=
    integral_mono hBI (hint _ (hEm _) (h3.trans h2)) fun y => (hpos h1 y).2
  have hI2 : ∫ y, F (euclBall x c) y ≤ ∫ y, F (Metric.closedBall 0 (R₀ + c)) y :=
    integral_mono (hint _ (hEm _) h2) hIR fun y => (hpos h2 y).2
  have hI3 : ∫ y, F (euclBall x (c * r)) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := by
    have : c ^ (2 * d) * ∫ y, F (euclBall x (c * r)) y ≤
        c ^ (2 * d) * (r ^ (2 * d) * ∫ y, F (euclBall x c) y) := by
      rw [← mul_assoc, ← mul_pow]; exact hmono
    exact le_of_mul_le_mul_left this (pow_pos hc0 _)
  calc ∫ y, F (Metric.ball x r) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := hI1.trans hI3
    _ ≤ r ^ (2 * d) * max M 0 :=
      mul_le_mul_of_nonneg_left (hI2.trans (hIRle.trans (le_max_left _ _))) (pow_nonneg hr.1.le _)
    _ = max M 0 * r ^ (2 * d) := mul_comm _ _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegLelongMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegLelongMono

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_annulus_nonneg (hL : RegLogDensNonneg.Statement) (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (x : Fin n → ℂ) {r s : ℝ} (hr : 0 < r) (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => logDistSq x) y := by
  unfold chartDens sheetSum
  refine finsum_nonneg fun z => finsum_nonneg fun hz => ?_
  split_ifs with h
  · beta_reduce
    by_cases hza : z ∈ euclBall x s \ euclBall x r
    · rw [Set.indicator_of_mem hza, one_mul]
      have := hL n d J A u ε x z h.choose hε (ne_of_mem_euclBall_diff hr hza) h.choose_spec
      rwa [hz.2] at this
    · rw [Set.indicator_of_notMem hza, zero_mul]
  · exact le_rfl

end RegLelongMono


open RegLelongMono in
theorem RegLelongMono.proof (hA : RegLelongAnnulus.Statement) (hL : RegLogDensNonneg.Statement) :
    RegLelongMono.Statement := by
  intro n d J A u ε x r s hJ hdim hAf hε hr hrs
  have heq := hA n d J A u ε x r s hJ hdim hAf hε hr hrs
  have hτ : 0 ≤ ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
      (vecCons (logReg u ε) fun _ => logDistSq x) y :=
    integral_nonneg fun y => chartDens_annulus_nonneg hL u hε x hr y
  have hrs0 : 0 ≤ r ^ (2 * d) * s ^ (2 * d) :=
    mul_nonneg (pow_nonneg hr.le _) (pow_nonneg (hr.le.trans hrs) _)
  have := mul_nonneg hrs0 hτ
  linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSeparateWeierstrassDivision
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem SeparateWeierstrassDivision.proof (h : WeierstrassPolynomialDivision.Statement) :
    SeparateWeierstrassDivision.Statement := by
  suffices H : ∀ (N : ℕ) (σ : Type) [Fintype σ] [DecidableEq σ], Fintype.card σ = N →
      ∀ (d : ℕ) (y₀ : Fin d → ℂ) (u₀ : σ → ℂ) (n : σ → ℕ)
        (b : (m : σ) → Fin (n m) → (Fin d → ℂ) → ℂ) (f : (Fin d → ℂ) × (σ → ℂ) → ℂ),
        (∀ m j, AnalyticAt ℂ (b m j) y₀) →
        (∀ m (T : ℂ), T ^ n m + ∑ j, b m j y₀ * T ^ (j : ℕ) = (T - u₀ m) ^ n m) →
        AnalyticAt ℂ f (y₀, u₀) →
        ∃ (v : σ → (Fin d → ℂ) × (σ → ℂ) → ℂ) (r : ((m : σ) → Fin (n m)) → (Fin d → ℂ) → ℂ),
          (∀ m, AnalyticAt ℂ (v m) (y₀, u₀)) ∧ (∀ α, AnalyticAt ℂ (r α) y₀) ∧
          ∀ᶠ x in 𝓝 (y₀, u₀),
            f x = ∑ m, v m x * (x.2 m ^ n m + ∑ j, b m j x.1 * x.2 m ^ (j : ℕ)) +
              ∑ α, r α x.1 * ∏ m, x.2 m ^ (α m : ℕ) by
    intro σ _ _ d y₀ u₀ n b f hb hG hf
    exact H _ σ rfl d y₀ u₀ n b f hb hG hf
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro σ _ _ hN d y₀ u₀ n b f hb hG hf
  rcases isEmpty_or_nonempty σ with hσ | ⟨⟨k⟩⟩
  ·
    refine ⟨fun _ _ => 0, fun _ y => f (y, u₀), fun _ => analyticAt_const,
      fun _ => hf.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl, Eventually.of_forall fun x => ?_⟩
    have hx : x = (x.1, u₀) := Prod.ext rfl (Subsingleton.elim _ _)
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, mul_one, zero_add,
      Fintype.sum_unique]
    rw [← hx]
  · obtain ⟨q, e, hq, he, hev⟩ :=
      weierstrassDivision_in_coordinate h k d y₀ u₀ (n k) (b k) f (hb k) (hG k) hf
    have hlt : Fintype.card {m // m ≠ k} < N :=
      hN ▸ Fintype.card_subtype_lt (p := fun m => m ≠ k) (x := k) (by simp)
    have IH := fun i => ih _ hlt {m // m ≠ k} rfl d y₀ (fun m => u₀ m) (fun m => n m)
      (fun m => b m) (e i) (fun m j => hb m j) (fun m T => hG m T) (he i)
    choose V R hV hR hVR using IH
    have hπ : AnalyticAt ℂ (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m : {m // m ≠ k} => x.2 m)) (y₀, u₀) :=
      analyticAt_fst.prod (AnalyticAt.pi (f := fun (m : {m // m ≠ k}) (x : (Fin d → ℂ) × (σ → ℂ)) => x.2 m)
        fun m => (analyticAt_coord _ _).comp analyticAt_snd)
    refine ⟨fun m x => if hm : m = k then q x else
        ∑ i, V i ⟨m, hm⟩ (x.1, fun m' => x.2 m') * x.2 k ^ (i : ℕ),
      fun α y => R (α k) (fun m' => α m') y, fun m => ?_, fun α => hR _ _, ?_⟩
    · by_cases hm : m = k
      · simpa [hm] using hq
      · simp only [hm, dite_false]
        exact Finset.analyticAt_fun_sum _ fun i _ =>
          ((hV i ⟨m, hm⟩).comp_of_eq hπ rfl).fun_mul
            (((analyticAt_coord k _).comp analyticAt_snd).fun_pow _)
    · have hT : Tendsto (fun x : (Fin d → ℂ) × (σ → ℂ) => (x.1, fun m' : {m // m ≠ k} => x.2 m'))
          (𝓝 (y₀, u₀)) (𝓝 (y₀, fun m' => u₀ m')) := hπ.continuousAt.tendsto
      filter_upwards [hev, hT.eventually (Filter.eventually_all.2 hVR)] with x hx hx'
      rw [hx, Fintype.sum_eq_add_sum_subtype_ne _ k,
        ← (Equiv.piSplitAt k (fun m => Fin (n m))).symm.sum_comp, Fintype.sum_prod_type]
      have hne : ∀ m : {m // m ≠ k}, ¬ ((m : σ) = k) := fun m => m.2
      simp_rw [Fintype.prod_eq_mul_prod_subtype_ne _ k]
      simp only [Equiv.piSplitAt_symm_apply, dite_true, hne, dite_false, Subtype.coe_eta, hx']
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      rw [add_assoc]
      congr 1
      congr 1
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => by ring
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

theorem SliceLength.proof (hV : IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.Statement)
    (hR : SliceReducedGeneral.Statement) (hM : SliceMultGeneral.Statement) :
    SliceLength.Statement := by
  intro n d J W u hJ hdim hu hW
  have hWp : W.IsPrime := hW.1.1
  obtain ⟨f₁, hf₁W, hf₁⟩ := hR n d J W u hJ hdim hu hW
  obtain ⟨f₂, hf₂W, hf₂⟩ := hM n d J W u hJ hdim hu hW
  have hf : f₁ * f₂ ∉ W := fun h => (hWp.mem_or_mem h).elim hf₁W hf₂W
  have hUo : IsOpen {x : Fin n → ℂ | eval x (f₁ * f₂) ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval (p := f₁ * f₂)) continuous_const
  refine ⟨{x | eval x (f₁ * f₂) ≠ 0}, hUo, ?_, ?_⟩
  ·
    intro x hx
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    apply hf
    refine hV n W (f₁ * f₂) x hWp hx ?_
    filter_upwards [ht] with y hyt hyW
    by_contra hne
    have hy : y ∈ t ∩ (zeroSet W ∩ {x | eval x (f₁ * f₂) ≠ 0}) := ⟨hyt, hyW, hne⟩
    rw [hempty] at hy
    exact hy
  ·
    rintro q ⟨hqW, hqf⟩
    rw [Set.mem_ofPred_eq, map_mul, mul_ne_zero_iff] at hqf
    obtain ⟨O₁, hO₁o, hO₁d, hO₁⟩ := hf₁ q hqW hqf.1
    obtain ⟨O₂, -, hO₂d, hO₂⟩ := hf₂ q hqW hqf.2
    exact (hO₁d.inter_of_isOpen_left hO₂d hO₁o).mono fun L (hL : L ∈ O₁ ∩ O₂) => ⟨hO₁ L hL.1, hO₂ L hL.2⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchGermDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchGermDimOne.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    0 < m → (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
      ringKrullDim (curveLocalRing I q) = 1

end

end GroundTheory.Heights₂.Heights
end

