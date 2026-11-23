module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0001
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalAbstract
section
noncomputable section

namespace PI.EF.Loc

open Complex Metric Set Filter Topology

def locC (r R' R : ℝ) : ℝ :=
  4 * (r + R') / (R' - r) ^ 2 + R' / (R * (R - R')) / Real.log (R / R')

lemma locC_pos {r R' R : ℝ} (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) : 0 < locC r R' R := by
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  have h1 : 0 < 4 * (r + R') / (R' - r) ^ 2 :=
    div_pos (by linarith) (pow_pos (by linarith) 2)
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have h2 : 0 < R' / (R * (R - R')) / Real.log (R / R') :=
    div_pos (div_pos hR' (mul_pos hR (by linarith))) hlog
  unfold locC
  linarith

section core

variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}

def gfun (s₀ : ℂ) (R : ℝ) (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (∏ ρ ∈ Z, (refl s₀ R ρ z) ^ (m ρ)) * h z

private theorem differentiableOn_gfun_of_differentiableOn {U : Set ℂ} (hh : DifferentiableOn ℂ h U) :
    DifferentiableOn ℂ (gfun s₀ R Z m h) U := by
  have e : gfun s₀ R Z m h = fun z => (∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) * h z := rfl
  rw [e]
  refine DifferentiableOn.mul ?_ hh
  have hd : Differentiable ℂ (fun z => ∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) := by
    first
      | exact Differentiable.finset_prod fun ρ _ => (differentiable_refl s₀ R ρ).pow (m ρ)
      | (have hbd := differentiable_refl s₀ R; fun_prop)
  exact hd.differentiableOn

lemma gfun_bounds (hR' : 0 < R') (hR'R : R' < R)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    (∀ z ∈ closedBall s₀ R, ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * ‖gfun s₀ R Z m h s₀‖) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * Real.log (R / R') ≤ M := by
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑ ρ ∈ Z, m ρ = N := ⟨_, rfl⟩
  have hs₀R' : s₀ ∈ closedBall s₀ R' := mem_closedBall_self hR'.le
  have hs₀R : s₀ ∈ closedBall s₀ R := mem_closedBall_self hR.le
  have hhs₀ : h s₀ ≠ 0 := hh0 s₀ hs₀R'
  have hg₀ : gfun s₀ R Z m h s₀ = (R : ℂ) ^ N * h s₀ := by
    have hc : ∀ ρ ∈ Z, refl s₀ R ρ s₀ ^ m ρ = (R : ℂ) ^ m ρ := fun ρ _ => by
      rw [refl_center hR]
    simp only [gfun]
    rw [Finset.prod_congr rfl hc, Finset.prod_pow_eq_pow_sum, hN]
  have hg₀n : ‖gfun s₀ R Z m h s₀‖ = R ^ N * ‖h s₀‖ := by
    rw [hg₀, norm_mul, norm_pow]
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hf₀ : ‖f s₀‖ ≤ R' ^ N * ‖h s₀‖ := by
    rw [hfac s₀ hs₀R, norm_mul, norm_prod]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ∏ ρ ∈ Z, ‖(s₀ - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖s₀ - ρ‖ ^ m ρ := by simp only [norm_pow]
      _ ≤ ∏ ρ ∈ Z, R' ^ m ρ := by
        refine Finset.prod_le_prod₀ (fun ρ _ => by positivity) fun ρ hρ => ?_
        have hρ' : ρ ∈ closedBall s₀ R' := ((hZ ρ).1 hρ).1
        rw [mem_closedBall, dist_eq_norm] at hρ'
        rw [norm_sub_rev]
        exact pow_le_pow_left₀ (norm_nonneg _) hρ' _
      _ = R' ^ N := by rw [Finset.prod_pow_eq_pow_sum, hN]
  have hsphere : ∀ z ∈ sphere s₀ R, ‖gfun s₀ R Z m h z‖ = ‖f z‖ := by
    intro z hz
    rw [hfac z (sphere_subset_closedBall hz)]
    simp only [gfun, norm_mul, norm_prod, norm_pow, norm_refl_sphere hR hz]
  have hdc : DiffContOnCl ℂ (gfun s₀ R Z m h) (ball s₀ R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s₀ hR.ne']
    exact differentiableOn_gfun_of_differentiableOn hh
  have hmax : ∀ z ∈ closedBall s₀ R,
      ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * (R' ^ N * ‖h s₀‖) := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
      (by rwa [closure_ball s₀ hR.ne'])
    intro w hw
    rw [frontier_ball s₀ hR.ne'] at hw
    rw [hsphere w hw]
    exact (hb w (sphere_subset_closedBall hw)).trans
      (mul_le_mul_of_nonneg_left hf₀ (Real.exp_pos M).le)
  have hkey : R ^ N ≤ Real.exp M * R' ^ N := by
    have h1 := hmax s₀ hs₀R
    rw [hg₀n, ← mul_assoc] at h1
    exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hhs₀)
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hg₀n]
    refine (hmax z hz).trans ?_
    have hp : R' ^ N ≤ R ^ N := pow_le_pow_left₀ hR'.le hR'R.le N
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      (Real.exp_pos M).le
  · rw [hN]
    have hl := Real.log_le_log (pow_pos hR N) hkey
    rw [Real.log_mul (Real.exp_pos M).ne' (pow_pos hR' N).ne', Real.log_exp, Real.log_pow,
      Real.log_pow] at hl
    rw [Real.log_div hR.ne' hR'.ne', mul_sub]
    linarith

theorem core (hDL : PI.DiscLog) (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) (hM : 0 < M)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
      ‖logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  intro s hs hfs
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨hg, hN⟩ := gfun_bounds hR' hR'R hZ hh hh0 hfac hb
  have hsR' : s ∈ closedBall s₀ R' := closedBall_subset_closedBall hrR'.le hs
  have hsball : s ∈ ball s₀ R := closedBall_subset_ball (hrR'.trans hR'R) hs
  have hsR : s ∈ closedBall s₀ R := ball_subset_closedBall hsball
  have hnhds : closedBall s₀ R ∈ 𝓝 s :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hsball) ball_subset_closedBall
  have hhs : h s ≠ 0 := hh0 s hsR'
  have hhd : DifferentiableAt ℂ h s := hh.differentiableAt hnhds
  have hρs : ∀ ρ ∈ Z, s - ρ ≠ 0 := by
    intro ρ hρ h0
    have hsρ : s = ρ := sub_eq_zero.mp h0
    exact hfs (by rw [hsρ]; exact ((hZ ρ).1 hρ).2)
  have hfeq : f =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem hnhds fun z hz => hfac z hz
  have hlf : logDeriv f s = (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + logDeriv h s := by
    have e1 : logDeriv f s = logDeriv (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z) s := by
      rw [logDeriv_apply, logDeriv_apply, hfeq.deriv_eq, hfeq.eq_of_nhds]
    rw [e1]
    refine (logDeriv_prod_pow_mul (φ := fun ρ z => z - ρ) (h := h) hρs
      (fun ρ _ => by fun_prop) hhs hhd).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    show (m ρ : ℂ) * logDeriv (fun z => z - ρ) s = (m ρ : ℂ) / (s - ρ)
    simp only [logDeriv_apply, deriv_sub_const, deriv_id'']
    ring
  have hBne : ∀ z ∈ closedBall s₀ R, ∀ ρ ∈ Z, refl s₀ R ρ z ≠ 0 := by
    intro z hz ρ hρ h0
    have h1 := le_norm_refl (R' := R') hR ((hZ ρ).1 hρ).1 hz
    rw [h0, norm_zero] at h1
    linarith
  have hlg : logDeriv (gfun s₀ R Z m h) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s) + logDeriv h s :=
    logDeriv_prod_pow_mul (φ := fun ρ => refl s₀ R ρ) (fun ρ hρ => hBne s hsR ρ hρ)
      (fun ρ _ => (differentiable_refl s₀ R ρ).differentiableAt) hhs hhd
  have hsub : ball s₀ R' ⊆ closedBall s₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hR'R.le)
  have hgne : ∀ z ∈ ball s₀ R', gfun s₀ R Z m h z ≠ 0 := by
    intro z hz
    simp only [gfun]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hBne z (hsub hz) ρ hρ))
      (hh0 z (ball_subset_closedBall hz))
  have hLg := logDeriv_bound_of_zero_free hDL hr hrR' hM
    (differentiableOn_gfun_of_differentiableOn (hh.mono hsub)) hgne (fun z hz => hg z (hsub hz)) s hs
  have hLg' : ‖logDeriv (gfun s₀ R Z m h) s‖ ≤ 4 * (r + R') / (R' - r) ^ 2 * M := by
    rw [logDeriv_apply]
    exact hLg
  have hK : 0 ≤ R' / (R * (R - R')) := div_nonneg hR'.le (mul_pos hR (by linarith)).le
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have hNle : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ M / Real.log (R / R') := by
    exact (le_div_iff₀ hlog).mpr hN
  have hsumB : ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ ≤
      R' / (R * (R - R')) / Real.log (R / R') * M := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (R' / (R * (R - R'))) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_mul]
          have hn : ‖(m ρ : ℂ)‖ = (m ρ : ℝ) := by
            exact Complex.norm_natCast _
          rw [hn]
          exact mul_le_mul_of_nonneg_left
            (norm_logDeriv_refl_le hR'R hR ((hZ ρ).1 hρ).1 hsR) (Nat.cast_nonneg _)
      _ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (R' / (R * (R - R'))) := by
          rw [Nat.cast_sum, Finset.sum_mul]
      _ ≤ M / Real.log (R / R') * (R' / (R * (R - R'))) :=
          mul_le_mul_of_nonneg_right hNle hK
      _ = R' / (R * (R - R')) / Real.log (R / R') * M := by ring
  have hdiff : logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) =
      logDeriv (gfun s₀ R Z m h) s -
        ∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s := by
    rw [hlf, hlg]
    ring
  rw [hdiff]
  calc _ ≤ ‖logDeriv (gfun s₀ R Z m h) s‖ +
        ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sub_le _ _
    _ ≤ 4 * (r + R') / (R' - r) ^ 2 * M + R' / (R * (R - R')) / Real.log (R / R') * M :=
        add_le_add hLg' hsumB
    _ = locC r R' R * M := by
        unfold locC
        ring

end core

theorem local_abstract (hDF : PI.DiscFactor) (hDL : PI.DiscLog) {r R' R : ℝ} (hr : 0 < r)
    (hrR' : r < R') (hR'R : R' < R) (f : ℂ → ℂ) (s₀ : ℂ) (M : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall s₀ R)) (hf0 : f s₀ ≠ 0) (hM : 0 ≤ M)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ({ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0}).Finite ∧
      ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
        ‖logDeriv f s - ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0},
            (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  have hR' : 0 < R' := hr.trans hrR'
  have hfd : DifferentiableOn ℂ f (closedBall s₀ R) := hf.differentiableOn
  obtain ⟨Z, m, h, hZ, -, hh, hh0, hfac⟩ := hDF f s₀ R R' hR' hR'R hfd hf0
  have hset : {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0} = (Z : Set ℂ) := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (hZ ρ).symm
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := by
    intro ρ hρ
    have hρR : ρ ∈ ball s₀ R := closedBall_subset_ball hR'R ((hZ ρ).1 hρ).1
    exact order_eq_of_factor hρ (isOpen_ball.mem_nhds hρR)
      (hf ρ (ball_subset_closedBall hρR)) (hh.mono ball_subset_closedBall)
      (hh0 ρ ((hZ ρ).1 hρ).1) fun z hz => hfac z (ball_subset_closedBall hz)
  refine ⟨by rw [hset]; exact Z.finite_toSet, ?_⟩
  intro s hs hfs
  have hsum : ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) :=
    Finset.sum_congr rfl fun ρ hρ => by rw [hord ρ hρ]
  rw [hset, finsum_mem_coe_finset, hsum]
  have hC : 0 < locC r R' R := locC_pos hr hrR' hR'R
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hεC : 0 < ε / locC r R' R := div_pos hε hC
  have hM' : 0 < M + ε / locC r R' R := add_pos_of_nonneg_of_pos hM hεC
  have hb' : ∀ z ∈ closedBall s₀ R,
      ‖f z‖ ≤ Real.exp (M + ε / locC r R' R) * ‖f s₀‖ := fun z hz =>
    (hb z hz).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _))
  have key := core hDL hr hrR' hR'R hM' hZ hh hh0 hfac hb' s hs hfs
  have hCε : locC r R' R * (ε / locC r R' R) = ε := by
    exact mul_div_cancel₀ ε hC.ne'
  calc _ ≤ locC r R' R * (M + ε / locC r R' R) := key
    _ = locC r R' R * M + ε := by rw [mul_add, hCε]

end PI.EF.Loc
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBounds
section
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem norm_root_number_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖eps0 χ‖ ≤ 1 := by
  unfold PI.EF.eps0
  split_ifs <;> simp

theorem norm_character_correction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖del1 χ‖ ≤ 1 := by
  unfold PI.EF.del1
  split_ifs <;> simp

theorem norm_near_sum_le {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      C * Real.log (N * (|s.im| + 2)) / d := by
  have hf := (hC N χ hχ s.im).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  calc ‖∑ ρ ∈ hf.toFinset, (mult χ ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ hf.toFinset, ‖(mult χ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ) / d := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (h ρ ((Set.Finite.mem_toFinset hf).mp hρ))
    _ = (∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ)) / d := by rw [Finset.sum_div]
    _ ≤ C * Real.log (N * (|s.im| + 2)) / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
        exact (hC N χ hχ s.im).2

private lemma norm_le_add_add_four_of_norm_sub_le {a b c e : ℂ} {x y : ℝ} (h1 : ‖a - b - c + e‖ ≤ x) (h2 : ‖b‖ ≤ y)
    (h3 : ‖c‖ ≤ 2) (h4 : ‖e‖ ≤ 2) : ‖a‖ ≤ x + y + 4 := by
  have e1 : a = (a - b - c + e) + b + c - e := by ring
  rw [e1]
  have k1 := norm_sub_le ((a - b - c + e) + b + c) e
  have k2 := norm_add_le ((a - b - c + e) + b) c
  have k3 := norm_add_le (a - b - c + e) b
  linarith

theorem norm_logDeriv_le {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3)
    (h0 : LFunction χ s ≠ 0) (hs0 : 1 / 2 ≤ ‖s‖) (hs1 : 1 / 2 ≤ ‖s - 1‖) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖logDeriv (LFunction χ) s‖ ≤
      Cl * Real.log (N * (|s.im| + 2)) + Cw * Real.log (N * (|s.im| + 2)) / d + 4 := by
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hs1
  have hmain := hL N χ hχ s h1 h2 h0 hs1'
  have hsum := norm_near_sum_le hW χ hχ s hd h
  have hE : ‖eps0 χ / s‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_root_number_le_one χ]
  have hD : ‖del1 χ / (s - 1)‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_character_correction_le χ]
  exact norm_le_add_add_four_of_norm_sub_le hmain hsum hE hD

theorem log_two_le_log {N : ℕ} [NeZero N] {x : ℝ} (hx : 2 ≤ x) : Real.log 2 ≤ Real.log (N * x) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact Real.log_le_log (by norm_num) (by nlinarith)

theorem logDerivLeft_of {Cw Cl : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hW : ZerosWindowWith Cw)
    (hL : LocalLemma Cl) (hZ : ZeroLocus) : LogDerivLeft (Cl + 2 * Cw + 6) := by
  unfold PI.EF.LogDerivLeft PI.EF.ZeroLocus at *
  intro N _ χ hχ t
  have hre : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re = -1 / 2 := by norm_num
  have him : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im = t := by norm_num
  have hne1 : ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro a
    have := congrArg Complex.re a
    rw [hre] at this
    norm_num at this
  have hL0 : LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h0
    rcases hZ N χ hχ _ (by rw [hre]; norm_num) hne1 h0 with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · rw [hre] at a
      norm_num at a
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
  have hs0 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ :=
    le_trans (by rw [hre]; norm_num) (Complex.abs_re_le_norm _)
  have hs1 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - 1‖ :=
    le_trans (by rw [Complex.sub_re, hre, Complex.one_re]; norm_num) (Complex.abs_re_le_norm _)
  have hnear : ∀ ρ ∈ ZerosNear χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im,
      1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, -⟩ := hρ
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, hre, abs_of_neg (by linarith)]
    linarith
  have key := norm_logDeriv_le hW hL χ hχ _ hre.symm.le (by rw [hre]; norm_num) hL0 hs0 hs1
    (by norm_num : (0 : ℝ) < 1 / 2) hnear
  rw [him] at key
  have hlog2 : Real.log 2 ≤ Real.log (N * (|t| + 2)) := log_two_le_log (by linarith [abs_nonneg t])
  have hl2 := Real.log_two_gt_d9
  refine le_trans key ?_
  calc Cl * Real.log (N * (|t| + 2)) + Cw * Real.log (N * (|t| + 2)) / (1 / 2) + 4
        = Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) + 4 := by ring
    _ ≤ Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) +
          6 * Real.log (N * (|t| + 2)) := by linarith
    _ = (Cl + 2 * Cw + 6) * Real.log (N * (|t| + 2)) := by ring

theorem norm_logDeriv_horiz {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T' : ℝ} (hT' : 2 ≤ T')
    (hg : GoodHeight χ κ T') (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) (him : |s.im| = T') :
    ‖logDeriv (LFunction χ) s‖ ≤ (4 * Cl + 2 * Cw * κ + 16) * Real.log (N * T') ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hℓ2 : Real.log 2 ≤ Real.log (N * T') := log_two_le_log hT'
  have hl2 := Real.log_two_gt_d9
  have hlogT2 : Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * T') := by
    have e : 2 * Real.log (N * T') = Real.log ((N * T') ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [e]
    apply Real.log_le_log (by nlinarith)
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hT2 : T' + 2 ≤ T' ^ 2 := by nlinarith
    calc (N : ℝ) * (T' + 2) ≤ N * T' ^ 2 := mul_le_mul_of_nonneg_left hT2 (by linarith)
      _ ≤ N ^ 2 * T' ^ 2 := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = (N * T') ^ 2 := by ring
  have hlogpos2 : 0 ≤ Real.log (N * (T' + 2)) := Real.log_nonneg (by nlinarith)
  unfold PI.EF.GoodHeight at hg
  set ℓ := Real.log (N * T') with hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hd : 0 < 1 / (κ * ℓ) := one_div_pos.mpr (mul_pos hκ hℓpos)
  have hsim : 2 ≤ |s.im| := by rw [him]; exact hT'
  have hs0 : 1 / 2 ≤ ‖s‖ := by linarith [Complex.abs_im_le_norm s]
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hsim
  have hL0 : LFunction χ s ≠ 0 := by
    intro h0
    rcases hZ N χ hχ s (by linarith) hs1' h0 with ⟨a1, a2⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · have := hg s a1 a2 h0
      rw [him, sub_self, abs_zero] at this
      linarith
    · rw [a] at hsim
      norm_num at hsim
    · rw [a] at hsim
      norm_num at hsim
  have hnear : ∀ ρ ∈ ZerosNear χ s.im, 1 / (κ * ℓ) ≤ ‖s - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, a4⟩ := hρ
    have hgρ := hg ρ a1 a2 a4
    have k1 : |(|ρ.im|) - T'| ≤ |s.im - ρ.im| := by
      rw [← him, abs_sub_comm]
      exact abs_abs_sub_abs_le_abs_sub s.im ρ.im
    have k2 : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    linarith
  have key := norm_logDeriv_le hW hL χ hχ s h1 h2 hL0 hs0 hs1 hd hnear
  rw [him, div_div_eq_mul_div, div_one] at key
  refine le_trans key ?_
  have h_a : Cl * Real.log (N * (T' + 2)) ≤ Cl * (2 * ℓ) := mul_le_mul_of_nonneg_left hlogT2 hCl
  have h_b : 2 * ℓ ≤ 4 * ℓ ^ 2 := by nlinarith
  have h_c : Cl * (2 * ℓ) ≤ Cl * (4 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h_b hCl
  have h_d : Cw * Real.log (N * (T' + 2)) * (κ * ℓ) ≤ Cw * (2 * ℓ) * (κ * ℓ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogT2 hCw) (mul_pos hκ hℓpos).le
  have h_e : 4 ≤ 16 * ℓ ^ 2 := by nlinarith
  nlinarith [h_a, h_c, h_d, h_e]

theorem logDerivHoriz_of {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) :
    LogDerivHoriz κ (4 * Cl + 2 * Cw * κ + 16) := by
  unfold PI.EF.LogDerivHoriz
  intro N _ χ hχ T' hT' hg σ h1 h2
  have hT0 : (0 : ℝ) ≤ T' := by linarith
  constructor
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])

end PI.EF
end
end

