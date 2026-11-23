module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronKernelA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructC
section
noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

lemma isCompact_rect (x₀ x₁ y₀ y₁ : ℝ) : IsCompact (rect x₀ x₁ y₀ y₁) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma mem_rect {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by
  simp only [rect, Complex.mem_reProdIm, Set.mem_Icc]

variable {N : ℕ} [NeZero N]

def Lent (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  open Classical in if χ = 1 then LFunctionTrivChar₁ N else LFunction χ

lemma differentiable_Lent (χ : DirichletCharacter ℂ N) : Differentiable ℂ (Lent χ) := by
  unfold Lent
  split_ifs with h
  · exact differentiable_LFunctionTrivChar₁ N
  · exact differentiable_LFunction h

lemma Lent_of_ne {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) : Lent χ = LFunction χ := by
  unfold Lent
  rw [if_neg h]

lemma Lent_one_apply {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = (s - 1) * LFunction χ s := by
  subst h
  unfold Lent
  rw [if_pos rfl]
  first
    | (rw [LFunctionTrivChar₁, Function.update_of_ne hs]; rfl)
    | (simp [LFunctionTrivChar₁, Function.update_of_ne hs])
    | (simp [LFunctionTrivChar₁, hs])

lemma Lent_two_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 2 ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have hL : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inr h2) (by norm_num)
  by_cases h : χ = 1
  · rw [Lent_one_apply h h2]
    exact mul_ne_zero (sub_ne_zero.mpr h2) hL
  · rw [Lent_of_ne h]
    exact hL

lemma Lent_one_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 1 ≠ 0 := by
  by_cases h : χ = 1
  · unfold Lent
    rw [if_pos h]
    exact LFunctionTrivChar₁_apply_one_ne_zero N
  · rw [Lent_of_ne h]
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h) (by simp)

lemma Lent_eq_zero_iff (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = 0 ↔ LFunction χ s = 0 := by
  by_cases h : χ = 1
  · rw [Lent_one_apply h hs, mul_eq_zero]
    simp [sub_eq_zero, hs]
  · rw [Lent_of_ne h]

lemma Lent_eventuallyEq {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ =ᶠ[𝓝 s] (fun z => z - 1) * LFunction χ := by
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  rw [Lent_one_apply h hz]
  rfl

lemma order_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt (Lent χ) s = analyticOrderNatAt (LFunction χ) s := by
  by_cases h : χ = 1
  · have hL : AnalyticAt ℂ (LFunction χ) s := by
      apply DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      · intro z hz
        exact (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
      · exact isOpen_ne.mem_nhds hs
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
      h1.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs)
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr (Lent_eventuallyEq h hs), analyticOrderAt_mul h1 hL, h0, zero_add]
  · rw [Lent_of_ne h]

lemma logDeriv_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) (h0 : LFunction χ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (Lent χ) s - del1 χ / (s - 1) := by
  by_cases h : χ = 1
  · have hd : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s (Or.inl hs)
    have he := Lent_eventuallyEq h hs
    have h1 : logDeriv (Lent χ) s = logDeriv (fun z => (z - 1) * LFunction χ z) s := by
      unfold logDeriv
      simp only [Pi.div_apply]
      rw [he.deriv_eq, he.eq_of_nhds]
      rfl
    have h2 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
      simp [logDeriv_apply]
    have hdz : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const (1 : ℂ)
    rw [h1, logDeriv_fun_mul (f := fun z : ℂ => z - 1) (g := LFunction χ) s
      (sub_ne_zero.mpr hs) h0 hdz hd, h2]
    simp only [del1, if_pos h]
    ring
  · rw [Lent_of_ne h]
    simp [del1, h]

theorem zerosFinite : ZerosFinite := by
  intro N _ χ hχ T
  have h := finite_zeros_of_compact (differentiable_Lent χ) (Lent_two_ne_zero χ)
    (isCompact_rect 0 1 (-T) T)
  refine h.subset ?_
  intro ρ hρ
  obtain ⟨hre0, hre1, him, hL⟩ := hρ
  have h1 : ρ ≠ 1 := fun e => by rw [e] at hre1; simp at hre1
  refine ⟨mem_rect.mpr ⟨⟨hre0.le, hre1.le⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [neg_abs_le ρ.im]
  · linarith [le_abs_self ρ.im]
  · exact (Lent_eq_zero_iff χ h1).mpr hL

theorem regularPart : RegularPart := by
  intro N _ χ hχ x₁ T' hx₁ hT' hNO
  classical
  have hSfin : (ZerosBelow χ T').Finite := zerosFinite N χ hχ T'

  obtain ⟨E0, hE0⟩ : ∃ E0 : Finset ℂ, E0 = if χ.Even ∧ χ ≠ 1 then {0} else ∅ := ⟨_, rfl⟩
  have hE0mem : ∀ ρ, ρ ∈ E0 ↔ ρ = 0 ∧ χ.Even ∧ χ ≠ 1 := by
    intro ρ
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.mem_singleton]
      exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
    · rw [if_neg he]
      simp only [Finset.notMem_empty, false_iff]
      exact fun h => he h.2
  have hre1 : ∀ ρ ∈ ZerosBelow χ T', ρ ≠ 1 := by
    intro ρ hρ e
    have h := hρ.2.1
    rw [e] at h
    simp at h
  have hZ0 : ∀ ρ ∈ hSfin.toFinset ∪ E0, Lent χ ρ = 0 := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · have h' := hSfin.mem_toFinset.mp h
      exact (Lent_eq_zero_iff χ (hre1 ρ h')).mpr h'.2.2.2
    · obtain ⟨rfl, he, h1⟩ := (hE0mem ρ).mp h
      exact (Lent_eq_zero_iff χ zero_ne_one).mpr (mult_zero_of_even hχ he h1).1
  have hK : ∀ s ∈ rect (-1 / 2) x₁ (-T') T', Lent χ s = 0 → s ∈ hSfin.toFinset ∪ E0 := by
    intro s hs hz
    have hs1 : s ≠ 1 := fun e => Lent_one_ne_zero χ (e ▸ hz)
    have hL : LFunction χ s = 0 := (Lent_eq_zero_iff χ hs1).mp hz
    obtain ⟨⟨hsre0, hsre1⟩, him0, him1⟩ := mem_rect.mp hs
    rcases zeroLocus N χ hχ s (by linarith) hs1 hL with h | h | h
    · apply Finset.mem_union_left
      rw [hSfin.mem_toFinset]
      refine ⟨h.1, h.2, ?_, hL⟩
      have hle : |s.im| ≤ T' := abs_le.mpr ⟨him0, him1⟩
      exact lt_of_le_of_ne hle (hNO s h.1 h.2 hL)
    · exact Finset.mem_union_right _ ((hE0mem s).mpr h)
    · exfalso
      rw [h.1] at hsre0
      norm_num at hsre0
  have hf : AnalyticOnNhd ℂ (Lent χ) (rect (-1 / 2) x₁ (-T') T') := fun x _ =>
    (differentiable_Lent χ).analyticAt x
  have hfin : ∀ ρ ∈ rect (-1 / 2) x₁ (-T') T', analyticOrderAt (Lent χ) ρ ≠ ⊤ := fun ρ _ =>
    order_ne_top_of_entire (differentiable_Lent χ) (Lent_two_ne_zero χ) ρ
  obtain ⟨H, hH, hHeq⟩ := exists_regular_part hf (hSfin.toFinset ∪ E0) hZ0 hK hfin
  refine ⟨H, hH.differentiableOn, ?_⟩
  intro s hs hL0 hs1
  have hLe : Lent χ s ≠ 0 := fun e => hL0 ((Lent_eq_zero_iff χ hs1).mp e)
  have hdisj : Disjoint hSfin.toFinset E0 := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have h1' := (hSfin.mem_toFinset.mp h1).1
    rw [((hE0mem ρ).mp h2).1] at h1'
    simp at h1'
  have hS : ∑ ρ ∈ hSfin.toFinset, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) =
      ∑ ρ ∈ hSfin.toFinset, (mult χ ρ : ℂ) / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [order_Lent χ (hre1 ρ (hSfin.mem_toFinset.mp hρ))]
  have hE : ∑ ρ ∈ E0, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) = eps0 χ / s := by
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.sum_singleton, order_Lent χ zero_ne_one,
        (mult_zero_of_even hχ he.1 he.2).2]
      simp only [eps0, if_pos he]
      simp
    · rw [if_neg he]
      simp only [eps0, if_neg he]
      simp
  rw [logDeriv_Lent χ hs1 hL0, hHeq s hs hLe, Finset.sum_union hdisj,
    finsum_mem_eq_finite_toFinset_sum _ hSfin, hS, hE]
  ring

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronKernelB
section
namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real

lemma norm_log_sub_log_le (c T : ℝ) (hc : 0 < c) :
    ‖Complex.log (((c : ℂ) + (T : ℂ) * I) - 0) - Complex.log (((c : ℂ) + ((-T : ℝ) : ℂ) * I) - 0)‖ ≤ π := by
  simp only [sub_zero]
  set z1 : ℂ := (c : ℂ) + T * I with hz1
  set z2 : ℂ := (c : ℂ) + ((-T : ℝ) : ℂ) * I with hz2
  have hconj : (starRingEnd ℂ) z1 = z2 := by
    rw [hz1, hz2, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hn : ‖z1‖ = ‖z2‖ := by rw [← hconj, Complex.norm_conj]
  have hre1 : 0 ≤ z1.re := by simp [hz1]; linarith
  have hre2 : 0 ≤ z2.re := by simp [hz2]; linarith
  have ha1 := Complex.abs_arg_le_pi_div_two_iff.mpr hre1
  have ha2 := Complex.abs_arg_le_pi_div_two_iff.mpr hre2
  calc ‖Complex.log z1 - Complex.log z2‖
      ≤ |(Complex.log z1 - Complex.log z2).re| + |(Complex.log z1 - Complex.log z2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Complex.arg z1 - Complex.arg z2| := by
        rw [Complex.sub_re, Complex.sub_im, Complex.log_re, Complex.log_re, hn, sub_self, abs_zero, zero_add,
          Complex.log_im, Complex.log_im]
    _ ≤ |Complex.arg z1| + |Complex.arg z2| := abs_sub _ _
    _ ≤ π := by linarith

lemma line_ne_zero (c : ℝ) (hc : 0 < c) (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp at h1
  linarith

lemma line_bound_small (l c T : ℝ) (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I)‖ ≤ Real.exp (l * c) * (π + |l| * (2 * T)) := by
  have hdec : (fun t : ℝ => ker l ((c : ℂ) + t * I)) = fun t : ℝ =>
      cexp (l * c) * (1 / (((c : ℂ) + t * I) - 0)) +
        cexp (l * c) * ((cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)) := by
    funext t
    have hexp : cexp (l * ((c : ℂ) + t * I)) = cexp (l * c) * cexp (I * ((l * t : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    unfold ker
    rw [hexp, sub_zero]
    ring
  have hc1 : Continuous fun t : ℝ => (1 : ℂ) / (((c : ℂ) + t * I) - 0) :=
    continuous_const.div₀ (by fun_prop) (fun t => by simpa using line_ne_zero c hc t)
  have hc2 : Continuous fun t : ℝ => (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I) :=
    Continuous.div₀ (by fun_prop) (by fun_prop) (line_ne_zero c hc)
  rw [hdec, intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
    ((hc2.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← mul_add, norm_mul]
  have hE : ‖cexp (l * c)‖ = Real.exp (l * c) := by
    rw [Complex.norm_exp]; simp
  rw [hE]
  have hP : ‖∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)‖ ≤ π := by
    have h := vert_inv_right (-T) T c 0 (by rw [Complex.zero_re]; exact hc)
    have h2 := norm_log_sub_log_le c T hc
    rw [← h, norm_smul, norm_I, one_mul] at h2
    exact h2
  have hQ : ‖∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖
      ≤ |l| * (2 * T) := by
    have h1 : ∀ t ∈ Set.uIoc (-T) T,
        ‖(cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖ ≤ |l| := by
      intro t _
      rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (line_ne_zero c hc t))]
      have a1 : ‖cexp (I * ((l * t : ℝ) : ℂ)) - 1‖ ≤ ‖l * t‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
      have a2 : |t| ≤ ‖(c : ℂ) + t * I‖ := by
        have := Complex.abs_im_le_norm ((c : ℂ) + t * I)
        simpa using this
      calc ‖cexp (I * ((l * t : ℝ) : ℂ)) - 1‖ ≤ ‖l * t‖ := a1
        _ = |l| * |t| := by rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |l| * ‖(c : ℂ) + t * I‖ := by gcongr
    have h2 := norm_integral_le_of_norm_le_const h1
    have e3 : |T - -T| = 2 * T := by
      rw [abs_of_nonneg (by linarith)]; ring
    rwa [e3] at h2
  have hE0 := (Real.exp_pos (l * c)).le
  calc Real.exp (l * c) * ‖(∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)) +
        ∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖
      ≤ Real.exp (l * c) * (‖∫ t : ℝ in -T..T, (1 : ℂ) / (((c : ℂ) + t * I) - 0)‖ +
        ‖∫ t : ℝ in -T..T, (cexp (I * ((l * t : ℝ) : ℂ)) - 1) / ((c : ℂ) + t * I)‖) := by
        gcongr
        exact norm_add_le _ _
    _ ≤ Real.exp (l * c) * (π + |l| * (2 * T)) := by gcongr

theorem perron_kernel_single_term : PerronKernel := by
  intro y c T hy hc hT
  obtain ⟨l, hl⟩ : ∃ l, l = Real.log y := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = y ^ c := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, J = ∫ t : ℝ in -T..T, ker l ((c : ℂ) + t * I) := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / (2 * π) := ⟨_, rfl⟩
  have hpi : 3 < π := Real.pi_gt_three
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r * (2 * π) = 1 := by rw [hr]; field_simp
  have hEe : E = Real.exp (l * c) := by rw [hE, hl]; exact Real.rpow_def_of_pos hy c
  have hE0 : 0 < E := by rw [hEe]; exact Real.exp_pos _
  have hK : perronK y c T = (r : ℂ) * J := by
    unfold perronK
    rw [hr, hJ, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [ker]
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le, ← hl]
  rw [← hl, ← hE, hK]
  obtain ⟨X, hX⟩ : ∃ X, X = ‖(r : ℂ) * J - (if 1 ≤ y then 1 else 0)‖ := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
  have hnr : ‖(r : ℂ)‖ = r := by rw [Complex.norm_real, Real.norm_of_nonneg hr0.le]

  have hb : T * |l| * X ≤ E := by
    rcases lt_trichotomy l 0 with hneg | hzero | hpos
    · have hy1 : y < 1 := (Real.log_neg_iff hy).mp (hl ▸ hneg)
      have h1 := line_bound_neg l c T hneg hc hT
      rw [← hJ, ← hEe] at h1
      have hXe : X = r * ‖J‖ := by
        rw [hX, if_neg (not_le.mpr hy1), sub_zero, norm_mul, hnr]
      rw [hXe, abs_of_neg hneg]
      have hl' : 0 < -l := by linarith
      calc T * -l * (r * ‖J‖) ≤ T * -l * (r * (2 * (E / (-l) / T))) := by gcongr
        _ = (r * 2) * E := by
            have hl0 : l ≠ 0 := hneg.ne
            field_simp
        _ ≤ 1 * E := by
            gcongr
            nlinarith
        _ = E := one_mul _
    · rw [hzero]; simp [hE0.le]
    · have hy1 : 1 ≤ y := ((Real.log_pos_iff hy.le).mp (hl ▸ hpos)).le
      have h1 := line_bound_pos l c T hpos hc hT
      rw [← hJ, ← hEe] at h1
      have hXe : X = r * ‖J - 2 * π‖ := by
        rw [hX, if_pos hy1, ← hnr, ← norm_mul, hnr]
        congr 1
        have : (r : ℂ) * (2 * π) = 1 := by exact_mod_cast hr1
        linear_combination this
      rw [hXe, abs_of_pos hpos]
      calc T * l * (r * ‖J - 2 * π‖) ≤ T * l * (r * (2 * (E / l / T))) := by gcongr
        _ = (r * 2) * E := by field_simp
        _ ≤ 1 * E := by
            gcongr
            nlinarith
        _ = E := one_mul _
  refine ⟨?_, hb⟩
  by_cases hsm : T * |l| ≤ 1
  · have h1 := line_bound_small l c T hc hT
    rw [← hJ, ← hEe] at h1
    have hind : ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ ≤ E := by
      split_ifs with hy1
      · rw [norm_one, hE]
        exact Real.one_le_rpow hy1 hc.le
      · rw [norm_zero]; exact hE0.le
    have h2 : r * ‖J‖ ≤ E := by
      calc r * ‖J‖ ≤ r * (E * (π + |l| * (2 * T))) := by gcongr
        _ ≤ r * (E * (π + 2)) := by
            gcongr
            nlinarith
        _ ≤ r * (E * (2 * π)) := by
            gcongr
            linarith
        _ = (r * (2 * π)) * E := by ring
        _ = E := by rw [hr1, one_mul]
    calc X ≤ ‖(r : ℂ) * J‖ + ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ := by rw [hX]; exact norm_sub_le _ _
      _ = r * ‖J‖ + ‖(if 1 ≤ y then 1 else 0 : ℂ)‖ := by rw [norm_mul, hnr]
      _ ≤ 2 * E := by linarith
  · rw [not_le] at hsm
    nlinarith

end PI.EF.PK
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ShiftBoundOf
section
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem shiftBound_of {κ Cs Cr : ℝ} (hκ : 0 < κ) (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr) (hRP : RegularPart)
    (hCI : ContourIdentity) (hS : SidesBound κ Cs) (hR : RegAtZero Cr) :
    ShiftBound κ (Cs + Cr + 3) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'T hg
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hu2 : (2 : ℝ) ≤ u := hT.trans hTu
  have hT'2 : (2 : ℝ) ≤ T' := hT.trans hTT'
  have hT0 : (0 : ℝ) < T := by linarith
  have hlogNT : 0 < Real.log (N * T') := Real.log_pos (by nlinarith)
  have hNO : NoOrdinate χ T' := by
    intro ρ h1 h2 h3 heq
    have h4 := hg ρ h1 h2 h3
    rw [heq, sub_self, abs_zero] at h4
    have h5 : 0 < 1 / (κ * Real.log (N * T')) := by positivity
    linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hx1 : 1 < cLine u := by
    unfold cLine
    have := one_div_pos.mpr hlogu
    linarith
  obtain ⟨H, hH⟩ := hRP N χ hχ (cLine u) T' hx1 (by linarith) hNO
  have hCIe := hCI N χ hχ u T' H hu2 hT'2 hNO hH
  have hSe := hS N χ hχ u T T' hT hTu hTT' hT'T hg
  have hRe := hR N χ hχ (cLine u) T' H hx1 hT'2 hH
  set R := rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
    (-1 / 2) (cLine u) (-T') T' with hRdef
  set Z := ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ with hZ
  set c : ℂ := 2 * Real.pi * I with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hcn : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  have hA : vertInt χ u T' - del1 χ * u + zsum χ T' u =
      (R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ := by
    rw [hCIe]
    field_simp
    ring
  rw [hA]
  have hE1 : ‖eps0 χ‖ ≤ 1 := by
    unfold eps0
    split_ifs <;> simp
  have hD1 : ‖del1 χ‖ ≤ 1 := by
    unfold del1
    split_ifs <;> simp
  have hS1 : 0 ≤ S1 χ := by
    unfold S1
    exact finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hNu : Real.log u ≤ Real.log (N * u) := Real.log_le_log (by positivity) (by nlinarith)
  have h2N : Real.log (2 * N) ≤ Real.log (N * u) := Real.log_le_log (by positivity) (by nlinarith)
  have hL : 1 ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have h4 : (4 : ℝ) ≤ N * u * T := by
      calc (4 : ℝ) = 1 * 2 * 2 := by norm_num
        _ ≤ N * u * T := mul_le_mul (mul_le_mul hN1 hu2 (by norm_num) (by linarith)) hT (by norm_num)
          (by positivity)
    have hl4 : 1 ≤ Real.log (N * u * T) := by
      have h5 : Real.log 4 ≤ Real.log (N * u * T) := Real.log_le_log (by norm_num) h4
      have h6 : 1 < Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        linarith [Real.log_two_gt_d9]
      linarith
    have hsq : 1 ≤ Real.log (N * u * T) ^ 2 := by nlinarith
    rw [le_div_iff₀ hT0]
    nlinarith [mul_le_mul hTu hsq (by norm_num) (by linarith)]
  have hlogNu : 0 ≤ Real.log (N * u) := by linarith
  have hErr1 : 1 ≤ Err N u T := by unfold Err; linarith
  have hErr2 : Real.log u ≤ Err N u T := by unfold Err; linarith
  have hErr3 : Real.log (2 * N) ≤ Err N u T := by unfold Err; linarith
  have hmain : ‖(R + c * vertInt χ u T') / c‖ ≤ Cs * Err N u T := by
    rw [norm_div, hcn, div_le_iff₀ (by positivity)]
    calc ‖R + c * vertInt χ u T'‖ ≤ Cs * Err N u T := hSe
      _ ≤ Cs * Err N u T * (2 * Real.pi) :=
        le_mul_of_one_le_right (by positivity) (by linarith [Real.pi_gt_three])
  have heps : ‖eps0 χ * (Real.log u : ℂ)‖ ≤ Real.log u := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlogu]
    exact mul_le_of_le_one_left hlogu.le hE1
  calc ‖(R + c * vertInt χ u T') / c + (Z - H 0) - eps0 χ * (Real.log u : ℂ) - del1 χ‖
      ≤ ‖(R + c * vertInt χ u T') / c‖ + ‖Z - H 0‖ + ‖eps0 χ * (Real.log u : ℂ)‖ + ‖del1 χ‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ Cs * Err N u T + (Cr * Real.log (2 * N) + S1 χ) + Real.log u + 1 := by
        gcongr
    _ ≤ (Cs + Cr + 3) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hCs hS1, mul_nonneg hCr hS1, mul_le_mul_of_nonneg_left hErr3 hCr]

end PI.EF
end
end

