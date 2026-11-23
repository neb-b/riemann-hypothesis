module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthDefs
section
noncomputable section

namespace PI.EF

def ZetaGrowth (C : ℝ) : Prop :=
  ∀ s : ℂ, -4 ≤ s.re → s.re ≤ 8 → ‖(s - 1) * riemannZeta s‖ ≤ C * (|s.im| + 2) ^ 7

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma
section
noncomputable section

namespace PI.EF

open Complex Filter Set

theorem norm_Gamma_le {w : ℂ} (hw : 0 < w.re) : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Real.Gamma_eq_integral hw, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx' : 0 < x := hx
  simp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx', Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simp

theorem norm_le_norm_of {a b : ℂ} (h1 : |a.re| ≤ |b.re|) (h2 : |a.im| ≤ |b.im|) : ‖a‖ ≤ ‖b‖ := by
  have h : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    have := sq_le_sq.mpr h1
    have := sq_le_sq.mpr h2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg a) (norm_nonneg b) two_ne_zero).mp h

theorem norm_sq_Gamma_half (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by
  set z : ℂ := 1 / 2 + t * I with hz
  have hconj : 1 - z = (starRingEnd ℂ) z := by
    apply Complex.ext
    · simp [hz]; norm_num
    · simp [hz]
  have h := Complex.Gamma_mul_Gamma_one_sub z
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at h
  have hs : Complex.sin (Real.pi * z) = ((Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
    have e : (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * I + Real.pi / 2 := by
      rw [hz]; push_cast; ring
    rw [e, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  rw [hs] at h
  have h' : normSq (Complex.Gamma z) = Real.pi / Real.cosh (Real.pi * t) := by exact_mod_cast h
  rw [← h', Complex.normSq_eq_norm_sq]

theorem half_line (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|) ≤ 3 := by
  have h := norm_sq_Gamma_half t
  have hpi := Real.pi_pos
  have hc : Real.exp (Real.pi * |t|) / 2 ≤ Real.cosh (Real.pi * t) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos hpi, Real.cosh_eq]
    have := Real.exp_pos (-(Real.pi * |t|))
    linarith
  have he : Real.exp (Real.pi / 2 * |t|) ^ 2 = Real.exp (Real.pi * |t|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hE := Real.exp_pos (Real.pi * |t|)
  have hsq : (‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|)) ^ 2 ≤ 9 := by
    rw [mul_pow, h, he, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have := Real.pi_lt_four
    nlinarith
  have h0 : 0 ≤ ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|) := by positivity
  by_contra hcon
  rw [not_le] at hcon
  nlinarith

def frobeniusStickelbergerDetMulSigmaCube (w : ℂ) : ℂ := Complex.Gamma w * Complex.exp (-(Real.pi / 2) * I * w) / (w + 1) ^ 5

theorem norm_twistedGamma (w : ℂ) :
    ‖frobeniusStickelbergerDetMulSigmaCube w‖ = ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im) / ‖w + 1‖ ^ 5 := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [norm_div, norm_mul, norm_pow, Complex.norm_exp]
  congr 3
  simp

theorem one_le_norm_add_one {w : ℂ} (hw : 0 ≤ w.re) : 1 ≤ ‖w + 1‖ := by
  have h := Complex.abs_re_le_norm (w + 1)
  have : |(w + 1).re| = w.re + 1 := by
    rw [Complex.add_re, Complex.one_re, abs_of_nonneg (by linarith)]
  linarith

theorem eq_re_add_im (w : ℂ) : w = (w.re : ℂ) + w.im * I := (Complex.re_add_im w).symm

theorem norm_twistedGamma_le_of_re_eq_half (w : ℂ) (hw : w.re = 1 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  rw [norm_twistedGamma]
  have h1 := one_le_norm_add_one (w := w) (by rw [hw]; norm_num)
  have e : w = 1 / 2 + (w.im : ℂ) * I := by
    conv_lhs => rw [eq_re_add_im w, hw]
    push_cast
    ring
  have h2 := half_line w.im
  rw [← e] at h2
  have h3 : Real.exp (Real.pi / 2 * w.im) ≤ Real.exp (Real.pi / 2 * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  have h4 : (1 : ℝ) ≤ ‖w + 1‖ ^ 5 := one_le_pow₀ h1
  rw [div_le_iff₀ (by linarith)]
  have h5 : ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im) ≤ 3 :=
    (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans h2
  nlinarith

theorem Gamma_add_five (z : ℂ) (hz : 0 < z.re) :
    Complex.Gamma (z + 5) = (z + 4) * ((z + 3) * ((z + 2) * ((z + 1) * (z * Complex.Gamma z)))) := by
  have ne : ∀ k : ℕ, z + k ≠ 0 := by
    intro k h
    have := congrArg Complex.re h
    simp at this
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have h0 := Complex.Gamma_add_one z (by simpa using ne 0)
  have h1 := Complex.Gamma_add_one (z + 1) (by simpa using ne 1)
  have h2 := Complex.Gamma_add_one (z + 2) (by simpa using ne 2)
  have h3 := Complex.Gamma_add_one (z + 3) (by simpa using ne 3)
  have h4 := Complex.Gamma_add_one (z + 4) (by simpa using ne 4)
  rw [show z + 5 = z + 4 + 1 by ring, h4, show z + 4 = z + 3 + 1 by ring, h3,
    show z + 3 = z + 2 + 1 by ring, h2, show z + 2 = z + 1 + 1 by ring, h1, h0]

theorem norm_twistedGamma_le_of_re_eq_eleven_halves (w : ℂ) (hw : w.re = 11 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  rw [norm_twistedGamma]
  have h1 := one_le_norm_add_one (w := w) (by rw [hw]; norm_num)
  set z : ℂ := 1 / 2 + (w.im : ℂ) * I with hz
  have e : w = z + 5 := by
    conv_lhs => rw [eq_re_add_im w, hw]
    rw [hz]
    push_cast
    ring
  have hzre : z.re = 1 / 2 := by simp [hz]
  have hzim : z.im = w.im := by simp [hz]
  have h2 := half_line w.im
  rw [← hz] at h2
  have h3 : Real.exp (Real.pi / 2 * w.im) ≤ Real.exp (Real.pi / 2 * |w.im|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  have hb : ∀ k : ℝ, 0 ≤ k → k ≤ 4 → ‖z + (k : ℂ)‖ ≤ ‖w + 1‖ := by
    intro k hk0 hk4
    apply norm_le_norm_of
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re, hzre, hw]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by norm_num)]
      linarith
    · simp [hzim]
  have b0 : ‖z‖ ≤ ‖w + 1‖ := by simpa using hb 0 (le_refl _) (by norm_num)
  have b1 : ‖z + 1‖ ≤ ‖w + 1‖ := by simpa using hb 1 (by norm_num) (by norm_num)
  have b2 : ‖z + 2‖ ≤ ‖w + 1‖ := by simpa using hb 2 (by norm_num) (by norm_num)
  have b3 : ‖z + 3‖ ≤ ‖w + 1‖ := by simpa using hb 3 (by norm_num) (by norm_num)
  have b4 : ‖z + 4‖ ≤ ‖w + 1‖ := by simpa using hb 4 (by norm_num) (by norm_num)
  have hG : ‖Complex.Gamma w‖ ≤ ‖w + 1‖ ^ 5 * ‖Complex.Gamma z‖ := by
    rw [e, Gamma_add_five z (by rw [hzre]; norm_num), ← e]
    simp only [norm_mul]
    set X := ‖w + 1‖
    have hX : 0 ≤ X := norm_nonneg _
    have hg := norm_nonneg (Complex.Gamma z)
    calc ‖z + 4‖ * (‖z + 3‖ * (‖z + 2‖ * (‖z + 1‖ * (‖z‖ * ‖Complex.Gamma z‖))))
        ≤ X * (X * (X * (X * (X * ‖Complex.Gamma z‖)))) := by gcongr
      _ = X ^ 5 * ‖Complex.Gamma z‖ := by ring
  have hpos : 0 < ‖w + 1‖ ^ 5 := by positivity
  rw [div_le_iff₀ hpos]
  calc ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * w.im)
      ≤ (‖w + 1‖ ^ 5 * ‖Complex.Gamma z‖) * Real.exp (Real.pi / 2 * |w.im|) :=
        mul_le_mul hG h3 (Real.exp_pos _).le (by positivity)
    _ = (‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * |w.im|)) * ‖w + 1‖ ^ 5 := by ring
    _ ≤ 3 * ‖w + 1‖ ^ 5 := mul_le_mul_of_nonneg_right h2 hpos.le

theorem diffContOnCl_twistedGamma : DiffContOnCl ℂ frobeniusStickelbergerDetMulSigmaCube (re ⁻¹' Ioo (1 / 2 : ℝ) (11 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  have hcl : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (11 / 2)) ⊆ re ⁻¹' Icc (1 / 2 : ℝ) (11 / 2) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
  intro w hw
  have hw' := hcl hw
  have hre : (1 / 2 : ℝ) ≤ w.re := hw'.1
  apply DifferentiableAt.differentiableWithinAt
  unfold frobeniusStickelbergerDetMulSigmaCube
  apply DifferentiableAt.div
  · apply DifferentiableAt.mul
    · apply Complex.differentiableAt_Gamma
      intro m h
      have := congrArg Complex.re h
      simp at this
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    · fun_prop
  · fun_prop
  · apply pow_ne_zero
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith

theorem norm_twistedGamma_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 11 / 2) : ‖frobeniusStickelbergerDetMulSigmaCube w‖ ≤ 3 := by
  refine PhragmenLindelof.vertical_strip diffContOnCl_twistedGamma ?_ norm_twistedGamma_le_of_re_eq_half norm_twistedGamma_le_of_re_eq_eleven_halves h1 h2
  refine ⟨1 / 2, ?_, Real.pi, ?_⟩
  · have := Real.pi_gt_three
    rw [lt_div_iff₀ (by norm_num)]
    linarith
  · apply Asymptotics.IsBigO.of_bound (max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)))
    apply Filter.eventually_inf_principal.mpr
    apply Filter.Eventually.of_forall
    intro z hz
    have hz1 : (1 / 2 : ℝ) < z.re := hz.1
    have hz2 : z.re < 11 / 2 := hz.2
    rw [norm_twistedGamma, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have a1 : ‖Complex.Gamma z‖ ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) :=
      (norm_Gamma_le (by linarith)).trans
        (Real.convexOn_Gamma.le_max_of_mem_Icc (by norm_num [Set.mem_Ioi]) (by norm_num [Set.mem_Ioi])
          ⟨hz1.le, hz2.le⟩)
    have a2 : Real.exp (Real.pi / 2 * z.im) ≤ Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) := by
      apply Real.exp_le_exp.mpr
      have q1 := Real.add_one_le_exp (1 / 2 * |z.im|)
      have q2 := le_abs_self z.im
      have q3 := abs_nonneg z.im
      have hpi := Real.pi_pos
      nlinarith
    have a3 : (1 : ℝ) ≤ ‖z + 1‖ ^ 5 := one_le_pow₀ (one_le_norm_add_one (by linarith))
    rw [div_le_iff₀ (by linarith)]
    have a4 : 0 ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) := (norm_nonneg _).trans a1
    calc ‖Complex.Gamma z‖ * Real.exp (Real.pi / 2 * z.im)
        ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) *
            Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) :=
          mul_le_mul a1 a2 (Real.exp_pos _).le a4
      _ ≤ max (Real.Gamma (1 / 2)) (Real.Gamma (11 / 2)) *
            Real.exp (Real.pi * Real.exp (1 / 2 * |z.im|)) * ‖z + 1‖ ^ 5 :=
          le_mul_of_one_le_right (mul_nonneg a4 (Real.exp_pos _).le) a3

theorem Gamma_decay {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 11 / 2) :
    ‖Complex.Gamma w‖ * Real.exp (Real.pi / 2 * |w.im|) ≤ 3 * ‖w + 1‖ ^ 5 := by
  have key : ∀ v : ℂ, 1 / 2 ≤ v.re → v.re ≤ 11 / 2 →
      ‖Complex.Gamma v‖ * Real.exp (Real.pi / 2 * v.im) ≤ 3 * ‖v + 1‖ ^ 5 := by
    intro v a b
    have h := norm_twistedGamma_le a b
    rw [norm_twistedGamma, div_le_iff₀ (by
      have := one_le_norm_add_one (w := v) (by linarith)
      positivity)] at h
    exact h
  rcases le_total 0 w.im with hi | hi
  · rw [abs_of_nonneg hi]
    exact key w h1 h2
  · rw [abs_of_nonpos hi]
    have h := key ((starRingEnd ℂ) w) (by simpa using h1) (by simpa using h2)
    rw [Complex.Gamma_conj, Complex.norm_conj, Complex.conj_im] at h
    have e : ‖(starRingEnd ℂ) w + 1‖ = ‖w + 1‖ := by
      rw [← Complex.norm_conj (w + 1), map_add (f := _), map_one]
    rw [e] at h
    exact h

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructA
section
noncomputable section

namespace PI.EF

open Complex Filter Topology Set

lemma logDeriv_local {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ)
    (hfin : analyticOrderAt f ρ ≠ ⊤) :
    ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s := by
  have hn : analyticOrderAt f ρ = (analyticOrderNatAt f ρ : ℕ∞) := (Nat.cast_analyticOrderNatAt hfin).symm
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderAt_eq_natCast).1 hn
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  have hU : ∀ᶠ z in 𝓝 ρ, (∀ᶠ w in 𝓝 z, f w = (w - ρ) ^ analyticOrderNatAt f ρ • g w) ∧
      g z ≠ 0 ∧ AnalyticAt ℂ g z :=
    hfg.eventually_nhds.and ((hg.continuousAt.eventually_ne hg0).and hg.eventually_analyticAt)
  filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with s hs hsne
  obtain ⟨hfs, hgs, hga⟩ := hs
  have hsr : s - ρ ≠ 0 := sub_ne_zero.2 hsne
  have hpow : (s - ρ) ^ analyticOrderNatAt f ρ ≠ 0 := pow_ne_zero _ hsr
  have hfs' : f s = (s - ρ) ^ analyticOrderNatAt f ρ * g s := by rw [hfs.self_of_nhds, smul_eq_mul]
  refine ⟨by rw [hfs']; exact mul_ne_zero hpow hgs, ?_⟩
  have hd : DifferentiableAt ℂ (fun w : ℂ => w - ρ) s := differentiableAt_id.sub_const ρ
  have hld : logDeriv f s = logDeriv (fun w => (w - ρ) ^ analyticOrderNatAt f ρ * g w) s := by
    rw [logDeriv_apply, logDeriv_apply,
      Filter.EventuallyEq.deriv_eq (hfs.mono fun w hw => by rw [hw, smul_eq_mul]), hfs']
  have hl : logDeriv (fun w : ℂ => w - ρ) s = 1 / (s - ρ) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  rw [hld, logDeriv_fun_mul (f := fun w => (w - ρ) ^ analyticOrderNatAt f ρ) s hpow hgs (hd.pow _)
    hga.differentiableAt, logDeriv_fun_pow hd, hl, logDeriv_apply]
  beta_reduce
  ring

theorem exists_regular_part {f : ℂ → ℂ} {K : Set ℂ} (hf : AnalyticOnNhd ℂ f K) (Z : Finset ℂ)
    (hZ0 : ∀ ρ ∈ Z, f ρ = 0) (hK : ∀ s ∈ K, f s = 0 → s ∈ Z)
    (hfin : ∀ ρ ∈ K, analyticOrderAt f ρ ≠ ⊤) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H K ∧ ∀ s ∈ K, f s ≠ 0 →
      logDeriv f s = H s + ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by
  classical
  have hloc : ∀ ρ, ρ ∈ K → ∃ k : ℂ → ℂ, AnalyticAt ℂ k ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, f s ≠ 0 ∧
      logDeriv f s = (analyticOrderNatAt f ρ : ℂ) / (s - ρ) + k s :=
    fun ρ hρ => logDeriv_local (hf ρ hρ) (hfin ρ hρ)
  choose! k hk hkev using hloc
  have hsumA : ∀ (W : Finset ℂ) (s0 : ℂ), s0 ∉ W →
      AnalyticAt ℂ (fun s => ∑ ρ ∈ W, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 := by
    intro W s0 hW
    have h := Finset.analyticAt_sum (𝕜 := ℂ) (c := s0) W
      (f := fun ρ (s : ℂ) => (analyticOrderNatAt f ρ : ℂ) / (s - ρ))
      (fun ρ hρ => analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.2 fun h => hW (h ▸ hρ)))
    convert h using 1
    ext s
    simp [Finset.sum_apply]
  let H : ℂ → ℂ := fun s => if s ∈ Z ∧ s ∈ K then
      k s s - ∑ ρ ∈ Z.erase s, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
    else logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
  refine ⟨H, ?_, ?_⟩
  · intro s0 hs0
    by_cases hz : s0 ∈ Z
    · have hRa : AnalyticAt ℂ
          (fun s => k s0 s - ∑ ρ ∈ Z.erase s0, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 :=
        (hk s0 hs0).sub (hsumA _ s0 (by simp))
      have h1 := hkev s0 hs0
      rw [eventually_nhdsWithin_iff] at h1
      have h2 : ∀ᶠ s in 𝓝 s0, s ∉ Z.erase s0 :=
        (Z.erase s0).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
      refine hRa.congr ?_
      filter_upwards [h1, h2] with s hs1 hs2
      by_cases hss : s = s0
      · subst hss
        simp only [H, if_pos (And.intro hz hs0)]
      · have hsZ : s ∉ Z := fun h => hs2 (Finset.mem_erase.2 ⟨hss, h⟩)
        obtain ⟨_, hl⟩ := hs1 hss
        simp only [H, hsZ, false_and, if_false]
        rw [hl, ← Finset.add_sum_erase Z _ hz]
        ring
    · have hf0 : f s0 ≠ 0 := fun h => hz (hK s0 hs0 h)
      have h2 : ∀ᶠ s in 𝓝 s0, s ∉ Z :=
        Z.finite_toSet.isClosed.isOpen_compl.mem_nhds (by simpa using hz)
      have hA : AnalyticAt ℂ (fun s => logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) s0 := by
        refine AnalyticAt.sub ?_ (hsumA Z s0 hz)
        have e : logDeriv f = fun s => deriv f s / f s := funext fun s => logDeriv_apply f s
        rw [e]
        exact (hf s0 hs0).deriv.div (hf s0 hs0) hf0
      refine hA.congr ?_
      filter_upwards [h2] with s hs
      simp only [H, hs, false_and, if_false]
  · intro s _ hfs
    have hsZ : s ∉ Z := fun h => hfs (hZ0 s h)
    simp only [H, hsZ, false_and, if_false]
    ring

lemma finite_zeros_of_compact {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ f ⁻¹' {0}).Finite := by
  by_contra hinf
  obtain ⟨z, _, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf hK Set.inter_subset_left
  have hfr : ∃ᶠ w in 𝓝[≠] z, f w = 0 := by
    rw [accPt_iff_frequently] at hacc
    rw [Filter.Frequently, eventually_nhdsWithin_iff]
    intro h
    apply hacc
    filter_upwards [h] with w hw
    rintro ⟨hne, hw'⟩
    exact hw hne hw'.2
  have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ z) hfr
  exact hx (h0 (Set.mem_univ x))

lemma order_ne_top_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) {x : ℂ} (hx : f x ≠ 0)
    (y : ℂ) : analyticOrderAt f y ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have h0 := AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (fun w _ => hf.analyticAt w) isPreconnected_univ (Set.mem_univ y) htop
  exact hx (h0 (Set.mem_univ x))

end PI.EF
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.NormLogDerivReflLe
section
noncomputable section

namespace PI.EF.Loc

open Complex Metric Set Filter Topology ComplexConjugate

def refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ := ((R : ℂ) ^ 2 - conj (ρ - s₀) * (z - s₀)) / R

lemma norm_refl_sphere {s₀ ρ z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere s₀ R) :
    ‖refl s₀ R ρ z‖ = ‖z - ρ‖ := by
  have hw : ‖z - s₀‖ = R := by rwa [mem_sphere_iff_norm] at hz
  have hR2 : (R : ℂ) ^ 2 = (z - s₀) * conj (z - s₀) := by
    rw [mul_conj, normSq_eq_norm_sq, hw]
    push_cast
    ring
  have hk : (z - s₀) * conj (z - s₀) - conj (ρ - s₀) * (z - s₀) = (z - s₀) * conj (z - ρ) := by
    simp only [map_sub]
    ring
  unfold refl
  rw [hR2, hk, norm_div, norm_mul, Complex.norm_conj, hw, Complex.norm_real, Real.norm_of_nonneg hR.le]
  field_simp

lemma le_norm_refl {s₀ ρ z : ℂ} {R R' : ℝ} (hR : 0 < R) (hρ : ρ ∈ closedBall s₀ R')
    (hz : z ∈ closedBall s₀ R) : R - R' ≤ ‖refl s₀ R ρ z‖ := by
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  have hw : ‖z - s₀‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hz
  unfold refl
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, le_div_iff₀ hR]
  have h1 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have h2 : ‖conj (ρ - s₀) * (z - s₀)‖ ≤ R' * R := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ha hw (norm_nonneg _) ((norm_nonneg _).trans ha)
  have h3 := norm_sub_norm_le ((R : ℂ) ^ 2) (conj (ρ - s₀) * (z - s₀))
  rw [h1] at h3
  nlinarith

lemma refl_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) : refl s₀ R ρ s₀ = R := by
  have h : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold refl
  rw [sub_self, mul_zero, sub_zero, pow_two, mul_div_assoc, div_self h, mul_one]

lemma hasDerivAt_refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) :
    HasDerivAt (refl s₀ R ρ) (-(conj (ρ - s₀) * 1) / R) z :=
  ((((hasDerivAt_id' z).sub_const s₀).const_mul (conj (ρ - s₀))).const_sub ((R : ℂ) ^ 2)).div_const (R : ℂ)

lemma differentiable_refl (s₀ : ℂ) (R : ℝ) (ρ : ℂ) : Differentiable ℂ (refl s₀ R ρ) :=
  fun z => (hasDerivAt_refl s₀ R ρ z).differentiableAt

lemma norm_logDeriv_refl_le {s₀ ρ z : ℂ} {R R' : ℝ} (hR'R : R' < R) (hR : 0 < R)
    (hρ : ρ ∈ closedBall s₀ R') (hz : z ∈ closedBall s₀ R) :
    ‖logDeriv (refl s₀ R ρ) z‖ ≤ R' / (R * (R - R')) := by
  have hpos : 0 < R - R' := sub_pos.mpr hR'R
  have hl := le_norm_refl hR hρ hz
  have hn : 0 < ‖refl s₀ R ρ z‖ := lt_of_lt_of_le hpos hl
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  rw [logDeriv_apply, (hasDerivAt_refl s₀ R ρ z).deriv, norm_div, norm_div, norm_neg, mul_one,
    Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hR.le, div_div,
    div_le_div_iff₀ (mul_pos hR hn) (mul_pos hR hpos)]
  have h4 := mul_le_mul ha hl hpos.le ((norm_nonneg _).trans ha)
  nlinarith

lemma logDeriv_prod_pow_mul {Z : Finset ℂ} {m : ℂ → ℕ} {φ : ℂ → ℂ → ℂ} {h : ℂ → ℂ} {s : ℂ}
    (hφ : ∀ ρ ∈ Z, φ ρ s ≠ 0) (hφd : ∀ ρ ∈ Z, DifferentiableAt ℂ (φ ρ) s) (hh : h s ≠ 0)
    (hhd : DifferentiableAt ℂ h s) :
    logDeriv (fun z => (∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) * h z) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (φ ρ) s) + logDeriv h s := by
  have hP : (∏ ρ ∈ Z, (φ ρ s) ^ (m ρ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)
  have hPd : DifferentiableAt ℂ (fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) s :=
    by
      have h5 := DifferentiableAt.finsetProd (f := fun ρ z => (φ ρ z) ^ (m ρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
      rwa [Finset.prod_fn] at h5
  rw [logDeriv_fun_mul (f := fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) (g := h) (x := s) hP hh hPd hhd]
  congr 1
  have h6 := logDeriv_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (s := Z) (x := s)
    (fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
  rw [Finset.prod_fn] at h6
  rw [h6]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  exact logDeriv_fun_pow (hφd ρ hρ) (m ρ)

lemma order_eq_of_factor {f h : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ} (hρ : ρ ∈ Z) {U : Set ℂ}
    (hU : U ∈ 𝓝 ρ) (hf : AnalyticAt ℂ f ρ) (hh : DifferentiableOn ℂ h U) (hhρ : h ρ ≠ 0)
    (hfac : ∀ z ∈ U, f z = (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z) :
    analyticOrderNatAt f ρ = m ρ := by
  have hha : AnalyticAt ℂ h ρ := hh.analyticAt hU
  have hg : AnalyticAt ℂ (fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z) ρ :=
    by
      have h7 := Finset.analyticAt_prod (𝕜 := ℂ) (Z.erase ρ) (f := fun ρ' z => (z - ρ') ^ (m ρ')) (c := ρ)
        (fun ρ' _ => by fun_prop)
      rw [Finset.prod_fn] at h7
      exact h7.mul hha
  have hg0 : (∏ ρ' ∈ Z.erase ρ, (ρ - ρ') ^ (m ρ')) * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' =>
      pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) hhρ
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hf.analyticOrderAt_eq_natCast]
    refine ⟨_, hg, hg0, ?_⟩
    filter_upwards [hU] with z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Z (fun ρ' => (z - ρ') ^ (m ρ')) hρ, smul_eq_mul, mul_assoc]
  simp [analyticOrderNatAt, hord]

end PI.EF.Loc
end
end

