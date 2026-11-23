module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousIsBigORpowLipschitzProductKernel
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

theorem mul_im_pos_of_sign_mul_pos {w : ℂ} {t : ℝ} (h : 0 < (SignType.sign w.im : ℝ) * t) :
    0 < t * w.im := by
  rcases lt_trichotomy w.im 0 with hw | hw | hw
  · rw [sign_neg hw] at h
    simp at h
    nlinarith
  · rw [hw, sign_zero] at h
    simp at h
  · rw [sign_pos hw] at h
    simp at h
    positivity

theorem norm_lipschitzOneVariableKernel_le (k : ℕ) (w : ℂ) (t : ℝ) :
    ‖phi1 k w t‖ ≤ |t| ^ (k - 1) * Real.exp (-(2 * Real.pi * |w.im|) * |t|) := by
  unfold phi1
  split_ifs with h
  · have hp := mul_im_pos_of_sign_mul_pos h
    have habs : |t| * |w.im| = t * w.im := by rw [← abs_mul]; exact abs_of_pos hp
    have hre : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * w).re = -(2 * Real.pi * |w.im|) * |t| := by
      simp [Complex.mul_re]
      linear_combination (-2 * Real.pi) * habs
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  · simp only [norm_zero]
    positivity

theorem abs_pow_mul_exp_le (n : ℕ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t| ^ n * Real.exp (-a * |t|) ≤ (n.factorial * (2 / a) ^ n) * Real.exp (-(a / 2) * |t|) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * |t|) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at h
  have h1 : |t| ^ n ≤ n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|) := by
    calc |t| ^ n = (2 / a) ^ n * (a / 2 * |t|) ^ n := by
          rw [← mul_pow]; congr 1; field_simp
      _ ≤ (2 / a) ^ n * (Real.exp (a / 2 * |t|) * n.factorial) := by gcongr
      _ = _ := by ring
  calc |t| ^ n * Real.exp (-a * |t|)
      ≤ (n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|)) * Real.exp (-a * |t|) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem continuous_lipschitzOneVariableKernel {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w.im ≠ 0) : Continuous (phi1 k w) := by
  have hg : Continuous fun t : ℝ =>
      ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) := by fun_prop
  show Continuous fun t => if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) else 0
  refine continuous_if (fun a ha => ?_) hg.continuousOn continuous_const.continuousOn
  have h0 := frontier_lt_subset_eq (continuous_const (y := (0 : ℝ)))
    (continuous_const.mul continuous_id (f := fun _ : ℝ => (SignType.sign w.im : ℝ))) ha
  simp only [Set.mem_setOf_eq, id] at h0
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 h0.symm with h | h
    · exfalso
      rcases lt_trichotomy w.im 0 with h' | h' | h'
      · rw [sign_neg h'] at h; norm_num at h
      · exact hw h'
      · rw [sign_pos h'] at h; norm_num at h
    · exact h
  subst ha0
  have : k - 1 ≠ 0 := by omega
  simp [this]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

theorem norm_le_sum_abs {F : Type} [Field F] [NumberField F] (v : RSp F) :
    ‖v‖ ≤ ∑ τ, |v τ| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun τ => |v τ|) fun _ _ => abs_nonneg _

theorem continuous_and_isBigO_rpow_Phi (F : Type) [Field F] [NumberField F] (k : ℕ) (hk : 2 ≤ k)
    (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  refine ⟨?_, fun b => ?_⟩
  · unfold Phi
    exact continuous_finsetProd _ fun τ _ =>
      (continuous_lipschitzOneVariableKernel hk (hz τ)).comp ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ τ, c ≤ 2 * Real.pi * |(z τ).im| / 2 := by
    rcases isEmpty_or_nonempty (F →+* ℝ) with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ0, hτ0⟩ := Finite.exists_min (fun τ => 2 * Real.pi * |(z τ).im| / 2)
      exact ⟨_, by have := abs_pos.2 (hz τ0); positivity, hτ0⟩
  set K : ℝ := ∏ τ, (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) with hK
  have hbound : ∀ v : RSp F, ‖Phi k z v‖ ≤ K * Real.exp (-c * ‖v‖) := by
    intro v
    have hfac : ∀ τ, ‖phi1 k (z τ) (v τ)‖ ≤
        (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|) := by
      intro τ
      have ha : 0 < 2 * Real.pi * |(z τ).im| := by have := abs_pos.2 (hz τ); positivity
      refine (norm_lipschitzOneVariableKernel_le k (z τ) (v τ)).trans ((abs_pow_mul_exp_le (k - 1) ha (v τ)).trans ?_)
      gcongr
      have := hcle τ
      nlinarith [abs_nonneg (v τ)]
    calc ‖Phi k z v‖ = ∏ τ, ‖phi1 k (z τ) (v τ)‖ := by unfold Phi; rw [norm_prod]
      _ ≤ ∏ τ, ((((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => hfac τ
      _ = K * Real.exp (-c * ∑ τ, |v τ|) := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
      _ ≤ K * Real.exp (-c * ‖v‖) := by
        have hK0 : 0 ≤ K := Finset.prod_nonneg fun τ _ => by positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [norm_le_sum_abs v])) hK0
  have h1 : Phi k z =O[Filter.cocompact (RSp F)] fun v : RSp F => Real.exp (-c * ‖v‖) :=
    Asymptotics.IsBigO.of_bound K (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound v)
  have h2 : (fun v : RSp F => Real.exp (-c * ‖v‖)) =O[Filter.cocompact (RSp F)]
      fun v : RSp F => ‖v‖ ^ (-b) :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-b)).isBigO.comp_tendsto tendsto_norm_cocompact_atTop
  exact h1.trans h2

end GlobalTheory.LipschitzTR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountGrowthExponentialRadii
section
open Filter Topology

namespace GlobalTheory

theorem hsGrowth_log_add_div_tendsto (D : ℕ) :
    Tendsto (fun m : ℕ => Real.log ((m : ℝ) + D) / m) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-(D : ℝ)) 1 one_ne_zero).comp
    (tendsto_atTop_add_const_right _ (D : ℝ) tendsto_natCast_atTop_atTop)
  refine h.congr (fun m => ?_)
  simp

theorem hsGrowth_log_floor_le {Y : ℝ} (hY : 0 < Y) :
    Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log 3 + |Real.log Y| := by
  have h3 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)
  rcases lt_or_ge Y 1 with h | h
  · have : ⌊Y⌋₊ = 0 := Nat.floor_eq_zero.mpr h
    simp only [this, mul_zero, zero_add, Nat.cast_one, Real.log_one]
    linarith [abs_nonneg (Real.log Y)]
  · have h1 : ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * Y := by
      push_cast
      have := Nat.floor_le hY.le
      linarith
    calc Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (3 * Y) := Real.log_le_log (by positivity) h1
      _ = Real.log 3 + Real.log Y := Real.log_mul (by norm_num) hY.ne'
      _ ≤ Real.log 3 + |Real.log Y| := by linarith [le_abs_self (Real.log Y)]

theorem hsGrowth_exp_radius : ∀ (D e δ : ℕ) (N : ℕ → ℝ → ℕ) (κ t : ℝ), 0 < e → 0 < κ → κ ≤ 1 → 0 < t → (∀ m, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' → N m R ≤ N m R') → (∀ s : ℕ, s < e → ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, δ / ((e : ℝ) ^ D * D.factorial) * t - ε ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ∧ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ δ / ((e : ℝ) ^ D * D.factorial) * (t - Real.log κ / e) + ε := by
  intro D e δ N κ t he hκ hκ1 ht hmono h ε hε
  have h' : ∀ s : ℕ, ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ (s < e → ∀ (q : ℕ) (R : ℝ), 0 ≤ R →
      (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧
      N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) := by
    intro s
    by_cases hs : s < e
    · obtain ⟨c, c', C, C', h1, h2, h3⟩ := h s hs
      exact ⟨c, c', C, C', h1, h2, fun _ => h3⟩
    · exact ⟨0, 0, 1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose c c' C C' hC hC' hb using h'
  set L : ℝ := δ / ((e : ℝ) ^ D * D.factorial) with hL
  have hdiv : ∀ q s, s < e → (e * q + s) / e = q ∧ (e * q + s) % e = s := by
    intro q s hs
    constructor
    · rw [add_comm, Nat.add_mul_div_left _ _ he, Nat.div_eq_of_lt hs, zero_add]
    · rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have hlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D)
      atTop (𝓝 L) := by
    refine GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e - c (m % e) + D).choose D) he ?_
    intro s hs
    refine ⟨c s, 0, fun q => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hdiv (q + c s) s hs
      simp only [h1, h2, Nat.add_sub_cancel, le_refl]
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [h1, h2, add_zero]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))
  have hup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D)
      atTop (𝓝 L) := by
    refine GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e δ (fun m => δ * (m / e + c' (m % e) + D).choose D) he ?_
    intro s hs
    refine ⟨0, c' s, fun q => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [add_zero, h1, h2]
      exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ (by omega))
    · obtain ⟨h1, h2⟩ := hdiv q s hs
      simp only [h1, h2, le_refl]
  set B : ℝ := ∑ s ∈ Finset.range e, |Real.log (C s)| with hBdef
  set B' : ℝ := ∑ s ∈ Finset.range e, |Real.log (C' s)| with hB'def
  set P : ℝ := ∑ s ∈ Finset.range e, (c' s : ℝ) with hPdef
  set M : ℕ := ∑ s ∈ Finset.range e, c s with hMdef
  have hB : ∀ s, s < e → Real.log (C s) ≤ B := fun s hs => (le_abs_self _).trans
    (Finset.single_le_sum (f := fun s => |Real.log (C s)|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.mpr hs))
  have hB' : ∀ s, s < e → |Real.log (C' s)| ≤ B' := fun s hs =>
    Finset.single_le_sum (f := fun s => |Real.log (C' s)|) (fun i _ => abs_nonneg _)
      (Finset.mem_range.mpr hs)
  have hP : ∀ s, s < e → (c' s : ℝ) ≤ P := fun s hs =>
    Finset.single_le_sum (f := fun s => (c' s : ℝ)) (fun i _ => Nat.cast_nonneg _)
      (Finset.mem_range.mpr hs)
  have hlk : Real.log κ ≤ 0 := Real.log_nonpos hκ.le hκ1

  have hlowE : ∀ᶠ m : ℕ in atTop,
      ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
        (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) ≤
      Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) := by
    filter_upwards [eventually_ge_atTop (e * M + 1)] with m hm
    have hm0' : 0 < m := Nat.lt_of_lt_of_le (Nat.succ_pos _) hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm0'
    set s := m % e with hs_def
    have hse : s < e := Nat.mod_lt _ he
    have hcm : c s ≤ m / e := by
      have : M ≤ m / e := by
        rw [Nat.le_div_iff_mul_le he]
        rw [mul_comm]; linarith
      exact (Finset.single_le_sum (f := c) (fun i _ => Nat.zero_le _)
        (Finset.mem_range.mpr hse)).trans this
    set q := m / e - c s with hq
    have hqm : q ≤ m := (Nat.sub_le _ _).trans (Nat.div_le_self _ _)
    have hmq : e * (q + c s) + s = m := by
      rw [hq, Nat.sub_add_cancel hcm]; exact Nat.div_add_mod m e
    have hKpos : 0 < (q + D).choose D := Nat.choose_pos (by omega)
    have hKpos' : (0 : ℝ) < ((q + D).choose D : ℝ) := by exact_mod_cast hKpos
    have hCs := hC s
    set R : ℝ := Real.exp (t * m) / (C s * ((q + D).choose D : ℝ)) with hR
    have hRpos : 0 < R := by rw [hR]; positivity
    have hCKR : C s * ((q + D).choose D : ℝ) * R = Real.exp (t * m) := by
      rw [hR]; field_simp
    have hb1 := (hb s hse q R hRpos.le).1
    rw [hmq, hCKR] at hb1
    have hK1 : Real.log ((q + D).choose D : ℝ) ≤ D * Real.log ((m : ℝ) + D) := by
      rw [← Real.log_pow]
      apply Real.log_le_log hKpos'
      have : (q + D).choose D ≤ (m + D) ^ D :=
        (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
      exact_mod_cast this
    set K := (q + D).choose D with hK
    have hlogN : (δ * K : ℝ) * Real.log R ≤ Real.log (N m (Real.exp (t * m))) := by
      have h1 : R ≤ ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        have := Nat.lt_floor_add_one R
        have := Nat.cast_nonneg (α := ℝ) ⌊R⌋₊
        linarith
      have h2 : ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) ≤ N m (Real.exp (t * m)) := by
        exact_mod_cast hb1
      have h3 : (0 : ℝ) < (((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ) : ℝ) := by positivity
      calc (δ * K : ℝ) * Real.log R ≤ (δ * K : ℝ) * Real.log ((2 * ⌊R⌋₊ + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log hRpos h1) (by positivity)
        _ = Real.log ((((2 * ⌊R⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) := by
            rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
        _ ≤ _ := Real.log_le_log h3 h2
    have hlogR : t * m - B - D * Real.log ((m : ℝ) + D) ≤ Real.log R := by
      rw [hR, Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp,
        Real.log_mul hCs.ne' hKpos'.ne']
      linarith [hB s hse]
    have key : (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) ≤
        Real.log (N m (Real.exp (t * m))) :=
      (mul_le_mul_of_nonneg_left hlogR (by positivity)).trans hlogN
    rw [le_div_iff₀ (by positivity)]
    calc ((δ * K : ℕ) : ℝ) / (m : ℝ) ^ D * (t - (B / m + D * (Real.log ((m : ℝ) + D) / m))) *
          (m : ℝ) ^ (D + 1) = (δ * K : ℝ) * (t * m - B - D * Real.log ((m : ℝ) + D)) := by
          push_cast; field_simp; ring
      _ ≤ _ := key

  have hupE : ∀ᶠ m : ℕ in atTop, Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤
      ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
        ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    set s := m % e with hs_def
    have hse : s < e := Nat.mod_lt _ he
    set q := m / e with hq
    have hmq : e * q + s = m := Nat.div_add_mod m e
    have hCs := hC' s
    set Y : ℝ := C' s * Real.exp (t * m) / κ ^ (q + c' s) with hY
    have hYpos : 0 < Y := by rw [hY]; positivity
    have hb2 := (hb s hse q (Real.exp (t * m)) (Real.exp_pos _).le).2
    rw [hmq, ← hY] at hb2
    set K := (q + c' s + D).choose D with hK
    have hlogN : Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|) := by
      have h0 : 0 ≤ Real.log 3 + |Real.log Y| := by
        have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3); positivity
      rcases Nat.eq_zero_or_pos (N m (Real.exp (t * m))) with hN | hN
      · rw [hN, Nat.cast_zero, Real.log_zero]; positivity
      · calc Real.log (N m (Real.exp (t * m)))
            ≤ Real.log ((((2 * ⌊Y⌋₊ + 1) ^ (δ * K) : ℕ)) : ℝ) :=
              Real.log_le_log (by exact_mod_cast hN) (by exact_mod_cast hb2)
          _ = (δ * K : ℝ) * Real.log ((2 * ⌊Y⌋₊ + 1 : ℕ) : ℝ) := by
              rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hsGrowth_log_floor_le hYpos) (by positivity)
    have hlogY : |Real.log Y| ≤ B' + t * m + (m / e + P) * (-Real.log κ) := by
      rw [hY, Real.log_div (by positivity) (by positivity),
        Real.log_mul hCs.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow]
      have hq1 : ((q : ℕ) : ℝ) ≤ (m : ℝ) / e := Nat.cast_div_le
      have hc1 := hP s hse
      have hx : ((q : ℝ) + c' s) * (-Real.log κ) ≤ ((m : ℝ) / e + P) * (-Real.log κ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have hx0 : 0 ≤ ((q : ℝ) + c' s) * (-Real.log κ) := mul_nonneg (by positivity) (by linarith)
      have ha := abs_le.mp (hB' s hse)
      have htm : 0 ≤ t * m := by positivity
      rw [abs_le]; push_cast; constructor <;> nlinarith
    rw [div_le_iff₀ (by positivity)]
    calc Real.log (N m (Real.exp (t * m))) ≤ (δ * K : ℝ) * (Real.log 3 + |Real.log Y|) := hlogN
      _ ≤ (δ * K : ℝ) * (Real.log 3 + (B' + t * m + (m / e + P) * (-Real.log κ))) := by
          gcongr
      _ = ((δ * K : ℕ) : ℝ) / (m : ℝ) ^ D *
            ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e)) * (m : ℝ) ^ (D + 1) := by
          push_cast; field_simp; ring

  have hLlow : Tendsto (fun m : ℕ => ((δ * (m / e - c (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
      (t - (B / m + D * (Real.log ((m : ℝ) + D) / m)))) atTop (𝓝 (L * t)) := by
    have h0 : Tendsto (fun m : ℕ => B / (m : ℝ) + D * (Real.log ((m : ℝ) + D) / m)) atTop (𝓝 0) := by
      have := (tendsto_const_div_atTop_nhds_zero_nat B).add
        ((hsGrowth_log_add_div_tendsto D).const_mul (D : ℝ))
      simpa only [mul_zero, add_zero] using this
    have := hlow.mul ((tendsto_const_nhds (x := t)).sub h0)
    simpa only [sub_zero] using this
  have hLup : Tendsto (fun m : ℕ => ((δ * (m / e + c' (m % e) + D).choose D : ℕ) : ℝ) / (m : ℝ) ^ D *
      ((Real.log 3 + B' + P * (-Real.log κ)) / m + (t - Real.log κ / e))) atTop
      (𝓝 (L * (t - Real.log κ / e))) := by
    have := hup.mul ((tendsto_const_div_atTop_nhds_zero_nat (Real.log 3 + B' + P * (-Real.log κ))).add
      (tendsto_const_nhds (x := t - Real.log κ / e)))
    simpa only [zero_add] using this
  have e1 := hLlow.eventually (lt_mem_nhds (show L * t - ε < L * t by linarith))
  have e2 := hLup.eventually (gt_mem_nhds
    (show L * (t - Real.log κ / e) < L * (t - Real.log κ / e) + ε by linarith))
  filter_upwards [e1, e2, hlowE, hupE] with m h1 h2 h3 h4
  exact ⟨by linarith, by linarith⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveDegreeUnique
section
open IsLocalRing Polynomial

namespace GlobalTheory.EtalePolyDvr

theorem isDiscreteValuationRing_atPrime_of_etale_polynomial :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (p : Ideal A) [p.IsPrime], p.height = 1 →
    P.comap (algebraMap A[X] (Localization.AtPrime Q)) = p.map (Polynomial.C : A →+* A[X]) →
    (∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P)) ∧
      ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
  intro A _ _ _ _ E _ _ _ _ _ Q _ P _ p _ hp hP
  classical
  haveI hE : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing A[X] E
  haveI hR : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ hE
  haveI hLPn : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ hR
  let Q' : Ideal E := P.comap (algebraMap E (Localization.AtPrime Q))
  haveI hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
  haveI hLoc : IsLocalization.AtPrime (Localization.AtPrime P) Q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl
      (Localization.AtPrime P) P
  let e : Localization.AtPrime Q' ≃ₐ[E] Localization.AtPrime P :=
    IsLocalization.algEquiv Q'.primeCompl _ _
  haveI hAp : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  haveI hApd : IsDiscreteValuationRing (Localization.AtPrime p) :=
    GlobalTheory.isDiscreteValuationRing_of_height_eq_one p hp _
  have hAL : ∀ a : A, algebraMap A (Localization.AtPrime Q') a =
      algebraMap E (Localization.AtPrime Q') (algebraMap A E a) := fun a =>
    IsScalarTower.algebraMap_apply A E _ a
  have hALP : ∀ a : A, algebraMap A (Localization.AtPrime P) a =
      algebraMap E (Localization.AtPrime P) (algebraMap A E a) := fun a => by
    rfl
  have he : ∀ a : A, e (algebraMap A (Localization.AtPrime Q') a) =
      algebraMap A (Localization.AtPrime P) a := by
    intro a; rw [hAL, hALP, e.commutes]
  have hunder : Q'.comap (algebraMap A[X] E) = p.map C := by
    rw [← hP]
    show Ideal.comap _ (Ideal.comap _ P) = _
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  have hunderA : ∀ a : A, algebraMap A E a ∈ Q' ↔ a ∈ p := by
    intro a
    rw [IsScalarTower.algebraMap_apply A A[X] E, ← Ideal.mem_comap, hunder,
      Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
    refine ⟨fun h => by simpa using h 0, fun h n => ?_⟩
    rw [Polynomial.coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem
  have hcomp : (algebraMap A[X] (Localization.AtPrime Q')).comp C =
      algebraMap A (Localization.AtPrime Q') := by
    ext a
    simp only [RingHom.comp_apply]
    rw [hAL, IsScalarTower.algebraMap_apply A A[X] E, Polynomial.algebraMap_eq,
      IsScalarTower.algebraMap_apply A[X] E (Localization.AtPrime Q')]
  have hun : Algebra.IsUnramifiedAt A[X] Q' := inferInstance
  let p0 : Ideal A[X] := Q'.under A[X]
  let := Localization.AtPrime.algebraOfLiesOver p0 Q'
  have hm := ((Algebra.isUnramifiedAt_iff_map_eq A[X] p0 Q').mp hun).2
  have hp0 : p0 = p.map C := hunder
  have hunit : ∀ a : A, a ∉ p → IsUnit (algebraMap A (Localization.AtPrime Q') a) := by
    intro a ha
    by_contra h
    apply ha
    rw [← hunderA, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q') Q', ← hAL]
    exact h
  haveI hflatE : Module.Flat A E := Module.Flat.trans A A[X] E
  haveI hflatL : Module.Flat A (Localization.AtPrime Q') := Module.Flat.trans A E _
  have key : ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
      ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) ∧
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
    intro π hπ
    have hπp : π ∈ p := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p π]
      exact hπ.not_isUnit
    have hπ0 : π ≠ 0 := by rintro rfl; exact hπ.ne_zero (map_zero _)
    have hmAp := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπ
    have hmL : maximalIdeal (Localization.AtPrime Q') =
        Ideal.span {algebraMap A (Localization.AtPrime Q') π} := by
      rw [← hm, hp0, Ideal.map_map, hcomp]
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        have h1 : algebraMap A (Localization.AtPrime p) a ∈ maximalIdeal _ :=
          (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p a).mpr ha
        rw [hmAp, Ideal.mem_span_singleton'] at h1
        obtain ⟨c, hc⟩ := h1
        obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
        have h2 : algebraMap A (Localization.AtPrime p) (a * s) =
            algebraMap A (Localization.AtPrime p) (b * π) := by
          rw [map_mul, map_mul, ← hc, mul_right_comm, IsLocalization.mk'_spec]
        obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists p.primeCompl _).mp h2
        have hts : (t : A) * s ∉ p := p.primeCompl.mul_mem t.2 s.2
        rw [Ideal.mem_comap, Ideal.mem_span_singleton,
          ← (hunit _ hts).dvd_mul_right, ← map_mul]
        have h3 : a * ((t : A) * s) = π * ((t : A) * b) := by linear_combination ht
        rw [h3, map_mul]
        exact dvd_mul_right _ _
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact Ideal.mem_map_of_mem _ hπp
    have hreg : ∀ x : Localization.AtPrime Q', algebraMap A _ π * x = 0 → x = 0 := by
      intro x hx
      have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Localization.AtPrime Q')
        (mem_nonZeroDivisors_of_ne_zero hπ0)
      exact this (show π • x = π • (0 : Localization.AtPrime Q') by
        rw [smul_zero, Algebra.smul_def, hx])
    have hmem : ∀ y : Localization.AtPrime Q',
        e y ∈ maximalIdeal (Localization.AtPrime P) ↔ y ∈ maximalIdeal _ := by
      intro y
      simp only [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
    have hmLP : maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap A (Localization.AtPrime P) π} := by
      ext x
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [hmem, hmL, Ideal.mem_span_singleton, Ideal.mem_span_singleton, ← he, map_dvd_iff]
    have hregP : ∀ x : Localization.AtPrime P, algebraMap A _ π * x = 0 → x = 0 := by
      intro x hx
      obtain ⟨y, rfl⟩ := e.surjective x
      rw [← he, ← map_mul, map_eq_zero_iff _ e.injective] at hx
      rw [hreg y hx, map_zero]
    exact GlobalTheory.Pat.dvr_of_maximalIdeal_eq_span hmLP hregP
  refine ⟨?_, fun π hπ => (key π hπ).2.2⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime p)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl ϖ
  have ha : Irreducible (algebraMap A (Localization.AtPrime p) a) := by
    have h := IsLocalization.mk'_spec (Localization.AtPrime p) a s
    rw [← h]
    exact (irreducible_mul_isUnit (IsLocalization.map_units _ s)).mpr hϖ
  obtain ⟨hd, hdvr, -⟩ := key a ha
  exact ⟨hd, hdvr⟩

end GlobalTheory.EtalePolyDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosNatSmulMemOfSpanningNumberFieldLatticeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_nat_smul_mem_of_spanning_numberField_lattice : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)), Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∀ v : Fin r → E, ∃ q : ℕ, 0 < q ∧ (q : E) • v ∈ Λ := by
  first | exact @GlobalTheory.exists_pos_nat_smul_mem_of_span_eq_top | exact GlobalTheory.exists_pos_nat_smul_mem_of_span_eq_top | (intros; apply GlobalTheory.exists_pos_nat_smul_mem_of_span_eq_top <;> assumption)
end

