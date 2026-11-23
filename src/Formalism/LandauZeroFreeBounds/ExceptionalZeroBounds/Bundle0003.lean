module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Positivity
section
open Complex LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma negLogDeriv_eq_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : negLD χ s = LSeries (↗χ * ↗Λ) s := by
  unfold negLD
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  ring

lemma hasSum_re_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : HasSum (fun n ↦ (term (↗χ * ↗Λ) s n).re) (negLD χ s).re := by
  rw [negLogDeriv_eq_LSeries χ hs]
  exact Complex.hasSum_re (DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs).hasSum

lemma term_ofReal_add_mul_I {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ u : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) ((σ : ℂ) + u * I) n =
      ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * (χ n / (n : ℂ) ^ ((u : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_def, if_neg hn, Complex.cpow_add _ _ hn']
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    rw [div_mul_div_comm]
    ring

lemma term_ofReal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ) (n : ℕ) :
    term (↗χ * ↗Λ) (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) * χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · rw [LSeries.term_def, if_neg hn]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    push_cast
    simp only [Pi.mul_apply]
    ring

lemma vonMangoldt_div_rpow_nonneg (σ : ℝ) (n : ℕ) : 0 ≤ Λ n / (n : ℝ) ^ σ :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

lemma term_three_four_one_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + 4 * (term (↗χ * ↗Λ) ((σ : ℂ) + t * I) n).re
      + (term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal_add_mul_I, term_ofReal_add_mul_I]
  by_cases hu : IsUnit (n : ZMod q)
  · have h1 : (1 : DirichletCharacter ℂ q) n = 1 := MulChar.one_apply hu
    have h2 : (χ ^ 2) n = (χ n) ^ 2 := MulChar.pow_apply' χ two_ne_zero _
    have hχ1 : ‖χ n‖ = 1 := by
      have := DirichletCharacter.unit_norm_eq_one χ hu.unit
      rwa [IsUnit.unit_spec] at this
    have hc : ‖(n : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
    have hc2 : (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = ((n : ℂ) ^ ((t : ℂ) * I)) ^ 2 := by
      rw [← Complex.cpow_nat_mul]
      push_cast
      ring_nf
    set w := χ n / (n : ℂ) ^ ((t : ℂ) * I) with hw_def
    have hw : ‖w‖ = 1 := by rw [hw_def, norm_div, hχ1, hc, div_one]
    have hw2 : (χ ^ 2) n / (n : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) = w ^ 2 := by
      rw [h2, hc2, div_pow]
    rw [h1, hw2]
    have hn1 : w.re * w.re + w.im * w.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]
      norm_num
    have hre : (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
      rw [sq, Complex.mul_re]
      nlinarith [hn1]
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre, Complex.one_re]
    nlinarith [mul_nonneg ha (sq_nonneg (1 + w.re))]
  · have h1 : (1 : DirichletCharacter ℂ q) n = 0 := MulChar.map_nonunit _ hu
    have h2 : χ n = 0 := MulChar.map_nonunit _ hu
    have h3 : (χ ^ 2) n = 0 := MulChar.map_nonunit _ hu
    simp [h1, h2, h3]

lemma eq_one_or_eq_neg_one_of_sq_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    {n : ℕ} (hu : IsUnit (n : ZMod q)) : χ n = 1 ∨ χ n = -1 := by
  have h : χ n * χ n = 1 := by
    rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply hu]
  exact mul_self_eq_one_iff.mp h

lemma term_one_add_real_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ * ↗Λ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    rcases eq_one_or_eq_neg_one_of_sq_eq_one χ hχ hu with h | h <;> rw [h] <;>
      simp only [Complex.re_ofReal_mul, Complex.one_re, Complex.neg_re] <;> linarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

lemma term_two_real_nonneg {q : ℕ} [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (σ : ℝ) (n : ℕ) :
    0 ≤ (term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + (term (↗χ₁ * ↗Λ) (σ : ℂ) n).re + (term (↗χ₂ * ↗Λ) (σ : ℂ) n).re
      + (term (↗(χ₁ * χ₂) * ↗Λ) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  have ha := vonMangoldt_div_rpow_nonneg σ n
  rw [term_ofReal, term_ofReal, term_ofReal,
    term_ofReal, MulChar.mul_apply]
  by_cases hu : IsUnit (n : ZMod q)
  · rw [MulChar.one_apply hu]
    rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₁ h₁ hu with h | h <;>
      rcases eq_one_or_eq_neg_one_of_sq_eq_one χ₂ h₂ hu with h' | h' <;> rw [h, h'] <;>
      generalize Λ n / (n : ℝ) ^ σ = a at ha ⊢ <;>
      simp [Complex.re_ofReal_mul] <;> linarith
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    simp

theorem negLogDerivPositivity : Positivity := by
  intro q _ σ hσ
  have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have H1 : ∀ χ : DirichletCharacter ℂ q, HasSum (fun n ↦ (term (↗χ * ↗Λ) (σ : ℂ) n).re)
      (negLD χ (σ : ℂ)).re := fun χ => hasSum_re_term χ hs1
  refine ⟨fun χ t => ?_, fun χ hχ => ?_, fun χ₁ χ₂ h₁ h₂ => ?_⟩
  · have hs2 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
    have hs3 : 1 < ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I).re := by simpa using hσ
    have HS := (((H1 1).mul_left 3).add ((hasSum_re_term χ hs2).mul_left 4)).add
      (hasSum_re_term (χ ^ 2) hs3)
    have e : ((σ : ℂ) + 2 * t * I) = (σ : ℂ) + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [e]
    exact HasSum.nonneg (fun n => term_three_four_one_nonneg χ σ t n) HS
  · exact HasSum.nonneg (fun n => term_one_add_real_nonneg χ hχ σ n) ((H1 1).add (H1 χ))
  · exact HasSum.nonneg (fun n => term_two_real_nonneg χ₁ χ₂ h₁ h₂ σ n)
      ((((H1 1).add (H1 χ₁)).add (H1 χ₂)).add (H1 (χ₁ * χ₂)))

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.RealLargeTOf
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma re_one_div_sub_zero_pos {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (σ t : ℝ) (hσ : 1 < σ) :
    0 < (1 / ((σ : ℂ) + t * I - ρ)).re := by
  have hre : ρ.re < 1 := by
    by_contra hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ) (not_lt.mp hc) hρ
  have hwre : ((σ : ℂ) + t * I - ρ).re = σ - ρ.re := by simp
  have hw0 : (σ : ℂ) + t * I - ρ ≠ 0 := fun h => by
    have h' : ((σ : ℂ) + t * I - ρ).re = 0 := by rw [h, Complex.zero_re]
    linarith
  rw [one_div, Complex.inv_re]
  exact div_pos (by rw [hwre]; linarith) (Complex.normSq_pos.mpr hw0)

lemma re_one_div_ofReal_add_mul_I (x y : ℝ) :
    (1 / ((x : ℂ) + y * I)).re = x / (x ^ 2 + y ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_add_mul_I]
  simp

lemma two_le_mul_abs_add_two (q : ℕ) [NeZero q] (t : ℝ) : 2 ≤ (q : ℝ) * (|t| + 2) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  nlinarith [abs_nonneg t]

lemma log_mul_abs_two_mul_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht := abs_nonneg t
  have e : 2 * Real.log ((q : ℝ) * (|t| + 2)) = Real.log (((q : ℝ) * (|t| + 2)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [abs_mul, abs_two, e]
  apply Real.log_le_log (by positivity)
  have h1 : (q : ℝ) * (2 * |t| + 2) ≤ (q : ℝ) * (|t| + 2) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h2 : (q : ℝ) * (|t| + 2) ^ 2 ≤ ((q : ℝ) * (|t| + 2)) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  linarith

theorem realCharZeroFreeLargeHeightOfBounds : RealLargeTOf := by
  intro hLZ hLD hPos hTriv δ hδ
  obtain ⟨C₁, hC₁⟩ := hLZ
  obtain ⟨C₂, hC₂0, hC₂⟩ := hLD
  obtain ⟨C₃, hC₃⟩ := hTriv
  have hM₁ : 0 ≤ max C₁ 0 := le_max_right _ _
  have hM₃ : 0 ≤ max C₃ 0 := le_max_right _ _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 4 * max C₁ 0 + 2 * max C₃ 0 + 6 * C₂ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min (δ / 2) (min (1 / 10) (1 / (4 * K + 1))) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; exact lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have ha1 : a ≤ δ / 2 := by rw [ha]; exact min_le_left _ _
  have ha2 : a ≤ 1 / 10 := by rw [ha]; exact (min_le_right _ _).trans (min_le_left _ _)
  have ha3 : a ≤ 1 / (4 * K + 1) := by rw [ha]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hKa : K * a ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at ha3
    nlinarith
  have hδa : a ^ 2 / (4 * δ ^ 2) ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨a / 8, by positivity, ?_⟩
  intro q _ χ s hχ2 hχ1 hδt hreg hzero
  have hreg' : 1 - a / 8 / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hreg
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log ((q : ℝ) * (|s.im| + 2)) := ⟨_, rfl⟩
  rw [← hLdef] at hreg' hδt
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL : 1 / 2 < L := by
    rw [hLdef]
    exact lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) (two_le_mul_abs_add_two q s.im))
  have hLpos : 0 < L := by linarith
  have hβ1 : s.re < 1 := by
    by_contra hc
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inl hχ1) (not_lt.mp hc)
      hzero
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 + a / L := ⟨_, rfl⟩
  have haL : 0 < a / L := div_pos ha0 hLpos
  have haL5 : a / L ≤ 1 / 5 := by
    rw [div_le_iff₀ hLpos]
    linarith
  have hσ1 : 1 < σ := by linarith
  have hσ65 : σ ≤ 6 / 5 := by linarith
  have ha8 : a / 8 / L = (a / L) / 8 := by ring
  have hσβ : σ - s.re ≤ 9 / 8 * (a / L) := by linarith
  have hσβpos : 0 < σ - s.re := by linarith
  obtain ⟨Z, m, hZ, hm1, -, hbd⟩ := hC₁ q χ hχ1 s.im
  have hsZ : s ∈ Z := by
    rw [hZ]
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hd : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have : a / L / 8 ≤ 1 / 40 := by linarith
    constructor <;> linarith
  have hterm : ∀ ρ ∈ Z, 0 ≤ (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re := fun ρ hρ =>
    mul_nonneg (Nat.cast_nonneg _)
      (re_one_div_sub_zero_pos χ hχ1 ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le
  have hs_term : (1 / ((σ : ℂ) + s.im * I - s)).re = 1 / (σ - s.re) := by
    have hd : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [hd, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hsum : 1 / (σ - s.re) ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re := by
    refine le_trans ?_ (Finset.single_le_sum hterm hsZ)
    rw [hs_term]
    have h1 : (1 : ℝ) ≤ m s := by exact_mod_cast hm1 s hsZ
    have h0 : 0 ≤ 1 / (σ - s.re) := by positivity
    nlinarith
  have hu : 8 / 9 * (L / a) ≤ 1 / (σ - s.re) := by
    have h1 := one_div_le_one_div_of_le hσβpos hσβ
    have e : 1 / (9 / 8 * (a / L)) = 8 / 9 * (L / a) := by field_simp
    rw [e] at h1
    exact h1
  have hP := (hPos q σ hσ1).1 χ s.im
  rw [hχ2] at hP
  have h1 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ L / a + C₂ := by
    have h := hC₂ q 1 (σ : ℂ) (by simpa using hσ1)
    have e : 1 / ((σ : ℂ).re - 1) = L / a := by
      rw [Complex.ofReal_re, hσ, add_sub_cancel_left, one_div_div]
    rw [e] at h
    exact (Complex.re_le_norm _).trans h
  have h2 := hbd σ hσ1 hσ65
  rw [← hLdef] at h2
  have h3 := hC₃ q σ (2 * s.im) hσ1 (by linarith)
  have hpole := re_one_div_ofReal_add_mul_I (σ - 1) (2 * s.im)
  push_cast at h3 hpole
  rw [hpole] at h3
  have ht2 : δ ^ 2 / L ^ 2 ≤ s.im ^ 2 := by
    have h0 : 0 ≤ δ / L := by positivity
    have h := pow_le_pow_left₀ h0 hδt 2
    rwa [div_pow, sq_abs] at h
  have hσ1' : σ - 1 = a / L := by rw [hσ]; ring
  have hpb : (σ - 1) / ((σ - 1) ^ 2 + (2 * s.im) ^ 2) ≤ a * L / (4 * δ ^ 2) := by
    rw [hσ1']
    have hden : 0 < (a / L) ^ 2 + (2 * s.im) ^ 2 := by positivity
    rw [div_le_iff₀ hden]
    have e : a / L = a * L / (4 * δ ^ 2) * (4 * (δ ^ 2 / L ^ 2)) := by field_simp
    have hc : 0 ≤ a * L / (4 * δ ^ 2) := by positivity
    calc a / L = a * L / (4 * δ ^ 2) * (4 * (δ ^ 2 / L ^ 2)) := e
      _ ≤ a * L / (4 * δ ^ 2) * ((a / L) ^ 2 + (2 * s.im) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hc
        nlinarith [sq_nonneg (a / L)]
  have hX0 : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
    Real.log_nonneg (by have := two_le_mul_abs_add_two q (2 * s.im); linarith)
  have hX : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * L := by
    rw [hLdef]; exact log_mul_abs_two_mul_le q s.im
  have hC3X : C₃ * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ max C₃ 0 * (2 * L) :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0).trans (mul_le_mul_of_nonneg_left hX hM₃)
  have hC1L : C₁ * L ≤ max C₁ 0 * L := mul_le_mul_of_nonneg_right (le_max_left _ _) hLpos.le
  have hw : 0 < L / a := div_pos hLpos ha0
  have hKL : K * L ≤ L / a / 4 := by
    calc K * L = K * a * (L / a) := by field_simp
      _ ≤ 1 / 4 * (L / a) := mul_le_mul_of_nonneg_right hKa hw.le
      _ = L / a / 4 := by ring
  have hKL' : K * L = 4 * max C₁ 0 * L + 2 * max C₃ 0 * L + 6 * C₂ * L := by rw [hK]; ring
  have hPw : a * L / (4 * δ ^ 2) ≤ L / a / 16 := by
    calc a * L / (4 * δ ^ 2) = a ^ 2 / (4 * δ ^ 2) * (L / a) := by field_simp
      _ ≤ 1 / 16 * (L / a) := mul_le_mul_of_nonneg_right hδa hw.le
      _ = L / a / 16 := by ring
  have hC2 : 3 * C₂ ≤ 6 * C₂ * L := by
    have h := mul_nonneg hC₂0 (show (0 : ℝ) ≤ 2 * L - 1 by linarith)
    linarith
  linarith [h1, h2, h3, hpb, hC3X, hC1L, hsum, hu, hKL, hKL', hPw, hC2, hP]

end Formalism.ZeroFreeDirichlet
end
end

-- bundled from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivReal
section
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma one_sub_prime_cpow_neg_ne_zero (p : ℕ) (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  have h2 := congrArg norm h1
  rw [norm_natCast_cpow_of_pos hp.pos, norm_one, neg_re] at h2
  have h3 : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  linarith

theorem trivialCharZerosOfZeta : TrivZeros := by
  intro q _ s hs hs1 h0
  have hmul := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs1
  have h0' : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s = 0 := by
    rw [← hmul]
    exact h0
  rcases mul_eq_zero.1 h0' with h | h
  · exfalso
    obtain ⟨p, hp, hp0⟩ := Finset.prod_eq_zero_iff.1 h
    exact one_sub_prime_cpow_neg_ne_zero p (Nat.prime_of_mem_primeFactors hp) hs hp0
  · exact h

lemma conj_apply_of_sq_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (a : ZMod q) :
    starRingEnd ℂ (χ a) = χ a := by
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← sq, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.1 h2 with h | h
    · rw [h, map_one]
    · rw [h, map_neg, map_one]
  · rw [MulChar.map_nonunit χ ha, map_zero]

lemma conj_LFunction_conj_of_sq_eq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1)
    (z : ℂ) (hz : 1 < z.re) :
    starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z)) =
      DirichletCharacter.LFunction χ z := by
  have hz' : 1 < (starRingEnd ℂ z).re := by rwa [Complex.conj_re]
  rw [DirichletCharacter.LFunction_eq_LSeries χ hz', DirichletCharacter.LFunction_eq_LSeries χ hz,
    LSeries, LSeries, Complex.conj_tsum]
  congr 1
  funext m
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hm
  · exact map_zero _
  · show starRingEnd ℂ (χ m / (m : ℂ) ^ starRingEnd ℂ z) = χ m / (m : ℂ) ^ z
    have harg : (m : ℂ).arg ≠ Real.pi := by
      rw [Complex.natCast_arg]
      exact Real.pi_ne_zero.symm
    rw [map_div₀, conj_apply_of_sq_eq_one χ hχ, Complex.cpow_conj _ _ harg, map_natCast (starRingEnd ℂ) m,
      Complex.conj_conj]

theorem realCharConj : RealConj := by
  intro q _ χ hχ h1 s
  have hL : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction h1
  have hG : Differentiable ℂ
      (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) := by
    intro z
    have := (hL (starRingEnd ℂ z)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  have heq : (fun z => starRingEnd ℂ (DirichletCharacter.LFunction χ (starRingEnd ℂ z))) =
      DirichletCharacter.LFunction χ := by
    refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := 2) (analyticOnNhd_univ_iff_differentiable.2 hG)
      (analyticOnNhd_univ_iff_differentiable.2 hL) ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    exact conj_LFunction_conj_of_sq_eq_one χ hχ z hz
  have := congrFun heq (starRingEnd ℂ s)
  simp only [Complex.conj_conj] at this
  exact this.symm

end Formalism.ZeroFreeDirichlet
end
end

