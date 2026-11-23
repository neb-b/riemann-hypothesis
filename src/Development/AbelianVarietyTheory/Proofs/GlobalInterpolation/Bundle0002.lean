module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableAtMellinSummatory
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LGrowth

open Filter Topology Asymptotics

theorem norm_partialSum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hper : ∀ m : ℕ, ∑ k ∈ Finset.range q, χ ((m + k : ℕ) : ZMod q) = 0 := by
    intro m
    have h0 : ∑ a : ZMod q, χ a = 0 := χ.sum_eq_zero_of_ne_one hχ
    rw [← h0, ← Equiv.sum_comp (Equiv.addLeft (m : ZMod q))]
    refine Finset.sum_bij (fun k _ => (k : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      have := (ZMod.natCast_eq_natCast_iff' a b q).1 hab
      rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
        at this
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
    · intro a _
      simp
  have hI : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)
      = ∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q) := by
    intro n
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp
  rw [hI]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n q with h | h
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => χ.norm_le_one _).trans ?_
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast h.le
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      rw [Finset.sum_range_add]
      have := hper (1 + m)
      simp only [← add_assoc]
      rw [this, add_zero]
      exact ih m (by omega)

section General

variable {f : ℕ → ℂ} {C : ℝ}

noncomputable def summatory (f : ℕ → ℂ) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

theorem measurable_summatory (f : ℕ → ℂ) : Measurable (summatory f) :=
  (measurable_from_top (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

theorem summatory_eq_zero {t : ℝ} (ht : t < 1) : summatory f t = 0 := by
  simp [summatory, Nat.floor_eq_zero.2 ht]

theorem mellin_summatory (s : ℂ) :
    mellin (summatory f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ici (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans_le (Set.mem_Ici.1 ht))), integral_Ici_eq_integral_Ioi]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [summatory, smul_eq_mul]
    rw [mul_comm]
    congr 2
    ring
  · intro t ht
    rw [summatory_eq_zero (not_le.1 ht.2), smul_zero]

theorem differentiableAt_mellin_summatory (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (summatory f) (-z)) s := by
  have h : DifferentiableAt ℂ (mellin (summatory f)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const C).mono (measurable_summatory f).aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => (hC _).trans (Real.le_norm_self C)
    · refine IsBigO.of_bound C (Eventually.of_forall fun t => ?_)
      simpa [summatory] using hC ⌊t⌋₊
    · simpa using hs
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
      simp [summatory_eq_zero ht]
    · simp
  exact h.comp s differentiableAt_id.neg

theorem norm_mellin_summatory_le (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mellin (summatory f) (-s)‖ ≤ C / s.re := by
  rw [mellin_summatory]
  have hlt : -(s.re + 1) < -1 := by linarith
  refine (norm_integral_le_of_norm_le (g := fun t : ℝ => C * t ^ (-(s.re + 1)))
    ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg ht0.le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]
    refine le_of_eq ?_
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this]
    field_simp

end General

theorem LFunction_eq_mul_mellin (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * mellin (summatory fun n => χ (n : ZMod q)) (-s) := by
  have hC := norm_partialSum_le q χ hχ
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have h1 : AnalyticOnNhd ℂ (LFunction χ) {z : ℂ | 0 < z.re} :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have h2 : AnalyticOnNhd ℂ (fun z => z * mellin (summatory fun n => χ (n : ZMod q)) (-z))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_id.mul
      (differentiableAt_mellin_summatory hC hz)).differentiableWithinAt
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by simp) ?_ hs
  have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hV.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz
  rw [LFunction_eq_LSeries χ hz, mellin_summatory]
  refine LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz) ?_
  refine IsBigO.of_bound q (Eventually.of_forall fun n => ?_)
  simpa using hC n

theorem norm_LFunction_le : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ s : ℂ, 0 < s.re → ‖LFunction χ s‖ ≤ q * ‖s‖ / s.re := by
  intro q _ χ hχ s hs
  rw [LFunction_eq_mul_mellin q χ hχ hs, norm_mul]
  refine (mul_le_mul_of_nonneg_left
    (norm_mellin_summatory_le (norm_partialSum_le q χ hχ) hs) (norm_nonneg s)).trans ?_
  exact le_of_eq (by ring)

end GlobalTheory.LGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfNormSubOneLt
section
namespace GlobalTheory.CharacterConductorBall

private lemma norm_sub_one_le_norm_mul_self_sub_one (w : ℂ) (h : ‖w - 1‖ < 1 / 2) :
    3 / 2 * ‖w - 1‖ ≤ ‖w * w - 1‖ := by
  have h1 : w * w - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (2 : ℝ) ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have := norm_sub_le (w + 1) (w - 1)
    have e : (w + 1) - (w - 1) = (2 : ℂ) := by ring
    rw [e] at this
    simpa using this
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem eq_one_of_norm_sub_one_lt {A : Type} [AddMonoid A] (ψ : AddChar A ℂ) (B : Set A)
    (hB : ∀ x ∈ B, x + x ∈ B) (hψ : ∀ x ∈ B, ‖ψ x - 1‖ < 1 / 2) : ∀ x ∈ B, ψ x = 1 := by

  have key : ∀ k : ℕ, ∀ x ∈ B, (3 / 2 : ℝ) ^ k * ‖ψ x - 1‖ < 1 / 2 := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hψ x hx
    | succ k ih =>
      intro x hx
      have h2 := ih (x + x) (hB x hx)
      have h3 := norm_sub_one_le_norm_mul_self_sub_one (ψ x) (hψ x hx)
      rw [AddChar.map_add_eq_mul] at h2
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖ψ x - 1‖ = (3 / 2) ^ k * (3 / 2 * ‖ψ x - 1‖) := by ring
        _ ≤ (3 / 2) ^ k * ‖ψ x * ψ x - 1‖ := by gcongr
        _ < 1 / 2 := h2
  intro x hx
  by_contra hne
  have hpos : 0 < ‖ψ x - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖ψ x - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have := key k x hx
  rw [div_lt_iff₀ hpos] at hk
  linarith

theorem exists_ball_trivial {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by

  have hnhds : (ψ : K → ℂ) ⁻¹' {w : ℂ | ‖w - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply hc.continuousAt.preimage_mem_nhds
    rw [AddChar.map_zero_eq_one]
    exact (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const))
      continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hnhds
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc_def
  have hc0 : c ≠ 0 := by
    have := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono (zero_lt_iff.2 γ.ne_zero)
    rw [map_zero] at this
    exact this.ne'

  have hlt : ∀ y ∈ {y : K | Valued.v y < c}, ψ y = 1 := by
    refine eq_one_of_norm_sub_one_lt ψ _ (fun y hy => ?_) (fun y hy => ?_)
    · exact lt_of_le_of_lt ((Valued.v.map_add y y).trans (max_self _).le) hy
    · apply hγ
      simpa [Valuation.restrict_lt_iff_lt_embedding] using hy
  refine ⟨WithZero.log c - 1, fun x hx => hlt x ?_⟩
  calc Valued.v x ≤ WithZero.exp (WithZero.log c - 1) := hx
    _ < WithZero.exp (WithZero.log c) := WithZero.exp_lt_exp.2 (by omega)
    _ = c := WithZero.exp_log hc0

private lemma addChar_trivial_mul_of_valuation_le {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) {t t' : K}
    (ht : ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1)
    (hle : Valued.v t' ≤ Valued.v t) :
    ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t' * s) = 1 := by
  intro s hs
  by_cases h0 : t = 0
  · subst h0
    have : t' = 0 := by simpa using hle
    simp [this, AddChar.map_zero_eq_one]
  · have hv : Valued.v t ≠ 0 := by simpa using h0
    have e : t' * s = t * (t' * t⁻¹ * s) := by field_simp
    rw [e]
    apply ht
    rw [map_mul, map_mul, map_inv₀]
    calc Valued.v t' * (Valued.v t)⁻¹ * Valued.v s ≤ Valued.v t * (Valued.v t)⁻¹ * 1 := by
          gcongr
      _ = 1 := by rw [mul_one, mul_inv_cancel₀ hv]

theorem exists_conductor {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous (ψ : K → ℂ)) (hψ : ∃ t : K, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K,
      (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
        Valued.v t ≤ WithZero.exp n := by
  classical
  obtain ⟨m, hm⟩ := exists_ball_trivial ψ hc
  obtain ⟨t₀, ht₀⟩ := hψ
  have ht₀0 : t₀ ≠ 0 := by rintro rfl; simp [AddChar.map_zero_eq_one] at ht₀
  have hnot : ¬ ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t₀ * s) = 1 :=
    fun h => ht₀ (by simpa using h 1 (by simp))

  have hmem : ∀ t : K, Valued.v t ≤ WithZero.exp m →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1 := by
    intro t ht s hs
    apply hm
    rw [map_mul]
    calc Valued.v t * Valued.v s ≤ WithZero.exp m * 1 := by gcongr
      _ = WithZero.exp m := mul_one _
  have hbdd : ∃ b : ℤ, ∀ k : ℤ, (∀ t : K, Valued.v t ≤ WithZero.exp k →
      ∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) → k ≤ b := by
    refine ⟨WithZero.log (Valued.v t₀), fun k hk => ?_⟩
    by_contra hlt
    apply hnot
    apply hk
    have hv : Valued.v t₀ ≠ 0 := by simpa using ht₀0
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 (by omega)
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd hbdd ⟨m, hmem⟩
  refine ⟨n, fun t => ⟨fun hS => ?_, fun ht => hn t ht⟩⟩
  by_contra hgt
  rw [not_le] at hgt
  have hv : Valued.v t ≠ 0 := ne_of_gt (lt_trans WithZero.exp_pos hgt)
  have hj : WithZero.log (Valued.v t) ≤ n := by
    apply hmax
    intro t' ht'
    rw [WithZero.exp_log hv] at ht'
    exact addChar_trivial_mul_of_valuation_le ψ hS ht'
  have : Valued.v t ≤ WithZero.exp n := by
    rw [← WithZero.exp_log hv]
    exact WithZero.exp_le_exp.2 hj
  exact absurd hgt (not_lt.2 this)

end GlobalTheory.CharacterConductorBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfPowClose
section
namespace GlobalTheory.EqOneOfPowerClose

open Finset

theorem eq_one_of_pow_close {u : ℂ} (h : ∀ n : ℕ, ‖u ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    u = (1 : ℂ) := by
  have key : ∀ n : ℕ, (n : ℝ) * ‖u - 1‖ ≤ 1 := by
    intro n
    have h1 : ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ (n : ℝ) / 2 := by
      calc ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ ∑ k ∈ range n, ‖u ^ k - 1‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ range n, (1 / 2 : ℝ) := sum_le_sum fun k _ => (h k).le
        _ = (n : ℝ) / 2 := by simp; ring
    have h2 : (n : ℂ) = ∑ k ∈ range n, u ^ k - ∑ k ∈ range n, (u ^ k - 1) := by
      rw [sum_sub_distrib]; simp
    have h3 : (n : ℝ) ≤ ‖∑ k ∈ range n, u ^ k‖ + ‖∑ k ∈ range n, (u ^ k - 1)‖ := by
      have := norm_sub_le (∑ k ∈ range n, u ^ k) (∑ k ∈ range n, (u ^ k - 1))
      rw [← h2, Complex.norm_natCast] at this
      exact this
    have h4 : ‖∑ k ∈ range n, u ^ k‖ * ‖u - 1‖ < 1 / 2 := by
      rw [← norm_mul, geom_sum_mul]; exact h n
    have h5 : (n : ℝ) / 2 ≤ ‖∑ k ∈ range n, u ^ k‖ := by linarith
    have h6 := mul_le_mul_of_nonneg_right h5 (norm_nonneg (u - 1))
    linarith
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖u - 1‖)
  rw [div_lt_iff₀ hpos] at hn
  linarith [key n]

end GlobalTheory.EqOneOfPowerClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsComapPrime
section
namespace GlobalTheory.ComapPrimeExistence

open NumberField IsDedekindDomain

theorem exists_comap_prime {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (φ : E →+* K) (w : HeightOneSpectrum (RingOfIntegers K)) :
    ∃ Q : HeightOneSpectrum (RingOfIntegers E), ∀ r : RingOfIntegers E,
      r ∈ Q.asIdeal ↔ (RingOfIntegers.mapRingHom φ : RingOfIntegers E → RingOfIntegers K) r ∈ w.asIdeal := by
  have hp := w.isPrime
  refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom φ), Ideal.comap_isPrime _ _, ?_⟩,
    fun r => Ideal.mem_comap⟩
  intro h
  have hn : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem : ((Ideal.absNorm w.asIdeal : ℕ) : RingOfIntegers E) ∈
      w.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hmem
  exact hn (Nat.cast_eq_zero.mp hmem)

end GlobalTheory.ComapPrimeExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConductorAdicCompletion
section
namespace GlobalTheory.ConductorAdicCompletion

theorem eq_one_of_pow_near_one (z : ℂ) (h : ∀ k : ℕ, ‖z ^ k - 1‖ ≤ 1 / 2) : z = 1 := by
  by_contra hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1

  have hre : ∀ k : ℕ, 1 / 2 ≤ (z ^ k).re := by
    intro k
    have h2 := (Complex.abs_re_le_norm (z ^ k - 1)).trans (h k)
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_le.mp h2).1
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hsum : ∑ k ∈ Finset.range N, z ^ k = (z ^ N - 1) / (z - 1) := geom_sum_eq hz N
  have hlow : (N : ℝ) / 2 ≤ (∑ k ∈ Finset.range N, z ^ k).re := by
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ k ∈ Finset.range N, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun k _ => hre k
  have hup : (∑ k ∈ Finset.range N, z ^ k).re ≤ 1 / 2 / ‖z - 1‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [hsum, norm_div]
    exact div_le_div_of_nonneg_right (h N) (norm_nonneg _)
  have he : 1 / 2 / ‖z - 1‖ = (1 / ‖z - 1‖) / 2 := by ring
  linarith

theorem exists_ball_trivial {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) :
    ∃ m : ℤ, ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1 := by
  have hmem : {x : K | ‖ψ x - 1‖ < 1 / 2} ∈ nhds (0 : K) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (by fun_prop) continuous_const
    · simp
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hmem
  set g : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hg
  have hg0 : g ≠ 0 := by
    rw [hg]
    exact (map_ne_zero _).mpr γ.ne_zero
  refine ⟨WithZero.log g - 1, fun x hx => ?_⟩
  have hlt : WithZero.exp (WithZero.log g - 1) < g :=
    (WithZero.lt_log_iff_exp_lt hg0).mp (by omega)
  apply eq_one_of_pow_near_one
  intro k
  rw [← AddChar.map_nsmul_eq_pow]
  have hk : Valued.v (k • x) ≤ WithZero.exp (WithZero.log g - 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [succ_nsmul]
      exact Valuation.map_add_le _ ih hx
  have : k • x ∈ {x : K | ‖ψ x - 1‖ < 1 / 2} := by
    apply hγ
    exact (Valuation.restrict_lt_iff_lt_embedding _).mpr (hk.trans_lt hlt)
  exact le_of_lt this

theorem exists_conductor {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hc : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun m : ℤ => ∀ x : K, Valued.v x ≤ WithZero.exp m → ψ x = 1)
    ⟨WithZero.log (Valued.v t₀ : WithZero (Multiplicative ℤ)), fun m hm => by
      have h1 : WithZero.exp m < Valued.v t₀ := lt_of_not_ge fun h => ht₀ (hm _ h)
      exact ((WithZero.lt_log_iff_exp_lt (ne_zero_of_lt h1)).mpr h1).le⟩
    (exists_ball_trivial ψ hc)
  refine ⟨n, fun t => ⟨fun h => ?_, fun h s hs => ?_⟩⟩
  · by_contra hlt
    have h1 : WithZero.exp n < Valued.v t := lt_of_not_ge hlt
    have hv0 : (Valued.v t : WithZero (Multiplicative ℤ)) ≠ 0 := ne_zero_of_lt h1
    have ht : t ≠ 0 := fun h0 => hv0 (by simp [h0])
    have h2 := (WithZero.lt_log_iff_exp_lt hv0).mpr h1
    have h3 := hmax (WithZero.log (Valued.v t : WithZero (Multiplicative ℤ))) (fun x hx => by
      rw [WithZero.exp_log hv0] at hx
      have h4 := h (x / t) (by
        rw [map_div₀]
        exact div_le_one_of_le₀ hx zero_le)
      rwa [mul_div_cancel₀ _ ht] at h4)
    omega
  · apply hn
    rw [map_mul]
    exact (mul_le_of_le_one_right' hs).trans h

theorem exists_conductor_adicCompletion :
    ∀ (F : Type) [Field F] [NumberField F]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      (ψ : AddChar (IsDedekindDomain.HeightOneSpectrum.adicCompletion F v) ℂ),
      Continuous (⇑ψ : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v → ℂ) →
      (∀ t, ‖ψ t‖ = (1 : ℝ)) → (∃ t, ψ t ≠ (1 : ℂ)) →
      ∃ n : ℤ, ∀ t : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v,
        (∀ s ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v,
          ψ (t * s) = (1 : ℂ)) ↔
        (Valued.v : IsDedekindDomain.HeightOneSpectrum.adicCompletion F v →
          WithZero (Multiplicative ℤ)) t ≤ WithZero.exp n := by
  intro F _ _ v ψ hc _ hne
  exact exists_conductor ψ hc hne

end GlobalTheory.ConductorAdicCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFactorOrder
section
namespace GlobalTheory.FactorOrderExistence

open Filter Topology

theorem exists_factor_order {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) {w : ℂ}
    (hw : w ∈ U) (hord : analyticOrderAt g w ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧
      (∀ z : ℂ, g z = (z - w) ^ analyticOrderNatAt g w * h z) ∧ h w ≠ (0 : ℂ) := by
  classical
  obtain ⟨h0, h0a, h0ne, hev⟩ := ((hg w hw).analyticOrderAt_ne_top).1 hord
  set n := analyticOrderNatAt g w with hn
  refine ⟨fun z => if z = w then h0 w else g z / (z - w) ^ n, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzw : z = w
    · subst hzw
      refine h0a.congr ?_
      filter_upwards [hev] with y hy
      by_cases hyz : y = z
      · simp [hyz]
      · have hne : (y - z) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hyz)
        simp only [hyz, if_false]
        rw [hy, smul_eq_mul, mul_div_cancel_left₀ _ hne]
    · have ha : AnalyticAt ℂ (fun y => g y / (y - w) ^ n) z :=
        (hg z hz).div ((analyticAt_id.sub analyticAt_const).pow n)
          (pow_ne_zero _ (sub_ne_zero.2 hzw))
      refine ha.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hzw] with y hy
      simp [hy]
  · intro z
    by_cases hzw : z = w
    · subst hzw
      have := hev.self_of_nhds
      simpa using this
    · have hne : (z - w) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hzw)
      simp only [hzw, if_false]
      field_simp
  · simpa using h0ne

end GlobalTheory.FactorOrderExistence
end

