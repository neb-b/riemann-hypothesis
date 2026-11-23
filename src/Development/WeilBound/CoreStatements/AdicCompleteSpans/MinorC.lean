module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec

@[expose] public section

noncomputable section

namespace PositivityTheory.CompleteLocalMinorRing.Minor

open PowerSeries GlobalTheory.BK Filter Topology

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K]

omit [IsUltrametricDist K] in
theorem dvd_iff_norm {x y : O} (hy : algebraMap O K y ≠ 0) :
    y ∣ x ↔ ‖algebraMap O K x‖ ≤ ‖algebraMap O K y‖ := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [map_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_algebraMap_le c)
  · intro h
    obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O)
      (algebraMap O K x / algebraMap O K y)).2 (by
        rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _))
    refine ⟨c, IsUnitBall.inj (O := O) (K := K) ?_⟩
    rw [map_mul, hc, mul_div_cancel₀ _ hy]

omit [IsUltrametricDist K] in
theorem isUnit_iff_norm {x : O} : IsUnit x ↔ ‖algebraMap O K x‖ = 1 := by
  rw [isUnit_iff_dvd_one]
  by_cases hx : algebraMap O K x = 0
  · constructor
    · rintro ⟨c, hc⟩
      have := congrArg (algebraMap O K) hc
      rw [map_mul, hx, zero_mul, map_one] at this
      exact absurd this one_ne_zero
    · intro h
      rw [hx, norm_zero] at h
      exact absurd h zero_ne_one
  · rw [dvd_iff_norm hx, map_one, norm_one]
    exact ⟨fun h => le_antisymm (norm_algebraMap_le x) h, fun h => h.ge⟩


omit [IsUltrametricDist K] in
theorem mem_max_iff [IsLocalRing O] {x : O} :
    x ∈ IsLocalRing.maximalIdeal O ↔ ‖algebraMap O K x‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm (K := K)]
  exact ⟨fun h => lt_of_le_of_ne (norm_algebraMap_le x) h, fun h => h.ne⟩

omit [IsUltrametricDist K] in
theorem isAdicComplete_span [CompleteSpace K] {c : O} (h0 : algebraMap O K c ≠ 0)
    (h1 : ‖algebraMap O K c‖ < 1) : IsAdicComplete (Ideal.span {c}) O := by
  have hmem : ∀ (n : ℕ) (x : O), x ∈ (Ideal.span {c} ^ n • ⊤ : Submodule O O) ↔
      ‖algebraMap O K x‖ ≤ ‖algebraMap O K c‖ ^ n := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      dvd_iff_norm (K := K) (by rw [map_pow]; exact pow_ne_zero _ h0), map_pow, norm_pow]
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (algebraMap O K c)) h1
  have : IsHausdorff (Ideal.span {c}) O := ⟨fun x hx => by
    apply IsUnitBall.inj (O := O) (K := K)
    rw [map_zero, ← norm_le_zero_iff]
    refine ge_of_tendsto' hlim fun n => ?_
    have := hx n
    rwa [SModEq.zero, hmem] at this⟩
  have : IsPrecomplete (Ideal.span {c}) O := ⟨fun f hf => by
    have hd : ∀ m n, m ≤ n → ‖algebraMap O K (f m) - algebraMap O K (f n)‖ ≤
        ‖algebraMap O K c‖ ^ m := fun m n h => by
      have := hf h
      rwa [SModEq.sub_mem, hmem, map_sub] at this
    have hc : CauchySeq fun n => algebraMap O K (f n) :=
      cauchySeq_of_le_tendsto_0' _ (fun m n h => by rw [dist_eq_norm]; exact hd m n h) hlim
    obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
    obtain ⟨L, hL⟩ := (IsUnitBall.mem_range_iff (O := O) y).2
      (le_of_tendsto' hy.norm fun n => norm_algebraMap_le _)
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem, hmem, map_sub, hL]
    refine le_of_tendsto (hy.const_sub (algebraMap O K (f n))).norm ?_
    exact eventually_atTop.2 ⟨n, fun m hm => hd n m hm⟩⟩
  exact {}

variable (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

include K l in
theorem isAdicComplete_max [CompleteSpace K] [FiniteDimensional ℚ_[l] K] [IsLocalRing O] :
    IsAdicComplete (IsLocalRing.maximalIdeal O) O := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  have hc : IsCompact (Metric.ball (0 : K) 1) :=
    (isCompact_closedBall (0 : K) 1).of_isClosed_subset (IsUltrametricDist.isClosed_ball _ _)
      Metric.ball_subset_closedBall
  obtain ⟨y, hy, hmax⟩ := hc.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  rw [mem_ball_zero_iff] at hy
  obtain ⟨c, rfl⟩ := (IsUnitBall.mem_range_iff (O := O) y).2 hy.le
  have h0 : algebraMap O K c ≠ 0 := by
    have : ‖(l : K)‖ ≤ ‖algebraMap O K c‖ := hmax (mem_ball_zero_iff.2 (norm_l_lt_one l))
    exact norm_pos_iff.1 ((norm_pos_iff.2 (l_ne_zero l)).trans_le this)
  have : IsLocalRing.maximalIdeal O = Ideal.span {c} := by
    ext x
    rw [mem_max_iff (K := K), Ideal.mem_span_singleton, dvd_iff_norm h0]
    exact ⟨fun h => hmax (mem_ball_zero_iff.2 h), fun h => h.trans_lt hy⟩
  rw [this]
  exact isAdicComplete_span h0 hy



end PositivityTheory.CompleteLocalMinorRing.Minor
