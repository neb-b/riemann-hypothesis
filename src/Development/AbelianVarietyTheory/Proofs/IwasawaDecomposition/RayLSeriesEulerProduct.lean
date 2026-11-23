module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.Mem Complex Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.Mem

theorem tsum_eq_exp_tsum_neg_log_of_primes {α ι : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    (p : ι → α) (hp : ∀ i, Prime (p i)) (hdvd : ∀ i j, p i ∣ p j → i = j)
    (f : α → ℂ) (hmul : ∀ a b, f (a * b) = f a * f b) (h1 : f 1 = 1)
    (hex : ∀ a, a ≠ 1 → f a ≠ 0 → ∃ i, p i ∣ a) (hsum : Summable fun a => ‖f a‖)
    (hne : ∀ i, 1 - f (p i) ≠ 0) :
    ∑' a, f a = exp (∑' i, -log (1 - f (p i))) := by
  classical
  set g : Finset ι → α → ℂ := fun S a => if ∀ i ∈ S, ¬ p i ∣ a then f a else 0 with hg
  have hgle : ∀ S a, ‖g S a‖ ≤ ‖f a‖ := by
    intro S a
    simp only [hg]
    split_ifs <;> simp
  have hgs : ∀ S, Summable (g S) := fun S => Summable.of_norm_bounded hsum (hgle S)
  have key : ∀ S : Finset ι, (∏ i ∈ S, (1 - f (p i))) * ∑' a, f a = ∑' a, g S a := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [hg]
    | insert i S hi ih =>
      rw [Finset.prod_insert hi, mul_assoc, ih]
      have hinj : Function.Injective fun b : α => p i * b := mul_right_injective₀ (hp i).ne_zero
      have e1 : ∀ a, g (insert i S) a = g S a - (if p i ∣ a then g S a else 0) := by
        intro a
        simp only [hg, Finset.forall_mem_insert]
        by_cases h : p i ∣ a <;> simp [h]
      have hs2 : Summable fun a => if p i ∣ a then g S a else 0 :=
        Summable.of_norm_bounded hsum (fun a => by
          split_ifs
          · exact hgle S a
          · simp)
      have e2 : ∑' a, (if p i ∣ a then g S a else 0) = f (p i) * ∑' a, g S a := by
        rw [← hinj.tsum_eq, ← tsum_mul_left]
        · refine tsum_congr fun b => ?_
          rw [if_pos (dvd_mul_right _ _)]
          have : (∀ j ∈ S, ¬ p j ∣ p i * b) ↔ ∀ j ∈ S, ¬ p j ∣ b := by
            refine forall₂_congr fun j hj => not_congr ?_
            rw [(hp j).dvd_mul]
            refine or_iff_right fun h => hi ?_
            rwa [← hdvd _ _ h]
          simp only [hg, this, hmul]
          split_ifs <;> simp
        · intro a ha
          by_cases h : p i ∣ a
          · obtain ⟨b, rfl⟩ := h
            exact ⟨b, rfl⟩
          · simp [h] at ha
      simp only [e1]
      rw [(hgs S).tsum_sub hs2, e2]
      ring
  have lim1 : Tendsto (fun S : Finset ι => ∑' a, g S a) atTop
      (𝓝 (∑' a : α, if a = 1 then (1 : ℂ) else 0)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun a => ?_)
      (Eventually.of_forall fun S a => hgle S a)
    by_cases ha : a = 1
    · subst ha
      have : ∀ S, g S 1 = 1 := fun S => by
        simp only [hg]
        rw [if_pos fun i _ => (hp i).not_dvd_one, h1]
      simp [this]
    · rw [if_neg ha]
      by_cases hf : f a = 0
      · simp [hg, hf]
      · obtain ⟨i, hi⟩ := hex a ha hf
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop ({i} : Finset ι)] with S hS
        simp only [hg]
        rw [if_neg]
        intro h
        exact h i (hS (Finset.mem_singleton_self i)) hi
  rw [tsum_ite_eq] at lim1
  have pinj : Function.Injective p := fun i j h => hdvd i j (h ▸ dvd_rfl)
  have hl : Summable fun i => log (1 - f (p i)) :=
    Summable.clog_one_sub (hsum.of_norm.comp_injective pinj)
  have lim2 : Tendsto (fun S : Finset ι => ∏ i ∈ S, (1 - f (p i))) atTop
      (𝓝 (exp (∑' i, log (1 - f (p i))))) := Complex.hasProd_of_hasSum_log hne hl.hasSum
  have lim3 := lim2.mul_const (∑' a, f a)
  simp only [key] at lim3
  have := tendsto_nhds_unique lim3 lim1
  rw [tsum_neg, exp_neg]
  exact eq_inv_of_mul_eq_one_right this

theorem lseriesSummable_card_absNorm (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (r := 1) ?_ (fun _ => Nat.cast_nonneg _)
    zero_le_one hs
  have h : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ)) atTop
      (𝓝 (dedekindZeta_residue K)) := by
    refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
    simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  simp only [Real.rpow_one]
  exact Asymptotics.isBigO_of_div_tendsto_nhds (by
    filter_upwards [eventually_gt_atTop 0] with n hn h0
    exact absurd (Nat.cast_eq_zero.1 h0) hn.ne') _ h

instance finite_absNorm_fiber (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

theorem summable_norm_absNorm_cpow (K : Type) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    Summable fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖ := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  rw [← (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I)).summable_iff,
    summable_sigma_of_nonneg (fun _ => by exact norm_nonneg _)]
  refine ⟨fun n => Summable.of_finite, ?_⟩
  refine (lseriesSummable_card_absNorm K hs).norm.congr fun n => ?_
  have : ∀ I : {I : Ideal (𝓞 K) // Ideal.absNorm I = n},
      ((fun I : Ideal (𝓞 K) => ‖((Ideal.absNorm I : ℕ) : ℂ) ^ (-s)‖) ∘
        (Equiv.sigmaFiberEquiv (fun I : Ideal (𝓞 K) => Ideal.absNorm I))) ⟨n, I⟩ = ‖(n : ℂ) ^ (-s)‖ := by
    rintro ⟨I, rfl⟩; rfl
  rw [tsum_congr this, tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hs0]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← cpow_neg, norm_mul]
    simp

end GlobalTheory.Mem
