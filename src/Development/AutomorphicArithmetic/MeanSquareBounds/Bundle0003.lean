module

public import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0011
public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0006
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0003
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.Bundle0002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagA
public import Development.AutomorphicArithmetic.MeanSquareBounds.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.MeanSquareBounds.CountBadCore
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem aux (Q : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hp : ψ.IsPrimitive) (hM : (M : ℝ) ≤ Q)
    (hz : ¬ ZeroFreeBox Q ψ) :
    ∃ p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)), p.1 + 1 = M ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  refine ⟨⟨k, ψ⟩, rfl, hp, hM, ?_⟩
  unfold ZeroFreeBox at hz
  push Not at hz
  exact hz

theorem count_bad_core :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q F : ℝ) (S : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ S, q.Prime ∧ F < q ∧ ∃ (N f : ℕ) (_ : NeZero N) (ψ : DirichletCharacter ℂ N),
        N = f * q ∧ (f : ℝ) ≤ F ∧ ψ.IsPrimitive ∧ (N : ℝ) ≤ Q ∧ ¬ ZeroFreeBox Q ψ) →
      (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  classical
  obtain ⟨C, hC⟩ := Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.zero_density_box
  refine ⟨max C 0, le_max_right _ _, fun Q F S hQ hS => ?_⟩
  have key : ∀ q : ℕ, ∃ p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)), q ∈ S →
      (∃ f : ℕ, p.1 + 1 = f * q ∧ (f : ℝ) ≤ F) ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨-, -, N, f, _, ψ, hN, hf, hp, hNQ, hz⟩ := hS q hq
      obtain ⟨p, h1, h2⟩ := aux Q N ψ hp hNQ hz
      exact ⟨p, fun _ => ⟨⟨f, h1.trans hN, hf⟩, h2⟩⟩
    · exact ⟨⟨0, 1⟩, fun h => absurd h hq⟩
  choose g hg using key
  have hinj : Set.InjOn g S := by
    intro q hq q' hq' h
    obtain ⟨⟨f, hf, -⟩, -⟩ := hg q hq
    obtain ⟨⟨f', hf', hF'⟩, -⟩ := hg q' hq'
    have hpq := (hS q hq).1
    have hpq' := (hS q' hq').1
    have hlt := (hS q hq).2.1
    have he : f * q = f' * q' := by rw [← hf, ← hf', h]
    have hd : q ∣ f' * q' := ⟨f, by rw [← he, mul_comm]⟩
    rcases (Nat.Prime.dvd_mul hpq).1 hd with h1 | h1
    · have hpos : 0 < f' := by
        rcases Nat.eq_zero_or_pos f' with h0 | h0
        · rw [h0] at hf'; simp at hf'
        · exact h0
      have : (q : ℝ) ≤ f' := by exact_mod_cast Nat.le_of_dvd hpos h1
      linarith
    · exact (Nat.prime_dvd_prime_iff_eq hpq hpq').1 h1
  have h1 := hC Q (S.image g) hQ (by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact (hg q hq).2)
  rw [Finset.card_image_of_injOn hinj] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact Real.rpow_nonneg (by linarith) _

end QH
end

-- bundled from Development.AutomorphicArithmetic.MeanSquareBounds.Kappa4Loglog
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem kappa4_num (K : ℝ) (hK : 0 ≤ K) (s Q : ℝ) (hs : 3 ≤ s) (hQ : 0 < Q)
    (hQs : (s ^ 4) ^ 1006 ≤ Q) (x : ℝ) (hx : x = s ^ 10) :
    ((K * s ^ 4 * (s ^ 4 * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ 2 * K + 802 := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs.trans (le_self_pow₀ hs1 (by norm_num))
  have hx0 : 0 < x := by linarith
  have hxa : x ^ ((2 / 5) / 4 : ℝ) = s := by
    rw [hx, ← Real.rpow_natCast s 10, ← Real.rpow_mul hs0.le]
    norm_num
  apply le_of_mul_le_mul_left _ hx0
  rw [Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (2 / 5) hx0, hxa,
    Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q K _ _ _ hx0 hQ]
  have t3 := Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3
  have t1 : (s ^ 4) ^ 2 * s ≤ x := by
    rw [hx]
    calc (s ^ 4) ^ 2 * s = s ^ 9 := by ring
      _ ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
  have t2 : s ^ 4 * x ^ 403 / Q ≤ x := by
    rw [div_le_iff₀ hQ]
    have e : s ^ 4 * x ^ 403 = x * (s ^ 4) ^ 1006 := by
      rw [hx, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    rw [e]
    exact mul_le_mul_of_nonneg_left hQs hx0.le
  have u1 := mul_le_mul_of_nonneg_left t1 hK
  have u2 := mul_le_mul_of_nonneg_left t2 hK
  have u3 : (802 : ℝ) ≤ x * 802 := by linarith
  have e1 : K * (s ^ 4) ^ 2 * s = K * ((s ^ 4) ^ 2 * s) := mul_assoc _ _ _
  have e2 : x * (2 * K + 802) = K * x + K * x + x * 802 := by ring
  rw [e1, e2]
  exact add_le_add (add_le_add u1 u2) (t3.trans u3)

set_option maxRecDepth 4096 in
private theorem kappa4_loglog : ∃ C l₀ : ℝ, 1 ≤ l₀ ∧ ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    l₀ ≤ Real.log Q → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 1000 * Real.log (Real.log Q) + C := by
  obtain ⟨K, hK0, hK⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_contour ((2 / 5) / 1600) (by positivity) (by norm_num)
  have hev : ∀ᶠ l : ℝ in Filter.atTop, l ^ 1006 ≤ Real.exp l := by
    have h := (Real.tendsto_exp_div_pow_atTop 1006).eventually_ge_atTop 1
    filter_upwards [h, Filter.eventually_gt_atTop 0] with l hl hl0
    rwa [le_div_iff₀ (by positivity), one_mul] at hl
  obtain ⟨l₀, hl₀⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_ge_atTop 81))
  refine ⟨2 * K + 802 + 2, l₀, by linarith [(hl₀ l₀ le_rfl).2], ?_⟩
  intro Q N _ χ hQlo hgood
  obtain ⟨hχ, hNQ, hbox⟩ := hgood
  obtain ⟨hexp, h81⟩ := hl₀ _ hQlo
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  rw [Real.exp_log hQ0] at hexp
  have hQ2 : 2 ≤ Q := by
    have := Real.log_le_self hQ0.le
    linarith
  obtain ⟨s, hs0, hs4⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 4 = Real.log Q :=
    ⟨Real.log Q ^ ((4 : ℕ) : ℝ)⁻¹, Real.rpow_nonneg (by linarith) _,
      Real.rpow_inv_natCast_pow (by linarith) (by norm_num)⟩
  have hs3 : 3 ≤ s := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hs0
    rw [hs4]; linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = s ^ 10 := ⟨_, rfl⟩
  have hnum := kappa4_num K hK0 s Q hs3 hQ0 (by rw [hs4]; exact hexp) x hx
  rw [hs4] at hnum
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs3.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hx0 : 0 < x := by linarith
  have hlogz : Real.log (x ^ 400) = 1000 * Real.log (Real.log Q) := by
    rw [← hs4, hx, Real.log_pow, Real.log_pow, Real.log_pow]; push_cast; ring
  set z : ℝ := x ^ 400 with hz
  set η : ℝ := 1 / x ^ 2 with hη
  have hz1 : 1 ≤ z := one_le_pow₀ (by linarith)
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  have hzη : 0 < z * η := by positivity
  have hC := hK N χ Q z η hχ hQ2 hNQ hbox hz1 hη0 hη1
  have hD := Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ z (z * η) hz1 hzη
  set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP
  have hkey : ((z * η : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.negLD χ 1 - P) =
      -(Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) +
      (Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * P) := by ring
  have hnorm : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤
      (K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + z ^ 2 / Q)
        + z * η * (z * η + 1) * Real.log (z + z * η) / z) / (z * η) := by
    rw [le_div_iff₀ hzη]
    have h1 := congrArg norm hkey
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hzη.le] at h1
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ * (z * η) = z * η * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := mul_comm _ _
      _ = _ := h1
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        exact add_le_add hC hD
  have htail := hnorm.trans hnum
  have hPle : ‖P‖ ≤ Real.log z + 2 := by
    have hM : ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤ Real.log z + 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (Deduction.mertens_upper z hz1)
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
      · intro n _ _
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    refine le_trans (norm_sum_le _ _) (le_trans ?_ hM)
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχn : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    gcongr
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ (n : ZMod N)‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 := by gcongr
      _ = ArithmeticFunction.vonMangoldt n := mul_one _
  have hLD : logDerivLAtOne χ = -(Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, neg_neg]
  rw [hLD, norm_neg]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1‖ = ‖P + (Formalism.ZeroFreeDirichlet.negLD χ 1 - P)‖ := by rw [add_sub_cancel]
    _ ≤ ‖P‖ + ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := norm_add_le _ _
    _ ≤ _ := by rw [← hlogz]; linarith

theorem kappa4 :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 52 → 0 < A → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ A * Y ^ (ε / 5) * Real.log Y ^ 2 → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 4 * Real.log Y := by
  intro ε A hε hε1 hA
  obtain ⟨C, l₀, hl₀, hC⟩ := kappa4_loglog
  have e1 : ∀ᶠ Y : ℝ in Filter.atTop, l₀ ≤ Y ^ (ε / 6) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 6)).eventually_ge_atTop _
  have e2 : ∀ᶠ u : ℝ in Filter.atTop, ‖Real.log u‖ ≤ (1 / 26000) * ‖u‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num)
  have e3 : ∀ᶠ u : ℝ in Filter.atTop, 13 * (1000 * Real.log A + C) ≤ u := Filter.eventually_ge_atTop _
  have e4 := Real.tendsto_log_atTop.eventually (e2.and (e3.and (Filter.eventually_ge_atTop 1)))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 (e1.and (e4.and (Filter.eventually_gt_atTop 0)))
  refine ⟨Y₀, ?_⟩
  intro Y hY Q N _ χ hlo hhi hgood
  obtain ⟨h1, ⟨h2, h3, h4⟩, hY0⟩ := hY₀ Y hY
  have hb := hC Q N χ (h1.trans hlo) hgood
  have hu0 : 0 < Real.log Y := by linarith
  have hp : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  have hl : Real.log (Real.log Q) ≤ Real.log A + ε / 5 * Real.log Y + 2 * Real.log (Real.log Y) := by
    refine (Real.log_le_log (by linarith) hhi).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hA.ne' hp.ne', Real.log_rpow hY0,
      Real.log_pow]
    push_cast; ring
  rw [Real.norm_of_nonneg hu0.le, Real.norm_of_nonneg (Real.log_nonneg h4)] at h2
  have h5 : ε * Real.log Y ≤ 1 / 52 * Real.log Y := mul_le_mul_of_nonneg_right hε1.le hu0.le
  have h6 : ε / 5 * Real.log Y = ε * Real.log Y / 5 := by ring
  rw [h6] at hl
  linarith

end QH
end

-- bundled from Development.AutomorphicArithmetic.MeanSquareBounds.RRLe
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem RR_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ (N m₀ : ℕ) (w : ℝ), 1 ≤ w →
      (∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ w) → RR (cN y) m₀ N ≤ C * (Real.sqrt y + w * Real.log y) := by
  obtain ⟨C₁, hC₁, hsP⟩ := exists_primePowerSum_le_mul_log
  have hK := dA_KC_pos
  refine ⟨3 * dA_KC + C₁, by positivity, ?_⟩
  intro y hy N m₀ w hw hm
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hf0 : ∀ n, 0 ≤ cN y n := fun n => dA_cN_nonneg hy0 n
  have hsplit : RR (cN y) m₀ N ≤
      (∑ n ∈ Icc 1 N with IsPrimePow n ∧ Even (n.factorization n.minFac), cN y n) +
      ∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac ∣ m₀, cN y n := by
    unfold RR
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have := hf0 n
    by_cases h1 : IsPrimePow n <;> by_cases h2 : Even (n.factorization n.minFac) <;>
      by_cases h3 : n.minFac ∣ m₀ <;> simp [h1, h2, h3, this]
  have hA : (∑ n ∈ Icc 1 N with IsPrimePow n ∧ Even (n.factorization n.minFac), cN y n)
      ≤ 3 * dA_KC * Real.sqrt y := by
    have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ Even (n.factorization n.minFac))
        ⊆ (Icc 1 N).image (fun m => m ^ 2) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpp, hev⟩ := hn
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      rw [Nat.pow_minFac hk.ne', hp.minFac_eq, Nat.factorization_pow_self hp] at hev
      obtain ⟨j, rfl⟩ := hev
      refine Finset.mem_image.2 ⟨p ^ j, ?_, by ring⟩
      have h1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
      have h2 : p ^ j ≤ p ^ (j + j) := Nat.pow_le_pow_right hp.pos (by omega)
      exact Finset.mem_Icc.2 ⟨h1, h2.trans hnN⟩
    calc _ ≤ ∑ n ∈ (Icc 1 N).image (fun m => m ^ 2), cN y n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
      _ = ∑ m ∈ Icc 1 N, cN y (m ^ 2) :=
          Finset.sum_image (fun a _ b _ h => Nat.pow_left_injective (by norm_num) h)
      _ = ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m * min 1 (y / (m:ℝ) ^ 2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [cN, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero, Nat.cast_pow]
      _ ≤ dA_KC * ∑ m ∈ Icc 1 N, min 1 (y / (m:ℝ) ^ 2) := by
          refine dA_vM_major _ (fun n => le_min zero_le_one (div_nonneg hy0 (by positivity))) ?_ N
          intro n hn
          apply min_le_min_left
          apply div_le_div_of_nonneg_left hy0 (pow_pos (Nat.cast_pos.mpr hn) 2)
          have := (Nat.cast_nonneg n : (0:ℝ) ≤ n)
          push_cast
          nlinarith
      _ ≤ dA_KC * (3 * Real.sqrt y) :=
          mul_le_mul_of_nonneg_left (dA_sum_min_sq y (by linarith) N) hK.le
      _ = 3 * dA_KC * Real.sqrt y := by ring
  have hB : (∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac ∣ m₀, cN y n)
      ≤ C₁ * w * Real.log y := by
    set P := (Icc 1 N).filter (fun p => p.Prime ∧ p ∣ m₀ ∧ (p:ℝ) ≤ w) with hP
    have hmaps : ∀ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀),
        n.minFac ∈ P := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpp, hd⟩ := hn
      have hpr : n.minFac.Prime := Nat.minFac_prime hpp.ne_one
      have hle : n.minFac ≤ N := (Nat.minFac_le (by omega)).trans hnN
      simp only [hP, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpr.one_lt.le, hle⟩, hpr, hd, hm _ hpr hd hle⟩
    have hcard : (P.card : ℝ) ≤ w := by
      have hs : P ⊆ Icc 1 ⌊w⌋₊ := by
        intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.1, Nat.le_floor hp.2.2.2⟩
      have h1 := Finset.card_le_card hs
      rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
      calc (P.card : ℝ) ≤ ⌊w⌋₊ := by exact_mod_cast h1
        _ ≤ w := Nat.floor_le (by linarith)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ p ∈ P, C₁ * Real.log y := by
          refine Finset.sum_le_sum fun p _ => ?_
          refine le_trans ?_ (hsP y hy N p)
          unfold sP
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hf0 n)
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1.1, hn.1.2.1, hn.2⟩
      _ = P.card * (C₁ * Real.log y) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ w * (C₁ * Real.log y) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hC₁.le hlog)
      _ = C₁ * w * Real.log y := by ring
  have hsq : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hwl : 0 ≤ w * Real.log y := mul_nonneg (by linarith) hlog
  calc RR (cN y) m₀ N ≤ _ := hsplit
    _ ≤ 3 * dA_KC * Real.sqrt y + C₁ * w * Real.log y := add_le_add hA hB
    _ ≤ (3 * dA_KC + C₁) * (Real.sqrt y + w * Real.log y) := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * dA_KC) hwl, mul_nonneg hC₁.le hsq]

end QH
end

-- bundled from Development.AutomorphicArithmetic.MeanSquareBounds.TailKExp
section
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem tailK_exp (ε K A : ℝ) (hε : 0 < ε) :
    ∀ᶠ Y : ℝ in Filter.atTop, A * (Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6)))) ≤ 1 / 3 := by
  have hc : 0 < ε / 6 := by positivity
  have hg := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (404 * K / (ε / 6)) 1 one_pos).comp
    (tendsto_rpow_atTop hc)
  have hlim : Filter.Tendsto (fun Y : ℝ => A * (Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6)))))
      Filter.atTop (nhds 0) := by
    have := hg.const_mul A
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with Y hY
    simp only [Function.comp_apply, neg_mul, one_mul]
    rw [← Real.rpow_mul hY.le, mul_div_cancel₀ _ hc.ne']
  exact hlim.eventually (ge_mem_nhds (by norm_num))

private theorem tailK_num (ε K A : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K) (hA0 : 0 ≤ A) :
    ∃ Y₀ : ℝ, 3 ≤ Y₀ ∧
    ∀ Y x Q : ℝ, Y₀ ≤ Y → x = Y ^ K → 0 < Q → Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) →
      x * ((A * Real.log Q * (Real.log Q * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + ε / K / 1600) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ Y ^ ε := by
  have hev1 := tailK_exp ε K A hε
  have hev2 : ∀ᶠ Y : ℝ in Filter.atTop, 3 * A ≤ Y ^ (ε / 4) :=
    (tendsto_rpow_atTop (by positivity)).eventually_ge_atTop _
  have hev3 : ∀ᶠ Y : ℝ in Filter.atTop, 3 * 802 ≤ Y ^ ε :=
    (tendsto_rpow_atTop hε).eventually_ge_atTop _
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1 (hev1.and (hev2.and hev3))
  refine ⟨max Y₁ 3, le_max_right _ _, ?_⟩
  intro Y x Q hY hx hQ hl1 hl2
  have hY1 : Y₁ ≤ Y := (le_max_left _ _).trans hY
  have hY3 : 3 ≤ Y := (le_max_right _ _).trans hY
  obtain ⟨h1, h2, h3⟩ := hY₁ Y hY1
  have hY0 : 0 < Y := by linarith
  have hK0 : K ≠ 0 := by positivity
  have hxY : Y ≤ x := by
    rw [hx]; simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) hK
  have hx0 : 0 < x := by linarith
  have hx3 : 3 ≤ x := by linarith
  rw [Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (ε / K) hx0,
    Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q A (Real.log Q) (x ^ (ε / K / 4))
      (Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2))) hx0 hQ]
  have ha : x ^ (ε / K / 4) = Y ^ (ε / 4) := by
    rw [hx, ← Real.rpow_mul hY0.le]
    congr 1
    field_simp
  have hlpos : 0 ≤ Real.log Q := le_trans (by positivity) hl1
  have hu1 : Y ^ (ε / 4) ≤ Y := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) (by linarith : ε / 4 ≤ 1)
  have huY : Y ^ (ε / 4) ≤ x := hu1.trans hxY
  have hlx : Real.log Q ≤ x := hl2.trans huY
  have ht : Real.exp (Y ^ (ε / 6)) ≤ Q := (Real.le_log_iff_exp_le hQ).1 hl1
  have hx404 : Y ^ (404 * K) = x ^ 404 := by
    rw [hx, ← Real.rpow_mul_natCast hY0.le]
    congr 1
    push_cast
    ring
  have hsecond : A * (Real.log Q * x ^ 403 / Q) ≤ 1 / 3 := by
    have hQe : 1 / Q ≤ Real.exp (-(Y ^ (ε / 6))) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos _) ht
    have hm : Real.log Q * x ^ 403 / Q ≤ Y ^ (404 * K) * Real.exp (-(Y ^ (ε / 6))) := by
      rw [hx404]
      calc Real.log Q * x ^ 403 / Q = Real.log Q * x ^ 403 * (1 / Q) := by ring
        _ ≤ x * x ^ 403 * Real.exp (-(Y ^ (ε / 6))) := by gcongr
        _ = x ^ 404 * Real.exp (-(Y ^ (ε / 6))) := by ring
    exact (mul_le_mul_of_nonneg_left hm hA0).trans h1
  have hthird := Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3
  rw [ha]
  have hu0 : 0 < Y ^ (ε / 4) := Real.rpow_pos_of_pos hY0 _
  have hu4 : Y ^ ε = (Y ^ (ε / 4)) ^ 4 := by
    rw [← Real.rpow_mul_natCast hY0.le]
    congr 1
    push_cast
    ring
  have hfirst : A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ (Y ^ (ε / 4)) ^ 4 / 3 := by
    have hl2' : Real.log Q ^ 2 ≤ (Y ^ (ε / 4)) ^ 2 := pow_le_pow_left₀ hlpos hl2 2
    have hm : A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ A * (Y ^ (ε / 4)) ^ 3 := by
      calc A * Real.log Q ^ 2 * Y ^ (ε / 4) ≤ A * (Y ^ (ε / 4)) ^ 2 * Y ^ (ε / 4) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl2' hA0) hu0.le
        _ = A * (Y ^ (ε / 4)) ^ 3 := by ring
    nlinarith [mul_nonneg (sub_nonneg.2 h2) (pow_pos hu0 3).le]
  rw [hu4] at h3 ⊢
  linarith

theorem tailK :
    ∀ ε K : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ →
      ‖((Y ^ K : ℝ) : ℂ) * tailL χ ((Y ^ K) ^ 400)‖ ≤ Y ^ ε := by
  intro ε K hε hε1 hK
  have hK0 : 0 < K := by linarith
  have hδ0 : 0 < ε / K / 1600 := by positivity
  have hδ1 : ε / K / 1600 ≤ 1 / 800 := by
    have : ε / K ≤ 1 := (div_le_one hK0).2 (by linarith)
    linarith
  obtain ⟨A, hA0, hA⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_contour (ε / K / 1600) hδ0 hδ1
  obtain ⟨Y₀, hY₀3, hY₀⟩ := tailK_num ε K A hε hε1 hK hA0
  refine ⟨Y₀, fun Y hY Q N _ χ hl1 hl2 hG => ?_⟩
  obtain ⟨hχ1, hNQ, hZ⟩ := hG
  have hY3 : 3 ≤ Y := le_trans hY₀3 hY
  have hY0 : 0 < Y := by linarith
  have hxY : Y ≤ Y ^ K := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Y) hK
  generalize hxd : Y ^ K = x at hxY ⊢
  have hx0 : 0 < x := by linarith
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  have hc1 : 1 ≤ Y ^ (ε / 6) := Real.one_le_rpow (by linarith) (by positivity)
  have hQ2 : 2 ≤ Q := by
    have e1 : Real.exp 1 ≤ Q := (Real.le_log_iff_exp_le hQ0).1 (hc1.trans hl1)
    have e2 := Real.add_one_le_exp (1:ℝ)
    linarith
  have hz1 : (1:ℝ) ≤ x ^ 400 := one_le_pow₀ (by linarith)
  have hη0 : (0:ℝ) < 1 / x ^ 2 := by positivity
  have hη1 : 1 / x ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hh0 : (0:ℝ) < x ^ 400 * (1 / x ^ 2) := by positivity
  have hc := hA N χ Q (x ^ 400) (1 / x ^ 2) hχ1 hQ2 hNQ hZ hz1 hη0 hη1
  have hd := Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ (x ^ 400) (x ^ 400 * (1 / x ^ 2)) hz1 hh0
  have key : ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) * tailL χ (x ^ 400) =
      (Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400 + x ^ 400 * (1 / x ^ 2)) - Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400) -
        ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) *
          ∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n) -
      (Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400 + x ^ 400 * (1 / x ^ 2)) - Formalism.ZeroFreeDirichlet.Schi χ (x ^ 400) -
        ((x ^ 400 * (1 / x ^ 2) : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [tailL, Formalism.ZeroFreeDirichlet.negLD, logDerivLAtOne]
    ring
  have hnorm := (norm_sub_le _ _).trans (add_le_add hd hc)
  rw [← key, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0.le] at hnorm
  have hfin := hY₀ Y x Q hY hxd.symm hQ0 hl1 hl2
  have ht : ‖tailL χ (x ^ 400)‖ ≤ (A * Real.log Q * (Real.log Q * (1 / x ^ 2) *
      (x ^ 400) ^ (1 - 1 / 400 + ε / K / 1600) + (x ^ 400) ^ 2 / Q) +
      x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) *
      Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400) / (x ^ 400 * (1 / x ^ 2)) := by
    rw [le_div_iff₀ hh0]
    linarith
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le]
  exact (mul_le_mul_of_nonneg_left ht hx0.le).trans hfin

end QH
end

