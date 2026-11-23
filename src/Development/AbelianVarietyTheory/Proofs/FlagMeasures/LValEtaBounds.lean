module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Formalism.GL3MeanSquares.HookFormulaTorsion.SumWeightsOverPrimeLeHalfDegree

@[expose] public section

open NumberField

namespace GlobalTheory.EtaValueBound

theorem summable_zeta (M : ℕ) (hM : 2 ≤ M) : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ M) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < M))
  simpa using this

theorem zeta_le_two (M : ℕ) (hM : 2 ≤ M) : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M ≤ 2 := by
  have h2 : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 = Real.pi ^ 2 / 6 := by
    have h := hasSum_zeta_two
    have h' := (hasSum_nat_add_iff' 1).2 h
    simpa using h'.tsum_eq
  have h3 : ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M ≤ ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ 2 := by
    refine (summable_zeta M hM).tsum_le_tsum (fun m => ?_) (summable_zeta 2 le_rfl)
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hM)
  have h4 := Real.pi_lt_d2
  have h5 := Real.pi_pos
  rw [h2] at h3
  nlinarith

theorem multipliable_pos_abs_log_le (K : Type) [Field K] [NumberField K] [StarRing K]
    (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    Multipliable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac K M P.1) ∧
      0 < Formalism.HermitianLatticesTheory.lValEta K M ∧
      |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log 2 := by
  classical
  let PrimeIdeal := {P : Ideal (𝓞 K) // P.IsMaximal}
  have hexists (P : PrimeIdeal) : ∃ p k : ℕ,
      0 < k ∧ (p : 𝓞 K) ∈ P.1 ∧ p.Prime ∧ P.1.absNorm = p ^ k := by
    have := P.2
    exact P.1.exists_prime_and_absNorm_eq_pow
  choose p k hk hmem hp hnorm using hexists

  -- A conjugation-fixed prime has residue degree at least two over its rational prime.
  have hinert (P : PrimeIdeal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P.1 = P.1) :
      2 ≤ k P := by
    by_contra! hlt
    have hk1 : k P = 1 := by have := hk P; omega
    have hcard : Nat.card (𝓞 K ⧸ P.1) = p P := by
      rw [← Ideal.absNorm_eq_natCard, hnorm P, hk1, pow_one]
    have := P.2
    let := Ideal.Quotient.field P.1
    have : Fact (p P).Prime := ⟨hp P⟩
    have : CharP (𝓞 K ⧸ P.1) (p P) := (CharP.charP_iff_prime_eq_zero (hp P)).2 (by
      rw [← map_natCast (Ideal.Quotient.mk P.1), Ideal.Quotient.eq_zero_iff_mem]
      exact hmem P)
    have : Finite (𝓞 K ⧸ P.1) := Nat.finite_of_card_ne_zero (hcard.symm ▸ (hp P).ne_zero)
    let f := ZMod.castHom (dvd_refl (p P)) (𝓞 K ⧸ P.1)
    obtain ⟨θ, t, ht, hθt⟩ := hK.2.2 P.1 P.2
    obtain ⟨z, hz⟩ := (f.injective.bijective_of_nat_card_le (by rw [hcard, Nat.card_zmod])).2
      (Ideal.Quotient.mk P.1 θ)
    have hzθ : θ - (z.val : ℤ) ∈ P.1 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hz, map_intCast, Int.cast_natCast]
      simp [f, ZMod.castHom_apply]
    have hzt : t - (z.val : ℤ) ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P.1 := by
      apply Ideal.subset_span
      refine ⟨θ - (z.val : ℤ), hzθ, ?_⟩
      rw [map_sub, map_sub, ht, star_sub, map_intCast, star_intCast]
    rw [hc] at hzt
    exact hθt (by simpa only [sub_sub_sub_cancel_right] using P.1.sub_mem hzθ hzt)

  let invPow : ℕ →* ℝ := {
    toFun := fun n => ((n : ℝ)⁻¹) ^ M
    map_one' := by simp
    map_mul' := fun a b => by push_cast; rw [mul_inv, mul_pow] }
  let primeLog (q : ℕ) := -Real.log (1 - invPow q)
  have hinv_nonneg (q : ℕ) : 0 ≤ invPow q := by change 0 ≤ ((q : ℝ)⁻¹) ^ M; positivity
  have hinv_lt_one (q : ℕ) (hq : q.Prime) : invPow q < 1 := by
    change ((q : ℝ)⁻¹) ^ M < 1
    exact pow_lt_one₀ (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)) (by omega)
  have hprimeLog_nonneg (q : ℕ) (hq : q.Prime) : 0 ≤ primeLog q :=
    neg_nonneg.mpr (Real.log_nonpos (sub_pos.mpr (hinv_lt_one q hq)).le (by linarith [hinv_nonneg q]))

  have hlocal (P : PrimeIdeal) : 0 < Formalism.HermitianLatticesTheory.eulerFac K M P.1 ∧
      |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| ≤
        (k P : ℝ) / 2 * primeLog (p P) := by
    have hp1 : (1 : ℝ) < p P := by exact_mod_cast (hp P).one_lt
    have hcompare (x : ℝ) (hx : (p P : ℝ) ≤ x) :
        0 ≤ x ^ (-(M : ℤ)) ∧ x ^ (-(M : ℤ)) ≤ invPow (p P) := by
      have hxinv : 0 ≤ x⁻¹ := inv_nonneg.mpr (by linarith)
      rw [zpow_neg, zpow_natCast, ← inv_pow]
      exact ⟨pow_nonneg hxinv _, pow_le_pow_left₀ hxinv (inv_anti₀ (by linarith) hx) M⟩
    have hlog (y : ℝ) (hy : 0 ≤ y) (hle : y ≤ invPow (p P)) :
        0 < 1 - y ∧ |Real.log (1 - y)| ≤ primeLog (p P) := by
      have hbase := sub_pos.mpr (hinv_lt_one _ (hp P))
      have hpos : 0 < 1 - y := by linarith
      rw [abs_of_nonpos (Real.log_nonpos hpos.le (by linarith))]
      exact ⟨hpos, neg_le_neg (Real.log_le_log hbase (by linarith))⟩
    unfold Formalism.HermitianLatticesTheory.eulerFac
    split_ifs with hc
    · have hk2 := hinert P hc
      have hsq : (p P : ℝ) ^ 2 ≤ (P.1.absNorm : ℝ) := by
        rw [hnorm P, Nat.cast_pow]
        exact pow_le_pow_right₀ hp1.le hk2
      have hsqrt := (le_abs_self (p P : ℝ)).trans (Real.abs_le_sqrt hsq)
      obtain ⟨hy, hle⟩ := hcompare _ hsqrt
      obtain ⟨hpos, hle'⟩ := hlog _ hy hle
      have hk2' : (2 : ℝ) ≤ k P := by exact_mod_cast hk2
      have hweight : primeLog (p P) ≤ (k P : ℝ) / 2 * primeLog (p P) :=
        le_mul_of_one_le_left (hprimeLog_nonneg _ (hp P)) (by linarith)
      rcases neg_one_pow_eq_or ℝ M with hs | hs
      · rw [hs, one_mul, Real.log_inv, abs_neg]
        exact ⟨inv_pos.mpr hpos, hle'.trans hweight⟩
      · rw [hs, neg_one_mul, sub_neg_eq_add, Real.log_inv, abs_neg,
          abs_of_nonneg (Real.log_nonneg (by linarith))]
        refine ⟨inv_pos.mpr (by linarith), le_trans ?_ hweight⟩
        change Real.log (1 + Real.sqrt (P.1.absNorm : ℝ) ^ (-(M : ℤ))) ≤
          -Real.log (1 - invPow (p P))
        have h₁ := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 +
          Real.sqrt (P.1.absNorm : ℝ) ^ (-(M : ℤ)))
        have h₂ := Real.log_le_sub_one_of_pos (sub_pos.mpr (hinv_lt_one _ (hp P)))
        linarith
    · have hN : p P ≤ P.1.absNorm := by
        rw [hnorm P]
        exact Nat.le_self_pow (hk P).ne' _
      obtain ⟨hy, hle⟩ := hcompare (P.1.absNorm : ℝ) (by exact_mod_cast hN)
      obtain ⟨hpos, hle'⟩ := hlog _ hy hle
      refine ⟨Real.rpow_pos_of_pos hpos _, ?_⟩
      rw [Real.log_rpow hpos, abs_mul, show |(-(1 : ℝ) / 2)| = 1 / 2 by norm_num]
      have hk1 : (1 : ℝ) ≤ k P := by exact_mod_cast hk P
      exact (mul_le_mul_of_nonneg_left hle' (by norm_num)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (hprimeLog_nonneg _ (hp P)))

  -- The product of the norms of the selected primes above q divides the norm of (q).
  have hdegree (q : ℕ) (hq : q.Prime) (T : Finset PrimeIdeal) (hT : ∀ P ∈ T, p P = q) :
      ∑ P ∈ T, k P ≤ Module.finrank ℚ K := by
    have hdvd : (∏ P ∈ T, P.1) ∣ Ideal.span {(q : 𝓞 K)} := by
      apply Finset.prod_dvd_of_coprime
      · intro P _ Q _ hne
        exact Ideal.isCoprime_iff_sup_eq.mpr
          (Ideal.IsMaximal.coprime_of_ne P.2 Q.2 (fun h => hne (Subtype.ext h)))
      · intro P hP
        rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff, ← hT P hP]
        exact hmem P
    have hspan : (Ideal.span {(q : 𝓞 K)}).absNorm = q ^ Module.finrank ℚ K := by
      rw [Ideal.absNorm_span_singleton]
      have heq : (q : 𝓞 K) = algebraMap ℤ (𝓞 K) (q : ℤ) := by simp
      rw [heq, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
      simp [Int.natAbs_pow]
    have hprod := map_dvd Ideal.absNorm hdvd
    rw [map_prod, hspan] at hprod
    have heq : (∏ P ∈ T, P.1.absNorm) = q ^ ∑ P ∈ T, k P := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_congr rfl (fun P hP => by rw [hnorm P, hT P hP])
    rw [heq] at hprod
    exact (pow_le_pow_iff_right₀ hq.one_lt).mp (Nat.le_of_dvd (pow_pos hq.pos _) hprod)

  have hsum_primeLog (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) :
      ∑ q ∈ S, primeLog q ≤ Real.log (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M) := by
    let N := S.sup id + 1
    have hsub : S ⊆ N.primesBelow := fun q hq => Nat.mem_primesBelow.mpr
      ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hq), hS q hq⟩
    have hpos (q : ℕ) (hq : q.Prime) : 0 < 1 - invPow q := sub_pos.mpr (hinv_lt_one q hq)
    have hsum : Summable (fun n : ℕ => invPow n) := by
      change Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ M)
      simpa only [inv_pow] using Real.summable_nat_pow_inv.mpr (by omega : 1 < M)
    have htsum : ∑' n : ℕ, invPow n = ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M := by
      rw [hsum.tsum_eq_zero_add]
      simp [invPow, zero_pow (show M ≠ 0 by omega), inv_pow, one_div]
    calc ∑ q ∈ S, primeLog q = Real.log (∏ q ∈ S, (1 - invPow q)⁻¹) := by
          rw [Real.log_prod (fun q hq => (inv_pos.mpr (hpos q (hS q hq))).ne')]
          exact Finset.sum_congr rfl (fun q _ => (Real.log_inv _).symm)
      _ ≤ Real.log (∏ q ∈ N.primesBelow, (1 - invPow q)⁻¹) := by
          apply Real.log_le_log (Finset.prod_pos (fun q hq => inv_pos.mpr (hpos q (hS q hq))))
          exact Finset.prod_le_prod_of_subset_of_one_le₀ hsub
            (fun q hq => (inv_pos.mpr (hpos q (hS q hq))).le)
            (fun q hq _ => (one_le_inv₀ (hpos q (Nat.mem_primesBelow.mp hq).2)).2
              (by linarith [hinv_nonneg q]))
      _ ≤ _ := by
          apply Real.log_le_log (Finset.prod_pos (fun q hq => inv_pos.mpr (hpos q (Nat.mem_primesBelow.mp hq).2)))
          rw [EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hsum, ← htsum]
          exact Summable.tsum_subtype_le (fun n : ℕ => invPow n) _ hinv_nonneg hsum

  have hdegree_eq : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) = (Module.finrank ℚ K : ℝ) / 2 := by
    have := hK.1
    unfold Formalism.HermitianLatticesTheory.fDeg
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, ← InfinitePlace.card_add_two_mul_card_eq_rank,
      IsTotallyComplex.nrRealPlaces_eq_zero K]
    push_cast
    ring
  have hpos : ∀ P : PrimeIdeal, 0 < Formalism.HermitianLatticesTheory.eulerFac K M P.1 :=
    fun P => (hlocal P).1
  have hpart (u : Finset PrimeIdeal) :
      ∑ P ∈ u, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| ≤
        (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M) := by
    let S := u.image p
    have hS : ∀ q ∈ S, q.Prime := by
      intro q hq
      obtain ⟨P, _, rfl⟩ := Finset.mem_image.mp hq
      exact hp P
    calc ∑ P ∈ u, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|
        ≤ ∑ P ∈ u, (k P : ℝ) / 2 * primeLog (p P) := Finset.sum_le_sum (fun P _ => (hlocal P).2)
      _ = ∑ q ∈ S, ∑ P ∈ u.filter (fun P => p P = q), (k P : ℝ) / 2 * primeLog (p P) :=
          (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem p hP) _).symm
      _ ≤ ∑ q ∈ S, (Module.finrank ℚ K : ℝ) / 2 * primeLog q := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          calc ∑ P ∈ u.filter (fun P => p P = q), (k P : ℝ) / 2 * primeLog (p P) =
              ∑ P ∈ u.filter (fun P => p P = q), (k P : ℝ) / 2 * primeLog q :=
                Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2])
            _ ≤ _ := by
                rw [← Finset.sum_mul, ← Finset.sum_div]
                apply mul_le_mul_of_nonneg_right _ (hprimeLog_nonneg q (hS q hq))
                apply div_le_div_of_nonneg_right _ (by norm_num)
                exact_mod_cast hdegree q (hS q hq) _ (fun P hP => (Finset.mem_filter.mp hP).2)
      _ ≤ _ := by
          rw [← Finset.mul_sum, hdegree_eq]
          exact mul_le_mul_of_nonneg_left (hsum_primeLog S hS) (by positivity)
  have habs : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|) :=
    summable_of_sum_le (fun P => abs_nonneg _) hpart
  have hsum : Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) := habs.of_abs
  have hprod : Real.exp (∑' P : {P : Ideal (𝓞 K) // P.IsMaximal},
      Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)) = Formalism.HermitianLatticesTheory.lValEta K M :=
    Real.rexp_tsum_eq_tprod hpos hsum
  refine ⟨Real.multipliable_of_summable_log hpos hsum, ?_, ?_⟩
  · rw [← hprod]; exact Real.exp_pos _
  · rw [← hprod, Real.log_exp]
    have hz : 0 < ∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ M :=
      (summable_zeta M hM).tsum_pos (fun m => by positivity) 0 (by positivity)
    calc |∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|
        ≤ ∑' P : {P : Ideal (𝓞 K) // P.IsMaximal}, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| := by
          simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := fun P :
            {P : Ideal (𝓞 K) // P.IsMaximal} => Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1))
            (by simpa [Real.norm_eq_abs] using habs)
      _ ≤ _ := habs.tsum_le_of_sum_le hpart
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.log_le_log hz (zeta_le_two M hM)) (Nat.cast_nonneg _)

theorem lValEta_bounds : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ i : ℕ, 2 ≤ i → ((2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg K))⁻¹ ≤ Formalism.HermitianLatticesTheory.lValEta K i ∧ Formalism.HermitianLatticesTheory.lValEta K i ≤ 2 ^ (Formalism.HermitianLatticesTheory.fDeg K) := by
  intro K _ _ _ hK i hi
  obtain ⟨-, h0, h1⟩ := multipliable_pos_abs_log_le K hK i hi
  rw [abs_le] at h1
  have h2 : (0 : ℝ) < 2 ^ Formalism.HermitianLatticesTheory.fDeg K := by positivity
  constructor
  · rw [← Real.log_le_log_iff (inv_pos.2 h2) h0, Real.log_inv, Real.log_pow]
    exact h1.1
  · rw [← Real.log_le_log_iff h0 h2, Real.log_pow]
    exact h1.2

end GlobalTheory.EtaValueBound
