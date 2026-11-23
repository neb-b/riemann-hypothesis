module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ArFact
section
open UpperTheory.V.Af.Rs in
private theorem arFact_agree (e e' a b : ℕ → ℂ) (ha : Rec e a) (hb : Rec e' b)
    (hp : ∀ p : ℕ, p.Prime → b p = a p) :
    ∀ n : ℕ, 1 ≤ n → (∀ p : ℕ, p.Prime → p ∣ n → e p = e' p) → b n = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn hdiv
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    rw [ha.1, hb.1]
  · obtain ⟨p, hpp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    obtain ⟨n', rfl⟩ := hpn
    have hn' : 1 ≤ n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hlt : n' < p * n' := by have := hpp.two_le; nlinarith
    have hep : e p = e' p := hdiv p hpp (dvd_mul_right p n')
    have hsub : ∀ q : ℕ, q.Prime → q ∣ n' → e q = e' q :=
      fun q hq hqd => hdiv q hq (dvd_mul_of_dvd_right hqd p)
    have h1 := ha.2 p hpp n' hn'
    have h2 := hb.2 p hpp n' hn'
    have hb' := ih n' hlt hn' hsub
    by_cases hpd : p ∣ n'
    · obtain ⟨t, rfl⟩ := hpd
      have ht : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn')
      have hdt : p * t / p = t := Nat.mul_div_cancel_left t hpp.pos
      have hlt' : t < p * t := by have := hpp.two_le; nlinarith
      have hbt := ih t (by nlinarith) ht
        (fun q hq hqd => hsub q hq (dvd_mul_of_dvd_right hqd p))
      rw [if_pos (dvd_mul_right p t), hdt] at h1 h2
      rw [hbt, hb', hp p hpp, ← hep] at h2
      linear_combination h2 - h1
    · rw [if_neg hpd, mul_zero, add_zero] at h1 h2
      rw [hb', hp p hpp] at h2
      rw [h2, h1]

theorem UpperTheory.V.Af.Rs.arFact :
    UpperTheory.V.Af.Rs.ArFact := by
  intro r e e' a b ha hb hp hbad hbd
  refine ⟨{n | b n = a n}, fun n hn => hn, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn han
  by_cases hgood : ∀ p : ℕ, p.Prime → p ∣ n → e p = e' p
  · have hag := arFact_agree e e' a b ha hb hp n hn hgood
    exact ⟨n, hag, 1, by ring, by simp, by simp [hag]⟩
  · push_neg at hgood
    obtain ⟨p, hpp, hpn, hne⟩ := hgood
    have hap : a p = 0 := hbad p hpp hne
    have hbp : b p = 0 := by rw [hp p hpp, hap]
    obtain ⟨n'', rfl⟩ := hpn
    have hn'' : 1 ≤ n'' := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have h1 := ha.2 p hpp n'' hn''
    by_cases hpd : p ∣ n''
    · obtain ⟨t, rfl⟩ := hpd
      have ht : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hn'')
      have hdt : p * t / p = t := Nat.mul_div_cancel_left t hpp.pos
      have h2 := hb.2 p hpp (p * t) hn''
      rw [if_pos (dvd_mul_right p t), hdt, hap, zero_mul] at h1
      rw [if_pos (dvd_mul_right p t), hdt, hbp, zero_mul] at h2
      have hA : a (p * (p * t)) = -(e p * a t) := by linear_combination h1
      have hB : b (p * (p * t)) = -(e' p * b t) := by linear_combination h2
      have hat : a t ≠ 0 := by
        intro h0
        apply han
        rw [hA, h0, mul_zero, neg_zero]
      have hlt : t < p * (p * t) := by have := hpp.two_le; nlinarith
      obtain ⟨n₁, hn₁, m, hnm, hA1, hB1⟩ := ih t hlt ht hat
      refine ⟨n₁, hn₁, p * m, by rw [hnm]; ring, ?_, ?_⟩
      · rw [hA, norm_neg, norm_mul]
        calc ‖e p‖ * ‖a t‖ ≤ (p:ℝ) ^ r * (‖a n₁‖ * (m:ℝ) ^ r) :=
              mul_le_mul (hbd p hpp).1 hA1 (norm_nonneg _) (by positivity)
          _ = ‖a n₁‖ * ((p * m : ℕ) : ℝ) ^ r := by push_cast; ring
      · rw [hB, norm_neg, norm_mul]
        calc ‖e' p‖ * ‖b t‖ ≤ (p:ℝ) ^ r * (‖a n₁‖ * (m:ℝ) ^ r) :=
              mul_le_mul (hbd p hpp).2 hB1 (norm_nonneg _) (by positivity)
          _ = ‖a n₁‖ * ((p * m : ℕ) : ℝ) ^ r := by push_cast; ring
    · exfalso
      apply han
      rw [if_neg hpd, mul_zero, add_zero, hap, zero_mul] at h1
      exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ArSumTerm
section
open scoped ComplexConjugate

private lemma arSum_term (r : ℕ) (t : ℝ) (ht : (r : ℝ) + 1 ≤ t) (x y : ℝ) (n₁ m : ℕ) (hx : 0 ≤ x)
    (hn : 1 ≤ n₁ * m ^ 2) (h : x ≤ y * (m : ℝ) ^ r) :
    x ^ 2 / ((n₁ * m ^ 2 : ℕ) : ℝ) ^ t ≤ y ^ 2 / (n₁ : ℝ) ^ t * (1 / (m : ℝ) ^ 2) := by
  have hn1 : 1 ≤ n₁ := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hn1r : (1:ℝ) ≤ n₁ := by exact_mod_cast hn1
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx2 : x ^ 2 ≤ y ^ 2 * ((m:ℝ) ^ r) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hx h 2
  have hM : (m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2 ≤ ((m:ℝ) ^ 2) ^ t := by
    have h1 : ((m:ℝ) ^ 2) ^ (r + 1) = (m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2 := by ring
    rw [← h1, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith) (by push_cast; linarith)
  have hcast : ((n₁ * m ^ 2 : ℕ) : ℝ) ^ t = (n₁ : ℝ) ^ t * ((m:ℝ) ^ 2) ^ t := by
    push_cast
    exact Real.mul_rpow (by positivity) (by positivity)
  have hN : (0:ℝ) < (n₁ : ℝ) ^ t := Real.rpow_pos_of_pos (by linarith) t
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  rw [hcast]
  calc x ^ 2 / ((n₁ : ℝ) ^ t * ((m:ℝ) ^ 2) ^ t)
      ≤ (y ^ 2 * ((m:ℝ) ^ r) ^ 2) / ((n₁ : ℝ) ^ t * ((m:ℝ) ^ 2 * ((m:ℝ) ^ r) ^ 2)) :=
        div_le_div₀ (by positivity) hx2 (by positivity) (mul_le_mul_of_nonneg_left hM hN.le)
    _ = y ^ 2 / (n₁ : ℝ) ^ t * (1 / (m:ℝ) ^ 2) := by
        field_simp

theorem UpperTheory.V.Af.Rs.arSum :
    UpperTheory.V.Af.Rs.ArSum := by
  intro r t a b P ht hP h3 hsu
  have ht0 : 0 < t := by have : (0:ℝ) ≤ r := Nat.cast_nonneg r; linarith
  set u : ℕ → ℝ := fun n => ‖a n‖ ^ 2 / (n:ℝ) ^ t with hu
  set w : ℕ → ℂ := fun n => starRingEnd ℂ (b n) * a n / (((n:ℝ) ^ t : ℝ) : ℂ) with hw
  have h3' : ∀ n : ℕ, ∃ q : ℕ × ℕ, 1 ≤ n → a n ≠ 0 →
      q.1 ∈ P ∧ n = q.1 * q.2 ^ 2 ∧ ‖a n‖ ≤ ‖a q.1‖ * (q.2:ℝ) ^ r ∧ ‖b n‖ ≤ ‖a q.1‖ * (q.2:ℝ) ^ r := by
    intro n
    by_cases hc : 1 ≤ n ∧ a n ≠ 0
    · obtain ⟨n₁, hn₁, m, h1, h2, h4⟩ := h3 n hc.1 hc.2
      exact ⟨(n₁, m), fun _ _ => ⟨hn₁, h1, h2, h4⟩⟩
    · exact ⟨(0, 0), fun h1 h2 => absurd ⟨h1, h2⟩ hc⟩
  choose φ hφ using h3'
  set Q : Set ℕ := {n | n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0} with hQ
  set c : ℕ → ℝ := ({m | 2 ≤ m} : Set ℕ).indicator (fun m => 1 / (m:ℝ) ^ 2) with hc
  set g : ℕ × ℕ → ℝ := fun q => P.indicator u q.1 * c q.2 with hg
  set G : ℕ → ℝ := Q.indicator (fun n => g (φ n)) with hG
  have hu0 : ∀ n, 0 ≤ u n := fun n => by simp only [hu]; positivity
  have hc0 : ∀ m, 0 ≤ c m := fun m => by
    simp only [hc]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _
  have hPu : Summable (P.indicator u) := hsu.indicator P
  have hzeta : Summable (fun m : ℕ => 1 / (m:ℝ) ^ 2) := hasSum_zeta_two.summable
  have hcs : Summable c := hzeta.indicator _
  have hgs : Summable g :=
    summable_mul_of_summable_norm (f := P.indicator u) (g := c)
      (summable_norm_iff.mpr hPu) (summable_norm_iff.mpr hcs)
  have hg0 : ∀ q, 0 ≤ g q := fun q =>
    mul_nonneg (Set.indicator_nonneg (fun n _ => hu0 n) _) (hc0 _)
  have hinj : Function.Injective (fun x : Q => φ x.1) := by
    intro x y hxy
    have hxQ : x.1 ∉ P ∧ 1 ≤ x.1 ∧ a x.1 ≠ 0 := x.2
    have hyQ : y.1 ∉ P ∧ 1 ≤ y.1 ∧ a y.1 ≠ 0 := y.2
    have hx := hφ x.1 hxQ.2.1 hxQ.2.2
    have hy := hφ y.1 hyQ.2.1 hyQ.2.2
    apply Subtype.ext
    simp only at hxy
    rw [hx.2.1, hy.2.1, hxy]
  have hGs : Summable G := by
    rw [hG, ← summable_subtype_iff_indicator]
    exact hgs.comp_injective hinj
  have hc34 : ∑' m, c m ≤ 3 / 4 := by
    have e1 := hzeta.sum_add_tsum_nat_add 2
    have e2 := hcs.sum_add_tsum_nat_add 2
    have s2 : ∑ i ∈ Finset.range 2, c i = 0 := by simp [Finset.sum_range_succ, hc]
    have s1 : ∑ i ∈ Finset.range 2, (1 / ((i:ℕ):ℝ) ^ 2) = 1 := by simp [Finset.sum_range_succ]
    have e3 : (fun i => c (i + 2)) = (fun i => 1 / (((i + 2 : ℕ)) : ℝ) ^ 2) := by
      funext i
      simp only [hc]
      rw [Set.indicator_of_mem (show i + 2 ∈ {m : ℕ | 2 ≤ m} by simp)]
    rw [s2, zero_add, e3] at e2
    rw [s1, hasSum_zeta_two.tsum_eq] at e1
    have hpi := Real.pi_lt_d2
    have hpi0 := Real.pi_pos
    have hpi2 : Real.pi ^ 2 < 9.93 := by nlinarith
    rw [← e2]
    linarith
  have hGle : ∑' n, G n ≤ (∑' n, P.indicator u n) * (3 / 4) := by
    rw [hG, ← tsum_subtype]
    calc ∑' x : Q, g (φ x) ≤ ∑' q, g q := tsum_comp_le_tsum_of_inj hgs hg0 hinj
      _ = (∑' n, P.indicator u n) * ∑' m, c m := by
          exact (tsum_mul_tsum_of_summable_norm (f := P.indicator u) (g := c)
            (summable_norm_iff.mpr hPu) (summable_norm_iff.mpr hcs)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hc34
          (tsum_nonneg (fun n => Set.indicator_nonneg (fun n _ => hu0 n) _))
  have hpt : ∀ n, ‖w n‖ ≤ P.indicator u n + G n ∧
      6 * P.indicator u n - 8 * G n ≤ 7 * (w n).re - u n := by
    intro n
    by_cases hn : n ∈ P
    · have hGn : G n = 0 := by
        simp only [hG]
        have hnQ : n ∉ Q := fun h => by
          have h' : n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0 := h
          exact h'.1 hn
        exact Set.indicator_of_notMem hnQ _
      have hPn : P.indicator u n = u n := Set.indicator_of_mem hn u
      have hwn : w n = ((u n : ℝ) : ℂ) := by
        simp only [hw, hu]
        rw [hP n hn, Complex.conj_mul']
        push_cast
        ring
      rw [hGn, hPn, hwn, Complex.norm_real, Real.norm_of_nonneg (hu0 n), Complex.ofReal_re]
      constructor <;> linarith [hu0 n]
    · have hPn : P.indicator u n = 0 := Set.indicator_of_notMem hn u
      by_cases hq : 1 ≤ n ∧ a n ≠ 0
      · have hφn := hφ n hq.1 hq.2
        have hGn : G n = P.indicator u (φ n).1 * c (φ n).2 := by
          simp only [hG, hg]
          exact Set.indicator_of_mem (show n ∈ Q from ⟨hn, hq.1, hq.2⟩) _
        rcases hφq : φ n with ⟨n₁, m⟩
        rw [hφq] at hφn hGn
        obtain ⟨hn₁P, hnm, hA, hB⟩ := hφn
        simp only at hn₁P hnm hA hB hGn
        rcases Nat.lt_or_ge m 2 with hlt | hm2
        · exfalso
          interval_cases m
          · simp at hnm
            omega
          · simp at hnm
            exact hn (hnm ▸ hn₁P)
        have hc2 : c m = 1 / (m:ℝ) ^ 2 := by
          simp only [hc]
          exact Set.indicator_of_mem (show m ∈ {m : ℕ | 2 ≤ m} from hm2) _
        have hPn1 : P.indicator u n₁ = u n₁ := Set.indicator_of_mem hn₁P u
        rw [hc2, hPn1] at hGn
        have h1n : 1 ≤ n₁ * m ^ 2 := hnm ▸ hq.1
        have k1 := arSum_term r t ht ‖a n‖ ‖a n₁‖ n₁ m (norm_nonneg _) h1n hA
        have k2 := arSum_term r t ht ‖b n‖ ‖a n₁‖ n₁ m (norm_nonneg _) h1n hB
        rw [← hnm] at k1 k2
        have hnt : 0 < (n:ℝ) ^ t := Real.rpow_pos_of_pos (by exact_mod_cast hq.1) t
        have hwn : ‖w n‖ = ‖b n‖ * ‖a n‖ / (n:ℝ) ^ t := by
          simp only [hw]
          rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hnt.le]
        have hw2 : ‖w n‖ ≤ G n := by
          rw [hwn, hGn]
          have hab : ‖b n‖ * ‖a n‖ ≤ (‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖a n‖ - ‖b n‖)]
          calc ‖b n‖ * ‖a n‖ / (n:ℝ) ^ t ≤ ((‖a n‖ ^ 2 + ‖b n‖ ^ 2) / 2) / (n:ℝ) ^ t := by gcongr
            _ = (‖a n‖ ^ 2 / (n:ℝ) ^ t + ‖b n‖ ^ 2 / (n:ℝ) ^ t) / 2 := by ring
            _ ≤ _ := by simp only [hu]; linarith
        have hun : u n ≤ G n := by
          rw [hGn]
          simp only [hu]
          exact k1
        have hre : -‖w n‖ ≤ (w n).re := by
          have := Complex.abs_re_le_norm (w n)
          linarith [neg_abs_le (w n).re]
        rw [hPn]
        constructor <;> linarith
      · have hGn : G n = 0 := by
          simp only [hG]
          have hnQ : n ∉ Q := fun h => by
            have h' : n ∉ P ∧ 1 ≤ n ∧ a n ≠ 0 := h
            exact hq ⟨h'.2.1, h'.2.2⟩
          exact Set.indicator_of_notMem hnQ _
        have hz : w n = 0 ∧ u n = 0 := by
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · subst h0
            simp [hw, hu, Real.zero_rpow (ne_of_gt ht0)]
          · have han : a n = 0 := by
              by_contra h
              exact hq ⟨h0, h⟩
            simp [hw, hu, han]
        rw [hPn, hGn, hz.1, hz.2]
        simp
  have hws : Summable w := Summable.of_norm_bounded (hPu.add hGs) (fun n => (hpt n).1)
  have hres : Summable (fun n => (w n).re) :=
    Summable.of_norm_bounded (hPu.add hGs)
      (fun n => by rw [Real.norm_eq_abs]; exact (Complex.abs_re_le_norm _).trans (hpt n).1)
  rw [Complex.re_tsum hws]
  have hD := Summable.tsum_le_tsum (fun n => (hpt n).2)
    ((hPu.mul_left 6).sub (hGs.mul_left 8)) ((hres.mul_left 7).sub hsu)
  rw [Summable.tsum_sub (hPu.mul_left 6) (hGs.mul_left 8),
    Summable.tsum_sub (hres.mul_left 7) hsu, Summable.tsum_mul_left 6 hPu,
    Summable.tsum_mul_left 8 hGs, Summable.tsum_mul_left 7 hres] at hD
  linarith [hGle]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.CharEq2
section
theorem UpperTheory.V.Af.Rs.charEq2 :
    UpperTheory.V.Af.Rs.Core → UpperTheory.V.Af.Rs.Deplete → UpperTheory.V.Af.Rs.CharEq2 := by
  intro hCore hDep k N M _ _ hk χ ψ g h hev
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨B, hB⟩ := hev.bddAbove
  obtain ⟨L, hL⟩ : ∃ L, L = N * M * B.factorial := ⟨_, rfl⟩
  haveI : NeZero L := ⟨by
    rw [hL]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne M)) (Nat.factorial_ne_zero B)⟩
  haveI : NeZero (L * L) := ⟨Nat.mul_ne_zero (NeZero.ne L) (NeZero.ne L)⟩
  have hNL : N ∣ L := ⟨M * B.factorial, by rw [hL]; ring⟩
  have hML : M ∣ L := ⟨N * B.factorial, by rw [hL]; ring⟩
  obtain ⟨χ1, g1, hg1⟩ := hDep k N L hk hNL χ g
  obtain ⟨χ2, h1, hh1⟩ := hDep k M L hk hML ψ h
  have good : ∀ p, Nat.Prime p → ¬ p ∣ L → (h.a p = g.a p ∧ (starRingEnd ℂ) (g.a p) * χ p = g.a p ∧
      (starRingEnd ℂ) (h.a p) * ψ p = h.a p) := by
    intro p hp hpL
    by_contra hbad
    have hle : p ≤ B := hB (by simp only [Set.mem_setOf_eq]; exact fun H => hbad (H hp))
    exact hpL (hL ▸ Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos hle) _)
  have hcore := hCore k (L * L) hk χ1 χ2 g1 h1 ?_ ?_
  · rw [Filter.eventually_cofinite]
    apply ((Finset.range (L + 1)).finite_toSet).subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_cases hpL : p ∣ L
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) hpL)
    · exfalso
      apply hp
      intro hpp
      rw [← ((hg1 p hpp).1 hpL).1, ← ((hh1 p hpp).1 hpL).1, hcore]
  · intro p hp
    by_cases hpL : p ∣ L
    · rw [(hg1 p hp).2 hpL, (hh1 p hp).2 hpL]
    · rw [((hh1 p hp).1 hpL).2, ((hg1 p hp).1 hpL).2]
      exact (good p hp hpL).1
  · intro p hp hne
    by_cases hpL : p ∣ L
    · exact (hg1 p hp).2 hpL
    · obtain ⟨e1, e2, e3⟩ := good p hp hpL
      rw [((hg1 p hp).1 hpL).2]
      by_contra ha
      apply hne
      rw [((hg1 p hp).1 hpL).1, ((hh1 p hp).1 hpL).1]
      rw [e1] at e3
      have hc : (starRingEnd ℂ) (g.a p) ≠ 0 := by simpa using ha
      exact mul_left_cancel₀ hc (e2.trans e3.symm)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ClsExKey
section
open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

private theorem clsEx_key (L : ℕ) (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ)
    (hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ z, F (γ • z) = ψ ((γ 1 1 : ℤ) : ZMod L) * F z)
    (n m : ℕ) (γ δ : SL(2, ℤ))
    (h : UpperTheory.V.Af.Rs.cls L ((m : ℤ) • UpperTheory.V.Af.Rs.row δ) = UpperTheory.V.Af.Rs.cls L ((n : ℤ) • UpperTheory.V.Af.Rs.row γ))
    (z : ℍ) : ψ (m : ZMod L) * F (δ • z) = ψ (n : ZMod L) * F (γ • z) := by
  classical
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [UpperTheory.V.Af.Rs.cls, UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
    Int.cast_natCast] at h0 h1
  have hdet : ((γ 0 0 : ℤ) : ZMod L) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast congrArg (fun t : ℤ => (t : ZMod L)) this
  have hn : (n : ZMod L) = m * (((γ 0 0 : ℤ) : ZMod L) * (δ 1 1 : ℤ) - (γ 0 1 : ℤ) * (δ 1 0 : ℤ)) := by
    linear_combination (-(n : ZMod L)) * hdet - ((γ 0 0 : ℤ) : ZMod L) * h1 +
      ((γ 0 1 : ℤ) : ZMod L) * h0
  by_cases hm : IsUnit (m : ZMod L)
  · obtain ⟨η, hη⟩ : ∃ η : SL(2, ℤ), η = δ * γ⁻¹ := ⟨_, rfl⟩
    have e10 : (η 1 0 : ℤ) = δ 1 0 * γ 1 1 - δ 1 1 * γ 1 0 := by
      rw [hη]
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have e11 : (η 1 1 : ℤ) = δ 1 1 * γ 0 0 - δ 1 0 * γ 0 1 := by
      rw [hη]
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hmem : η ∈ Gamma0 L := by
      rw [Gamma0_mem, e10]
      push_cast
      refine (hm.mul_right_eq_zero).1 ?_
      linear_combination ((γ 1 1 : ℤ) : ZMod L) * h0 - ((γ 1 0 : ℤ) : ZMod L) * h1
    have hδ : δ = η * γ := by
      rw [hη, inv_mul_cancel_right]
    have hn' : (n : ZMod L) = m * ((η 1 1 : ℤ) : ZMod L) := by
      rw [e11, hn]
      push_cast
      ring
    rw [hδ, mul_smul, hF η hmem, hn', map_mul]
    ring
  · have hn' : ¬IsUnit (n : ZMod L) := by
      intro hu
      rw [hn] at hu
      exact hm (isUnit_of_mul_isUnit_left hu)
    rw [MulChar.map_nonunit _ hm, MulChar.map_nonunit _ hn']
    simp

theorem UpperTheory.V.Af.Rs.clsEx :
    UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.ClsEx := by
  intro _ L _ ψ F hF
  classical
  refine ⟨fun v z => if h : ∃ p : ℕ × SL(2, ℤ), cls L ((p.1 : ℤ) • row p.2) = v then
    ψ (h.choose.1 : ZMod L) * F (h.choose.2 • z) else 0, ?_⟩
  intro n γ z
  have h : ∃ p : ℕ × SL(2, ℤ), cls L ((p.1 : ℤ) • row p.2) = cls L ((n : ℤ) • row γ) := ⟨(n, γ), rfl⟩
  simp only [dif_pos h]
  exact clsEx_key L ψ F hF n _ γ _ h.choose_spec z
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.FdCount
section
open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

theorem UpperTheory.V.Af.Rs.fdCount :
    UpperTheory.V.Af.Rs.FdNull → UpperTheory.V.Af.Rs.FdCount := by
  intro hN
  unfold UpperTheory.V.Af.Rs.FdNull at hN
  unfold UpperTheory.V.Af.Rs.FdCount
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hnull : ∀ γ : SL(2, ℤ),
      volume ((fun z : ℍ => γ • z) ⁻¹' (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
    intro γ
    have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
    rw [this, measure_preimage_smul]
    exact hN
  have hB := measure_iUnion_null hnull
  rw [ae_iff]
  refine measure_mono_null ?_ hB
  intro z hz
  by_contra hzB
  simp only [mem_iUnion, mem_preimage, not_exists] at hzB
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hgo : g • z ∈ ModularGroup.fdo := by
    by_contra h
    exact hzB g ⟨hg, h⟩
  have hne : g ≠ -g := by
    intro h
    have h1 : (1 : SL(2, ℤ)) = -1 := by
      have := congrArg (fun A => A * g⁻¹) h
      simpa using this
    have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1
    simp at this
  apply hz
  rw [tsum_eq_sum (s := {g, -g}) ?_]
  · rw [Finset.sum_pair hne]
    have hg' : (-g) • z ∈ ModularGroup.fd := by simpa using hg
    rw [indicator_of_mem hg, indicator_of_mem hg', one_add_one_eq_two]
  · intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
    apply indicator_of_notMem
    intro hmem
    have heq : γ • z = (γ * g⁻¹) • (g • z) := by
      rw [smul_smul, inv_mul_cancel_right]
    rw [heq] at hmem
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hgo hmem with h | h
    · exact hγ.1 (mul_inv_eq_one.mp h)
    · apply hγ.2
      rw [mul_inv_eq_iff_eq_mul] at h
      rw [h]
      simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.PetChar
section
open CongruenceSubgroup UpperTheory.V.Af
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

theorem UpperTheory.V.Af.Rs.petChar :
    UpperTheory.V.Af.Rs.PetChar := by
  intro k L _ χ ψ f g hf hg γ hγ z
  have h := UpperHalfPlane.petersson_slash_SL (k : ℤ) g f γ z
  rw [hg γ hγ, hf γ hγ] at h
  rw [← h]
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply,
    MulChar.star_apply', MulChar.mul_apply]
  ring
end

