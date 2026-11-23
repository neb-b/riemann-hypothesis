module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0007

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZFinal
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

attribute [local irreducible] q0 pY pJ pN in
theorem final_bound_of_assembly : FinalOf := by
  rintro ⟨C, hC0, hC⟩ hDet hBC hNum
  obtain ⟨Q₀, C', hQ₀, hN⟩ := hNum C hC0
  classical

  let F : Finset PC := (range ⌈Q₀⌉₊).sigma (fun N => @Finset.univ (DirichletCharacter ℂ (N + 1)) (Fintype.ofFinite _))
  refine ⟨max C' ((F.card : ℝ) + 1), fun Q S hQ hS => ?_⟩
  have hQ14 : (1 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hQ14' : (0 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := by linarith
  rcases lt_or_ge Q Q₀ with hQQ | hQQ
  ·
    have hsub : S ⊆ F := by
      intro p hp
      obtain ⟨-, hpQ, -⟩ := hS p hp
      simp only [F, mem_sigma, mem_range, mem_univ, and_true]
      have h1 : ((p.1 : ℕ) : ℝ) < Q₀ := by push_cast at hpQ; linarith
      have h2 : (Q₀ : ℝ) ≤ (⌈Q₀⌉₊ : ℝ) := Nat.le_ceil Q₀
      exact_mod_cast h1.trans_le h2
    have hc : (S.card : ℝ) ≤ F.card := by exact_mod_cast card_le_card hsub
    calc (S.card : ℝ) ≤ (F.card : ℝ) + 1 := by linarith
      _ ≤ max C' ((F.card : ℝ) + 1) := le_max_right _ _
      _ = max C' ((F.card : ℝ) + 1) * 1 := (mul_one _).symm
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hQ14 (le_trans (by positivity) (le_max_right _ _))
  ·
    obtain ⟨hsm, hfin⟩ := hN Q hQQ
    have hQ20 : (20 : ℝ) ≤ Q := le_trans hQ₀ hQQ
    set J := pJ Q with hJdef
    have hJ1 : 1 ≤ J := by rw [hJdef]; unfold pJ; omega
    have hY1 : 1 ≤ pY Q := by
      unfold pY
      have : 1 ≤ q0 Q := by unfold q0; exact Nat.one_le_iff_ne_zero.mpr (by
        intro h; rw [Nat.ceil_eq_zero] at h; linarith)
      exact Nat.one_le_pow _ _ (by omega)

    have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun p : PC => p.1 = 0)
    set S' := S.filter (fun p : PC => ¬ p.1 = 0) with hS'
    have h0 : (S.filter (fun p : PC => p.1 = 0)).card ≤ 1 := by
      refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      obtain ⟨Na, χa⟩ := a
      obtain ⟨Nb, χb⟩ := b
      simp only [mem_filter] at ha hb
      obtain ⟨-, rfl⟩ := ha
      obtain ⟨-, rfl⟩ := hb
      have e1 : χa = 1 := DirichletCharacter.level_one' _ rfl
      have e2 : χb = 1 := DirichletCharacter.level_one' _ rfl
      rw [e1, e2]

    let ρ : PC → ℂ := fun p => if h : (∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧
        DirichletCharacter.LFunction p.2 s = 0) then h.choose else 0
    have hρ : ∀ p ∈ S, 1 - 1 / 400 < (ρ p).re ∧ |(ρ p).im| ≤ Q ∧ DirichletCharacter.LFunction p.2 (ρ p) = 0 := by
      intro p hp
      have h := (hS p hp).2.2
      simp only [ρ, dif_pos h]
      exact h.choose_spec
    let jf : PC → ℕ := fun p => if h : (∃ j ∈ range J, 1 / (2 * (J : ℝ)) ≤
        ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p (ρ p)‖) then h.choose else 0
    have hne1 : ∀ p ∈ S', p.2 ≠ 1 := by
      intro p hp h
      simp only [hS', mem_filter] at hp
      have hc : p.2.conductor = p.1 + 1 := (hS p hp.1).1
      rw [h, DirichletCharacter.conductor_one] at hc
      omega
    have hjf : ∀ p ∈ S', jf p ∈ range J ∧
        1 / (2 * (J : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ (jf p)) p (ρ p)‖ := by
      intro p hp
      have hpS : p ∈ S := (mem_filter.1 hp).1
      have hp0 : p.1 ≠ 0 := (mem_filter.1 hp).2
      obtain ⟨hprim, hlev, -⟩ := hS p hpS
      obtain ⟨h1, h2, h3⟩ := hρ p hpS
      have h := hDet Q hQ20 p hprim hp0 hlev (ρ p) (by unfold s0; exact h1) h2 h3
      rw [← hJdef] at h
      simp only [jf, dif_pos h]
      exact h.choose_spec
    have hre1 : ∀ p ∈ S', (ρ p).re < 1 := by
      intro p hp
      by_contra hc
      push Not at hc
      have hpS : p ∈ S := (mem_filter.1 hp).1
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re p.2 (Or.inl (hne1 p hp)) hc (hρ p hpS).2.2

    have hfib := Finset.card_eq_sum_card_fiberwise (f := jf) (s := S') (t := range J) (fun p hp => (hjf p hp).1)
    set K : ℕ := pY Q * 2 ^ J with hK
    have hKpos : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hblock : ∀ j ∈ range J, ((S'.filter (fun p => jf p = j)).card : ℝ) ≤
        8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ) := by
      intro j hj
      have hU : 1 ≤ pY Q * 2 ^ j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
      have h := hBC C hC0 hC Q (by linarith) (pY Q) (pN Q) (pY Q * 2 ^ j) J hU hJ1 (hsm j hj)
        (S'.filter (fun p => jf p = j)) ρ (by
          intro p hp
          obtain ⟨hpS', hpj⟩ := mem_filter.1 hp
          have hpS : p ∈ S := (mem_filter.1 hpS').1
          obtain ⟨hprim, hlev, -⟩ := hS p hpS
          obtain ⟨h1, h2, -⟩ := hρ p hpS
          refine ⟨hprim, hlev, by unfold s0; exact h1, hre1 p hpS', h2, ?_⟩
          have := (hjf p hpS').2
          rw [hpj] at this
          exact this)
      refine h.trans ?_
      have hUK : ((pY Q * 2 ^ j : ℕ) : ℝ) ≤ K := by
        have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (mem_range.1 hj).le
        exact_mod_cast Nat.mul_le_mul_left _ this
      have hrp : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (K : ℝ) ^ (3 / 200 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hUK (by norm_num)
      have : (0 : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C := by positivity
      exact mul_le_mul_of_nonneg_left hrp this
    have hS'card : (S'.card : ℝ) ≤ (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      rw [hfib]; push_cast
      refine (sum_le_sum hblock).trans ?_
      rw [sum_const, card_range, nsmul_eq_mul]
    have htot : (S.card : ℝ) ≤ 1 + (J : ℝ) * (8 * (J : ℝ) ^ 2 * C * (K : ℝ) ^ (3 / 200 : ℝ)) := by
      have : (S.card : ℝ) = (S.filter (fun p : PC => p.1 = 0)).card + S'.card := by
        rw [← hcard]; push_cast; ring
      rw [this]
      have : ((S.filter (fun p : PC => p.1 = 0)).card : ℝ) ≤ 1 := by exact_mod_cast h0
      linarith
    calc (S.card : ℝ) ≤ C' * Q ^ (1 / 4 : ℝ) := htot.trans hfin
      _ ≤ max C' ((F.card : ℝ) + 1) * Q ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hQ14'

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll
section
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

lemma mco_one {Y N : ℕ} (hY : 1 ≤ Y) (hN : 1 ≤ N) : mco Y N 1 = 1 := by
  unfold mco
  have h : (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = 1) = {(1, 1)} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_Icc, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨ha1, -⟩, hb1, -⟩, h⟩
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨⟨le_rfl, hY⟩, le_rfl, hN⟩, rfl⟩
  rw [h, sum_singleton]
  simp

lemma mco_filter_eq_antidiag {Y N n : ℕ} (hn : 1 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product, mem_Icc, Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨h, by omega⟩
  · rintro ⟨h, -⟩
    have ha : a ≠ 0 := by
      rintro rfl
      omega
    have hb : b ≠ 0 := by
      rintro rfl
      omega
    have ha' : a ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro b h)
    have hb' : b ≤ n := Nat.le_of_dvd (by omega) (Dvd.intro_left a h)
    exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, h⟩

lemma mco_filter_subset_antidiag {Y N n : ℕ} (hn : 1 ≤ n) :
    (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n) ⊆ n.divisorsAntidiagonal := by
  intro x hx
  rw [mem_filter] at hx
  rw [Nat.mem_divisorsAntidiagonal]
  exact ⟨hx.2, by omega⟩

lemma mco_sum_moebius_divisors {n : ℕ} (hn : 2 ≤ n) : ∑ i ∈ n.divisors, (μ i : ℤ) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  simp only [coe_mul_zeta_apply] at h
  rw [h, one_apply_ne (by omega)]

lemma mco_eq_zero {Y N n : ℕ} (h2 : 2 ≤ n) (hnY : n ≤ Y) (hYN : Y ≤ N) : mco Y N n = 0 := by
  unfold mco
  rw [mco_filter_eq_antidiag (by omega) hnY hYN]
  have h := Nat.sum_divisorsAntidiagonal (fun a _ => ((μ a : ℤ) : ℂ)) (n := n)
  rw [h]
  exact_mod_cast mco_sum_moebius_divisors h2

lemma mco_norm_le (Y N : ℕ) {n : ℕ} (hn : 1 ≤ n) : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := by
  unfold mco
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (sum_le_sum (g := fun _ => (1 : ℝ)) ?_) ?_
  · intro p _
    have h1 := abs_moebius_le_one (n := p.1)
    first
      | (rw [Complex.norm_intCast]; exact_mod_cast h1)
      | (rw [Complex.norm_int]; exact_mod_cast h1)
      | (rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]; exact_mod_cast h1)
  · rw [sum_const, nsmul_eq_mul, mul_one]
    have hc := card_le_card (mco_filter_subset_antidiag (Y := Y) (N := N) hn)
    have he : n.divisorsAntidiagonal.card = n.divisors.card := by
      first
        | exact Nat.card_divisorsAntidiagonal_eq_card_divisors n
        | (rw [← Nat.map_div_right_divisors, card_map])
    rw [he] at hc
    exact_mod_cast hc

theorem mollifier_identity : MollId := by
  unfold MollId
  intro q _ χ s Y N K hY hYN hK
  have hN : 1 ≤ N := le_trans hY hYN
  have hYK : Y ≤ K := by
    calc Y = Y * 1 := (mul_one Y).symm
      _ ≤ Y * N := Nat.mul_le_mul le_rfl hN
      _ ≤ K := hK
  have hmaps : ∀ p ∈ Icc 1 Y ×ˢ Icc 1 N, p.1 * p.2 ∈ Icc 1 K := by
    intro p hp
    simp only [mem_product, mem_Icc] at hp ⊢
    constructor
    · have := Nat.mul_le_mul hp.1.1 hp.2.1
      simpa using this
    · exact le_trans (Nat.mul_le_mul hp.1.2 hp.2.2) hK
  rw [sum_mul]
  simp_rw [mul_sum]
  rw [sum_comm, ← sum_product',
    ← sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 * p.2) (t := Icc 1 K) hmaps]
  calc _ = ∑ k ∈ Icc 1 K, mco Y N k * χ k * (k : ℂ) ^ (-s) := by
        apply sum_congr rfl
        intro k _
        unfold mco
        rw [sum_mul, sum_mul]
        apply sum_congr rfl
        intro p hp
        rw [mem_filter] at hp
        obtain ⟨-, hpk⟩ := hp
        subst hpk
        simp only [Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
        ring
    _ = 1 + ∑ n ∈ Ioc Y K, mco Y N n * χ n * (n : ℂ) ^ (-s) := by
        have hsplit : Icc 1 K = Icc 1 Y ∪ Ioc Y K := by
          ext k
          simp only [mem_union, mem_Icc, mem_Ioc]
          omega
        have hdisj : Disjoint (Icc 1 Y) (Ioc Y K) := by
          rw [disjoint_left]
          intro k hk hk'
          rw [mem_Icc] at hk
          rw [mem_Ioc] at hk'
          omega
        rw [hsplit, sum_union hdisj]
        congr 1
        rw [sum_eq_single 1]
        · rw [mco_one hY hN]
          simp
        · intro k hk hk1
          rw [mem_Icc] at hk
          rw [mco_eq_zero (by omega) hk.2 hYN]
          simp
        · intro h
          exact absurd (mem_Icc.mpr ⟨le_rfl, hY⟩) h

theorem coefficient_square_bound : CoeffSqOf := by
  unfold CoeffSqOf
  intro hD
  unfold CoeffSq
  unfold FX.DivisorBound at hD
  have hs0 : s0 = 399 / 400 := by
    unfold s0
    norm_num
  obtain ⟨C, hC⟩ := hD (1 / 400) (by norm_num)
  have hC1 : 1 ≤ C := by
    have h := hC 1 le_rfl
    simpa using h
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro Y N U hU
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U),
      (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) := le_trans (mco_norm_le Y N hn1) (hC n hn1)
    have h2 : (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) = (n : ℝ) ^ (-(199 / 200 : ℝ)) := by
      rw [← Real.rpow_add hnpos, hs0]
      norm_num
    have h3 : (n : ℝ) ^ (-(199 / 200 : ℝ)) ≤ (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      first
        | exact Real.rpow_le_rpow_of_nonpos hUpos hUn (by norm_num)
        | exact Real.rpow_le_rpow_of_exponent_nonpos hUpos hUn (by norm_num)
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_anti₀ (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
        | (rw [Real.rpow_neg hnpos.le, Real.rpow_neg hUpos.le]
           exact inv_le_inv_of_le (Real.rpow_pos_of_pos hUpos _) (Real.rpow_le_rpow hUpos.le hUn (by norm_num)))
    have h4 : 0 ≤ ‖mco Y N n‖ * (n : ℝ) ^ (-s0) := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hnpos.le _)
    have h5 : ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := by
      calc ‖mco Y N n‖ * (n : ℝ) ^ (-s0) ≤ C * (n : ℝ) ^ (1 / 400 : ℝ) * (n : ℝ) ^ (-s0) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hnpos.le _)
        _ = C * (n : ℝ) ^ (-(199 / 200 : ℝ)) := by rw [mul_assoc, h2]
        _ ≤ C * (U : ℝ) ^ (-(199 / 200 : ℝ)) := mul_le_mul_of_nonneg_left h3 (by linarith)
    first
      | exact pow_le_pow_left h4 h5 2
      | exact pow_le_pow_left₀ h4 h5 2
      | nlinarith
  have e1 : ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 = (U : ℝ) ^ (-(199 / 100 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hUpos.le]
    norm_num
  have e2 : (U : ℝ) * (U : ℝ) ^ (-(199 / 100 : ℝ)) = (U : ℝ) ^ (-(99 / 100 : ℝ)) := by
    rw [show (U : ℝ) ^ (-(99 / 100 : ℝ)) = (U : ℝ) ^ ((1 : ℝ) + -(199 / 100 : ℝ)) by norm_num,
      Real.rpow_add hUpos, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) * (C * (U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2 := by
        rw [sum_const, Nat.card_Ioc, show 2 * U - U = U by omega, nsmul_eq_mul]
    _ = C ^ 2 * ((U : ℝ) * ((U : ℝ) ^ (-(199 / 200 : ℝ))) ^ 2) := by ring
    _ = C ^ 2 * (U : ℝ) ^ (-(99 / 100 : ℝ)) := by rw [e1, e2]
    _ ≤ C ^ 2 * (U : ℝ) ^ (-(197 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)) (by positivity)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZNum
section
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

attribute [local irreducible] q0 pY pJ pN in
theorem numeric_constants : Num := by
  intro C hC
  have h3 := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (by norm_num : (0 : ℝ) < 7 / 100)).bound
    (by norm_num : (0 : ℝ) < 1 / 32768)
  have h2 := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 47 / 50)).bound
    (by positivity : (0 : ℝ) < 1 / (65536 * (C + 1)))
  obtain ⟨Q1, hQ1⟩ := Filter.eventually_atTop.1 (h3.and h2)
  refine ⟨max 20 Q1, 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ), le_max_left _ _, fun Q hQ => ?_⟩
  have hQ20 : 20 ≤ Q := (le_max_left _ _).trans hQ
  obtain ⟨hl3, hl2⟩ := hQ1 Q ((le_max_right _ _).trans hQ)
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le hQ0]
    have := Real.exp_one_lt_d9
    linarith
  have hlog0 : 0 ≤ Real.log Q := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog0 _),
    abs_of_nonneg (Real.rpow_nonneg hQ0.le _)] at hl3 hl2
  have hl3' : Real.log Q ^ 3 ≤ 1 / 32768 * Q ^ (7 / 100 : ℝ) := by
    have e : Real.log Q ^ (3 : ℝ) = Real.log Q ^ 3 := by simpa using Real.rpow_natCast (Real.log Q) 3
    rw [← e]
    exact hl3
  have hl2' : Real.log Q ^ 2 ≤ 1 / (65536 * (C + 1)) * Q ^ (47 / 50 : ℝ) := by
    have e : Real.log Q ^ (2 : ℝ) = Real.log Q ^ 2 := by simpa using Real.rpow_natCast (Real.log Q) 2
    rw [← e]
    exact hl2
  have hq1 : Q ≤ (q0 Q : ℝ) := by rw [q0]; exact Nat.le_ceil Q
  have hq2 : (q0 Q : ℝ) ≤ 2 * Q := by
    rw [q0]
    have := Nat.ceil_lt_add_one hQ0.le
    linarith
  have hqpos : 0 < q0 Q := by exact_mod_cast lt_of_lt_of_le hQ0 hq1
  have hL2 : 2 ^ Nat.log 2 (q0 Q) ≤ q0 Q := Nat.pow_log_le_self 2 hqpos.ne'
  have hJdef : pJ Q = 8 * (Nat.log 2 (q0 Q) + 1) := by rw [pJ]
  have hYdef : pY Q = q0 Q ^ 4 := by rw [pY]
  have hLr : (Nat.log 2 (q0 Q) : ℝ) * Real.log 2 ≤ Real.log Q + Real.log 2 := by
    have h1 : ((2 ^ Nat.log 2 (q0 Q) : ℕ) : ℝ) ≤ q0 Q := by exact_mod_cast hL2
    push_cast at h1
    have h4 : Real.log ((2 : ℝ) ^ Nat.log 2 (q0 Q)) ≤ Real.log (2 * Q) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_pow, Real.log_mul (by norm_num) hQ0.ne'] at h4
    linarith
  have hlt2 := Real.log_two_gt_d9
  have hlt2' := Real.log_two_lt_d9
  have hL' : (Nat.log 2 (q0 Q) : ℝ) ≤ 3 * Real.log Q := by
    by_contra hc
    push_neg at hc
    nlinarith [(Nat.cast_nonneg (Nat.log 2 (q0 Q)) : (0 : ℝ) ≤ _)]
  have hJ : (pJ Q : ℝ) ≤ 32 * Real.log Q := by
    rw [hJdef]
    push_cast
    linarith
  have hJpos : (0 : ℝ) < pJ Q := by rw [hJdef]; positivity
  constructor
  · intro j _
    have hY : Q ^ 4 ≤ ((pY Q * 2 ^ j : ℕ) : ℝ) := by
      rw [hYdef]
      push_cast
      have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      calc Q ^ 4 ≤ (q0 Q : ℝ) ^ 4 := by gcongr
        _ ≤ (q0 Q : ℝ) ^ 4 * 2 ^ j := le_mul_of_one_le_right (by positivity) h1
    have hpow : ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤ Q ^ (-(197 / 50 : ℝ)) := by
      calc ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤ (Q ^ 4) ^ (-(197 / 200 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hY (by norm_num)
        _ = Q ^ (-(197 / 50 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
            norm_num
    have hQ3 : Q ^ 3 * Q ^ (-(197 / 50 : ℝ)) = Q ^ (-(47 / 50 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hQ0]
      norm_num
    have hQ47 : Q ^ (47 / 50 : ℝ) * Q ^ (-(47 / 50 : ℝ)) = 1 := by
      rw [← Real.rpow_add hQ0]
      norm_num
    have hkey : 64 * C * (pJ Q : ℝ) ^ 2 ≤ Q ^ (47 / 50 : ℝ) := by
      have hJ2 : (pJ Q : ℝ) ^ 2 ≤ 1024 * Real.log Q ^ 2 := by nlinarith
      have hC1 : C / (C + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      calc 64 * C * (pJ Q : ℝ) ^ 2 ≤ 64 * C * (1024 * Real.log Q ^ 2) := by gcongr
        _ ≤ 64 * C * (1024 * (1 / (65536 * (C + 1)) * Q ^ (47 / 50 : ℝ))) := by gcongr
        _ = C / (C + 1) * Q ^ (47 / 50 : ℝ) := by field_simp; ring
        _ ≤ 1 * Q ^ (47 / 50 : ℝ) := by gcongr
        _ = Q ^ (47 / 50 : ℝ) := one_mul _
    rw [le_div_iff₀ (by positivity)]
    calc 8 * Q ^ 3 * C * ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) * (8 * (pJ Q : ℝ) ^ 2)
        ≤ 8 * Q ^ 3 * C * Q ^ (-(197 / 50 : ℝ)) * (8 * (pJ Q : ℝ) ^ 2) := by gcongr
      _ = (64 * C * (pJ Q : ℝ) ^ 2) * (Q ^ 3 * Q ^ (-(197 / 50 : ℝ))) := by ring
      _ ≤ Q ^ (47 / 50 : ℝ) * Q ^ (-(47 / 50 : ℝ)) := by rw [hQ3]; gcongr
      _ = 1 := hQ47
  · have hJ2 : (2 : ℕ) ^ pJ Q ≤ 256 * q0 Q ^ 8 := by
      rw [hJdef, pow_mul', pow_succ]
      calc (2 ^ Nat.log 2 (q0 Q) * 2) ^ 8 = 256 * (2 ^ Nat.log 2 (q0 Q)) ^ 8 := by ring
        _ ≤ 256 * q0 Q ^ 8 := by gcongr
    have hYJ : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ 1048576 * Q ^ 12 := by
      have h1 : pY Q * 2 ^ pJ Q ≤ q0 Q ^ 4 * (256 * q0 Q ^ 8) := by
        rw [hYdef]
        exact Nat.mul_le_mul_left _ hJ2
      have h4 : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ (q0 Q : ℝ) ^ 4 * (256 * (q0 Q : ℝ) ^ 8) := by
        exact_mod_cast h1
      calc ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ≤ (q0 Q : ℝ) ^ 4 * (256 * (q0 Q : ℝ) ^ 8) := h4
        _ ≤ (2 * Q) ^ 4 * (256 * (2 * Q) ^ 8) := by gcongr
        _ = 1048576 * Q ^ 12 := by ring
    have hpow : ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤
        (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ) := by
      calc ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ) ≤ (1048576 * Q ^ 12) ^ (3 / 200 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hYJ (by norm_num)
        _ = (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast Q 12,
              ← Real.rpow_mul hQ0.le]
            norm_num
    have hJ3 : (pJ Q : ℝ) ^ 3 ≤ Q ^ (7 / 100 : ℝ) := by
      calc (pJ Q : ℝ) ^ 3 ≤ (32 * Real.log Q) ^ 3 := by gcongr
        _ = 32768 * Real.log Q ^ 3 := by ring
        _ ≤ 32768 * (1 / 32768 * Q ^ (7 / 100 : ℝ)) := by gcongr
        _ = Q ^ (7 / 100 : ℝ) := by ring
    have hQ14 : 1 ≤ Q ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hsplit : Q ^ (7 / 100 : ℝ) * Q ^ (9 / 50 : ℝ) = Q ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hQ0]
      norm_num
    calc 1 + (pJ Q : ℝ) * (8 * (pJ Q : ℝ) ^ 2 * C * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ))
        = 1 + 8 * C * ((pJ Q : ℝ) ^ 3 * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ)) := by ring
      _ ≤ 1 + 8 * C * (Q ^ (7 / 100 : ℝ) * ((1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (9 / 50 : ℝ))) := by
          gcongr
      _ = 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * (Q ^ (7 / 100 : ℝ) * Q ^ (9 / 50 : ℝ)) := by ring
      _ = 1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (1 / 4 : ℝ) := by rw [hsplit]
      _ ≤ Q ^ (1 / 4 : ℝ) + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ) * Q ^ (1 / 4 : ℝ) := by gcongr
      _ = (1 + 8 * C * (1048576 : ℝ) ^ (3 / 200 : ℝ)) * Q ^ (1 / 4 : ℝ) := by ring

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

