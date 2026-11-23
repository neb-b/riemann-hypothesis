module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensPair
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0008
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0018
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLoc

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensBlock
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma char_mul_conj_self {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (a : ZMod M) :
    χ a * (starRingEnd ℂ) (χ a) = (1 : DirichletCharacter ℂ M) a := by
  have h : (starRingEnd ℂ) (χ a) = χ⁻¹ a := MulChar.star_apply' χ a
  rw [h, ← MulChar.mul_apply, mul_inv_cancel]

lemma char_mul_conj {M : ℕ} [NeZero M] (χ χ' : DirichletCharacter ℂ M) (a : ZMod M) :
    χ a * (starRingEnd ℂ) (χ' a) = (χ * χ'⁻¹) a := by
  have h : (starRingEnd ℂ) (χ' a) = χ'⁻¹ a := MulChar.star_apply' χ' a
  rw [h, ← MulChar.mul_apply]

lemma offdiag_term {M : ℕ} [NeZero M] (σ T : ℝ) (U : ℕ) (hU : 1 ≤ U) (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ)
    (p p' : DirichletCharacter ℂ M × ℂ)
    (hp : σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) (hp' : σ ≤ p'.2.re ∧ p'.2.re ≤ 1 ∧ |p'.2.im| ≤ T)
    (hsp : p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) :
    ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (if p' = p then (U : ℝ) else 0) +
        (if p'.1 = p.1 then 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) else 0) +
        4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
  obtain ⟨hl, hu, hi⟩ := hp
  obtain ⟨hl', hu', hi'⟩ := hp'
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  set w : ℂ := (p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ)) with hw
  have hwre : w.re = p.2.re + p'.2.re - 2 * σ := by
    simp only [hw, add_re, sub_re, ofReal_re, conj_re]; ring
  have hwim : w.im = p.2.im - p'.2.im := by
    simp only [hw, add_im, sub_im, ofReal_im, conj_im]; ring
  have hw0 : 0 ≤ w.re := by rw [hwre]; linarith
  have hw1 : w.re ≤ 1 := by rw [hwre]; linarith
  have hwn : ‖w‖ ≤ 1 + 2 * T := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_nonneg hw0, hwim]
    have : |p.2.im - p'.2.im| ≤ |p.2.im| + |p'.2.im| := abs_sub _ _
    linarith
  have hB : 4 * ((M : ℝ) + 1) * (1 + ‖w‖) ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
    have : 1 + ‖w‖ ≤ 2 + 2 * T := by linarith
    gcongr
  have hB0 : 0 ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hq0 : 0 ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by positivity
  by_cases h1 : p' = p
  · rw [if_pos h1, if_pos (by rw [h1])]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-w)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ n ∈ Ioc U (2 * U), ‖p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w)‖ ≤ 1 := by
        intro n hn
        have hn1 : 1 ≤ n := by have := (mem_Ioc.1 hn).1; omega
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have a1 : ‖p.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a2 : ‖p'.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a3 : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := norm_natCast_cpow_neg_le_one hn1 hw0
        calc ‖p.1 (n : ZMod M)‖ * ‖p'.1 (n : ZMod M)‖ * ‖(n : ℂ) ^ (-w)‖ ≤ 1 * 1 * 1 := by
              gcongr
          _ = 1 := by norm_num
      refine (sum_le_sum this).trans ?_
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
      exact_mod_cast (by omega : 2 * U - U ≤ U)
    linarith
  · rw [if_neg h1]
    by_cases h2 : p'.1 = p.1
    · rw [if_pos h2]
      have hgap : 1 ≤ |p.2.im - p'.2.im| := hsp (fun h => h1 h.symm) h2.symm
      have him : w.im ≠ 0 := by
        rw [hwim]; intro h0; rw [h0, abs_zero] at hgap; linarith
      have hsame := pair_same_bound M w hw0 hw1 him U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [h2, char_mul_conj_self]
      rw [heq]
      have hUp : (U : ℝ) ^ (1 - w.re) ≤ U := by
        calc (U : ℝ) ^ (1 - w.re) ≤ (U : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
          _ = U := Real.rpow_one _
      have hdiv : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by
        rw [hwim, mul_one_div]
        gcongr
      linarith
    · rw [if_neg h2]
      have hne : p.1 * p'.1⁻¹ ≠ 1 := by
        intro h; exact h2 (mul_inv_eq_one.1 h).symm
      have hcross := pair_cross_bound M (p.1 * p'.1⁻¹) hne w hw0 U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (p.1 * p'.1⁻¹) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [char_mul_conj]
      rw [heq]
      linarith

theorem off_diagonal_bound : Offdiag := by
  intro M _ S σ T U hU hT hσ hS hsp p hp
  classical
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hterm := fun p' (hp' : p' ∈ S) =>
    offdiag_term σ T U hU hT hσ p p' (hS p hp) (hS p' hp') (hsp p hp p' hp')
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq' S p, if_pos hp,
    ← sum_filter, ← mul_sum]
  set Fib : Finset (DirichletCharacter ℂ M × ℂ) := S.filter (fun p' => p'.1 = p.1) with hFib
  set P : Finset ℝ := Fib.image (fun p' => p'.2.im) with hP
  have hinj : Set.InjOn (fun p' : DirichletCharacter ℂ M × ℂ => p'.2.im) (Fib : Set _) := by
    intro a ha b hb hab
    have ha' := mem_filter.1 (mem_coe.1 ha)
    have hb' := mem_filter.1 (mem_coe.1 hb)
    by_contra hne
    have := hsp a ha'.1 b hb'.1 hne (ha'.2.trans hb'.2.symm)
    simp only at hab
    rw [hab, sub_self, abs_zero] at this
    linarith
  have hpF : p ∈ Fib := mem_filter.2 ⟨hp, rfl⟩
  have htP : p.2.im ∈ P := mem_image_of_mem _ hpF
  have hsp' := (zero_spacing P T (by linarith)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      exact (hS a (mem_filter.1 ha).1).2.2)
    (by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
      have ha' := mem_filter.1 ha
      have hb' := mem_filter.1 hb
      exact hsp a ha'.1 b hb'.1 (fun h => hxy (by rw [h])) (ha'.2.trans hb'.2.symm))).2 _ htP
  have hsumeq : ∑ p' ∈ Fib, 1 / |p.2.im - p'.2.im| = ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| := by
    rw [← add_zero (∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x|)]
    have h0 : (0 : ℝ) = 1 / |p.2.im - p.2.im| := by simp
    rw [h0, sum_erase_add P _ htP, hP, sum_image hinj]
  rw [hsumeq]
  have hc0 : (0 : ℝ) ≤ S.card := by positivity
  have hB0 : 0 ≤ ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have h1 : 4 * (U : ℝ) * ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| ≤
      4 * (U : ℝ) * (2 * (1 + Real.log (2 * T + 1))) := by gcongr
  have h2 : (S.card : ℝ) * (4 * ((M : ℝ) + 1) * (2 + 2 * T)) ≤
      (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    nlinarith
  linarith

lemma conj_natCast_cpow_neg' (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by
  have h := Complex.cpow_conj (n : ℂ) (-z) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [map_neg] at h
  rw [h, Complex.conj_natCast]

theorem dyadic_block_count : BlockCnt := by
  intro α S f ρ Y N U σ θ G K hU hθ hσ hG hK hf hρ hoff hlarge hsmall
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(σ : ℂ)) with hb
  set v : α → ℕ → ℂ := fun p n => f p n * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) with hv
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hbv : ∀ p, ∀ n ∈ Ioc U (2 * U), b n * v p n = mco Y N n * f p n * (n : ℂ) ^ (-ρ p) := by
    intro p n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    have : (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) = (n : ℂ) ^ (-ρ p) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    simp only [hb, hv]
    rw [← this]; ring
  have hsum : ∀ p, ∑ n ∈ Ioc U (2 * U), b n * v p n = blkD Y N U (f p) (ρ p) := by
    intro p; unfold blkD; exact sum_congr rfl (hbv p)
  have heq : ∀ p p', ∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n) =
      ∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) *
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
    intro p p'
    refine sum_congr rfl (fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    simp only [hv]
    rw [map_mul, conj_natCast_cpow_neg']
    have : (n : ℂ) ^ (-(ρ p - (σ : ℂ))) * (n : ℂ) ^ (-(starRingEnd ℂ) (ρ p' - (σ : ℂ))) =
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    rw [← this]; ring
  have hΔ : ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n)‖ ≤
      (U : ℝ) * G + (S.card : ℝ) * K := by
    intro p hp
    simp only [heq]
    exact hoff p hp
  have hΔ0 : (0 : ℝ) ≤ (U : ℝ) * G + (S.card : ℝ) * K := by positivity
  have hmain := duality_inequality α ℕ S (Ioc U (2 * U)) b v _ hΔ0 hΔ
  simp only [hsum] at hmain
  set a : ℝ := 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 with ha
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ a := by
    refine le_trans (le_of_eq ?_) (coefficient_block_bound Y N U σ hU hσ)
    refine sum_congr rfl (fun n hn => ?_)
    have hn1 : 0 < n := by have := (mem_Ioc.1 hn).1; omega
    simp only [hb, norm_mul, norm_natCast_cpow_of_pos hn1, neg_re, ofReal_re]
  have hlow : (S.card : ℝ) * θ ^ 2 ≤ ∑ p ∈ S, ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
    have : ∀ p ∈ S, θ ^ 2 ≤ ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
      intro p hp
      exact pow_le_pow_left₀ hθ.le (hlarge p hp) 2
    have h := sum_le_sum this
    rw [sum_const, nsmul_eq_mul] at h
    exact h
  have haU : a * U = 2 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
    have : (U : ℝ) ^ (2 - 2 * σ) = (U : ℝ) ^ (1 - 2 * σ) * (U : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hU0]; congr 1; ring
    rw [this, Real.rpow_one, ha]; ring
  have h1 : (S.card : ℝ) * θ ^ 2 ≤ a * ((U : ℝ) * G + (S.card : ℝ) * K) :=
    hlow.trans (hmain.trans (mul_le_mul_of_nonneg_right hbn hΔ0))
  have hS0 : (0 : ℝ) ≤ S.card := by positivity
  have h2 : (S.card : ℝ) * θ ^ 2 ≤ 2 * (a * U) * G := by
    have := mul_le_mul_of_nonneg_left hsmall hS0
    nlinarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  rw [le_div_iff₀ hθ2]
  rw [haU] at h2
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplLocL
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_centre_re (t : ℝ) : ((101 / 100 : ℂ) + t * I).re = 101 / 100 := by
  simp only [add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero, mul_one, sub_self]
  have : ((101 / 100 : ℂ)).re = 101 / 100 := by
    have h : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ) := by push_cast; ring
    rw [h, ofReal_re]
  rw [this]; ring

theorem ex_centre_norm (t : ℝ) : ‖(101 / 100 : ℂ) + t * I‖ ≤ 101 / 100 + |t| := by
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(101 / 100 : ℂ)‖ = 101 / 100 := by
    have h : (101 / 100 : ℂ) = ((101 / 100 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have h2 : ‖(t : ℂ) * I‖ = |t| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, h2]

theorem ex_centre_lower {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (t : ℝ) :
    1 / 10100 ≤ ‖exLF χ ((101 / 100 : ℂ) + t * I)‖ := by
  have hre := ex_centre_re t
  have h := exLF_lower χ ((101 / 100 : ℂ) + t * I) (by rw [hre]; norm_num)
  rw [hre] at h
  have h1 : (1 / 100 : ℝ) ≤ ‖(101 / 100 : ℂ) + t * I - 1‖ := by
    have h2 := Complex.abs_re_le_norm ((101 / 100 : ℂ) + t * I - 1)
    rw [sub_re, hre, one_re] at h2
    rw [abs_of_pos (by norm_num)] at h2
    linarith
  have h3 : (1 / 100 : ℝ) ≤ min 1 ‖(101 / 100 : ℂ) + t * I - 1‖ := le_min (by norm_num) h1
  have h4 : (1 / 100 : ℝ) * ((101 / 100 - 1) / (101 / 100)) ≤
      min 1 ‖(101 / 100 : ℂ) + t * I - 1‖ * ((101 / 100 - 1) / (101 / 100)) :=
    mul_le_mul_of_nonneg_right h3 (by norm_num)
  refine le_trans ?_ (h4.trans h)
  norm_num

theorem ex_log_bound (C0 : ℝ) (hC0 : 1 ≤ C0) (M : ℕ) (hM : 3 ≤ M) (t : ℝ) :
    1 ≤ C0 * M * (|t| + 3) ^ 2 * 10100 ∧
    0 ≤ Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ∧
    Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ≤
      (Real.log (C0 * 10100) + 3) * Real.log ((M : ℝ) * (|t| + 2)) := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have ht : 0 ≤ |t| := abs_nonneg t
  have hB1 : 1 ≤ C0 * M * (|t| + 3) ^ 2 * 10100 := by
    have h1 : 1 ≤ C0 * M := by nlinarith
    have h2 : 1 ≤ (|t| + 3) ^ 2 := by nlinarith
    have h3 : 1 ≤ C0 * M * (|t| + 3) ^ 2 := by nlinarith
    linarith
  refine ⟨hB1, Real.log_nonneg hB1, ?_⟩
  set X : ℝ := (M : ℝ) * (|t| + 2) with hX
  have hX6 : 6 ≤ X := by rw [hX]; nlinarith
  have hX0 : 0 < X := by linarith
  have hMX : (M : ℝ) ≤ X := by rw [hX]; nlinarith
  have htX : |t| + 3 ≤ X := by rw [hX]; nlinarith
  have hlogX : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hK : 1 ≤ C0 * 10100 := by linarith
  have hK0 : 0 ≤ Real.log (C0 * 10100) := Real.log_nonneg hK
  have hle : C0 * M * (|t| + 3) ^ 2 * 10100 ≤ C0 * 10100 * X ^ 3 := by
    have h1 : (|t| + 3) ^ 2 ≤ X ^ 2 := by gcongr
    have h2 : (M : ℝ) * (|t| + 3) ^ 2 ≤ X * X ^ 2 := by
      apply mul_le_mul hMX h1 (by positivity) hX0.le
    have h3 : C0 * 10100 * ((M : ℝ) * (|t| + 3) ^ 2) ≤ C0 * 10100 * (X * X ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    calc C0 * M * (|t| + 3) ^ 2 * 10100 = C0 * 10100 * ((M : ℝ) * (|t| + 3) ^ 2) := by ring
      _ ≤ C0 * 10100 * (X * X ^ 2) := h3
      _ = C0 * 10100 * X ^ 3 := by ring
  have h5 : Real.log (C0 * M * (|t| + 3) ^ 2 * 10100) ≤ Real.log (C0 * 10100 * X ^ 3) :=
    Real.log_le_log (by linarith) hle
  have h6 : Real.log (C0 * 10100 * X ^ 3) = Real.log (C0 * 10100) + 3 * Real.log X := by
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    push_cast; ring
  rw [h6] at h5
  nlinarith

theorem ex_local : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (t : ℝ), 3 ≤ M →
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((101 / 100 : ℂ) + t * I) (2 / 15) ∧ exLF χ ρ = 0)) ∧
      ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ s ∈ Metric.closedBall ((101 / 100 : ℂ) + t * I) (1 / 15), exLF χ s ≠ 0 →
        ‖deriv (exLF χ) s / exLF χ s - ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ)‖ ≤
          C * Real.log ((M : ℝ) * (|t| + 2)) := by
  obtain ⟨C0, hC0, hG⟩ := exLF_growth
  have hK0 : 0 ≤ Real.log (C0 * 10100) := Real.log_nonneg (by linarith)
  refine ⟨180 * (Real.log (C0 * 10100) + 3), by linarith, ?_⟩
  intro M _ χ t hM
  obtain ⟨hB1, hB0, hBlog⟩ := ex_log_bound C0 hC0 M hM t
  set B : ℝ := C0 * M * (|t| + 3) ^ 2 * 10100 with hB
  set z₀ : ℂ := (101 / 100 : ℂ) + t * I with hz₀
  have hlow : 1 / 10100 ≤ ‖exLF χ z₀‖ := ex_centre_lower χ t
  have hne : exLF χ z₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hlow; norm_num at hlow
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hbound : ∀ z ∈ Metric.closedBall z₀ (2 / 5), ‖exLF χ z‖ ≤ B * ‖exLF χ z₀‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hre : 1 / 2 ≤ z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      rw [sub_re, hz₀, ex_centre_re t] at h1
      have h2 := (abs_le.1 (h1.trans hz)).1
      linarith
    have hn : ‖z‖ ≤ |t| + 2 := by
      have h1 : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := by
        have := norm_add_le (z - z₀) z₀
        rwa [sub_add_cancel] at this
      have h2 := ex_centre_norm t
      rw [← hz₀] at h2
      linarith
    have h3 : (1 + ‖z‖) ^ 2 ≤ (|t| + 3) ^ 2 := by
      have : 0 ≤ ‖z‖ := norm_nonneg z
      exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h4 : C0 * M * (1 + ‖z‖) ^ 2 ≤ C0 * M * (|t| + 3) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hM0)
    have h5 : B * (1 / 10100) ≤ B * ‖exLF χ z₀‖ := mul_le_mul_of_nonneg_left hlow (by linarith)
    have h6 : B * (1 / 10100) = C0 * M * (|t| + 3) ^ 2 := by rw [hB]; ring
    linarith [hG M χ z hre]
  obtain ⟨Z, hZ1, -, hZ3, hZ4⟩ := ex_landau_ord (exLF χ) z₀ (2 / 5) B (by norm_num) hB1
    (exLF_differentiable χ).differentiableOn hne hbound
  have e3 : (2 / 5 : ℝ) / 3 = 2 / 15 := by norm_num
  have e6 : (2 / 5 : ℝ) / 6 = 1 / 15 := by norm_num
  rw [e3] at hZ1
  rw [e6] at hZ4
  refine ⟨Z, hZ1, ?_, ?_⟩
  · have h2 : Real.log B / Real.log 2 ≤ 180 * Real.log B := by
      have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have h3 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 := hZ3
    calc ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) ≤ 180 * Real.log B := h3.trans h2
      _ ≤ 180 * (Real.log (C0 * 10100) + 3) * Real.log ((M : ℝ) * (|t| + 2)) := by linarith
  · intro s hs hs0
    have h1 : ‖deriv (exLF χ) s / exLF χ s - ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ)‖ ≤
        72 * Real.log B / (2 / 5) := hZ4 s hs hs0
    have h2 : 72 * Real.log B / (2 / 5) = 180 * Real.log B := by ring
    rw [h2] at h1
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

