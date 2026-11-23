module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0008
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0010
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0009
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZPair
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.DivisorBound
public import Mathlib
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailBox
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContourA
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContourB
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0005
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.Bundle0002

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZAll
section
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

theorem zero_density_box : Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZeroDensityBox :=
  final_bound_of_assembly (coefficient_square_bound Formalism.FX.divisor_weight_bound) (zero_detection mollifier_identity)
    (blockCountOf_statement duality_inequality (pair_twist_bound pair_sum_bound)) numeric_constants

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistB
section
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem coprime_of_cls {m₀ s a₀ b : ℕ} (ha : a₀.Coprime m₀) (hb : b ∈ clsB m₀ s a₀) : b.Coprime (m₀ * s) := by
  simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb
  have hm : b.Coprime m₀ := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hb.2.1, ← Nat.gcd_rec, Nat.gcd_comm]
    exact ha
  exact Nat.Coprime.mul_right hm hb.2.2

private theorem sum_clsB_mul_mod_eq_sum {M : Type*} [AddCommMonoid M] (m₀ s a₀ u : ℕ) (hN : 0 < m₀ * s)
    (hu1 : u % m₀ = 1 % m₀) (hus : u.Coprime s) (f : ℕ → M) :
    ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s)) = ∑ b ∈ clsB m₀ s a₀, f b := by
  have hcm : ∀ x k : ℕ, Nat.Coprime x k ↔ Nat.Coprime (x % k) k := fun x k => by
    rw [Nat.Coprime, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec]
  have hum : u.Coprime m₀ := by
    rw [hcm, hu1, ← hcm]
    exact Nat.coprime_one_left _
  have huN : u.Coprime (m₀ * s) := Nat.Coprime.mul_right hum hus
  have hmap : ∀ b ∈ clsB m₀ s a₀, (b * u) % (m₀ * s) ∈ clsB m₀ s a₀ := by
    intro b hb
    simp only [clsB, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨Nat.mod_lt _ hN, ?_, ?_⟩
    · rw [Nat.mod_mod_of_dvd _ (dvd_mul_right m₀ s), Nat.mul_mod, hb.2.1, hu1, ← Nat.mul_mod, mul_one]
    · rw [hcm, Nat.mod_mod_of_dvd _ (dvd_mul_left s m₀), ← hcm]
      exact Nat.Coprime.mul_left hb.2.2 hus
  have hinj : Set.InjOn (fun b => (b * u) % (m₀ * s)) (clsB m₀ s a₀) := by
    intro x hx y hy hxy
    simp only [Finset.mem_coe, clsB, Finset.mem_filter, Finset.mem_range] at hx hy
    have h := Nat.ModEq.cancel_right_of_coprime huN.symm (show x * u ≡ y * u [MOD m₀ * s] from hxy)
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] at h
  have himg : (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)) = clsB m₀ s a₀ :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hmap)
      (by rw [Finset.card_image_of_injOn hinj])
  calc ∑ b ∈ clsB m₀ s a₀, f ((b * u) % (m₀ * s))
      = ∑ x ∈ (clsB m₀ s a₀).image (fun b => (b * u) % (m₀ * s)), f x := (Finset.sum_image hinj).symm
    _ = ∑ b ∈ clsB m₀ s a₀, f b := by rw [himg]

private theorem jacobiSym_mul_mod_eq_mul (m₀ s b u : ℕ) :
    jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s = jacobiSym (b : ℤ) s * jacobiSym (u : ℤ) s := by
  rw [← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  push_cast
  exact Int.emod_emod_of_dvd _ (dvd_mul_left _ _)

private theorem exists_jacobiSym_neg_one_in_residue_class (m₀ s : ℕ) (h1 : 1 < s) (hodd : Odd s) (hsq : Squarefree s)
    (hcop : m₀.Coprime s) :
    ∃ u : ℕ, u % m₀ = 1 % m₀ ∧ u.Coprime s ∧ jacobiSym (u : ℤ) s = -1 := by
  have hp : s.minFac.Prime := Nat.minFac_prime (by omega)
  haveI := Fact.mk hp
  haveI : NeZero s := ⟨by omega⟩
  obtain ⟨t, ht⟩ := Nat.minFac_dvd s
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [mul_zero] at ht
    omega
  haveI : NeZero t := ⟨ht0⟩
  haveI : NeZero s.minFac := ⟨hp.ne_zero⟩
  have hp2 : s.minFac ≠ 2 := by
    intro h2
    rw [h2] at ht
    rw [ht] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul t)
  have hpt : s.minFac.Coprime t := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    rintro ⟨v, hv⟩
    have hu := hsq s.minFac ⟨v, by rw [mul_assoc, ← hv]; exact ht⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp hu)
  have hmp : (m₀ * t).Coprime s.minFac :=
    Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_right (Nat.minFac_dvd s) hcop) hpt.symm
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare (F := ZMod s.minFac)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  let c := Nat.chineseRemainder hmp 1 g.val
  have hc1 : (c : ℕ) ≡ 1 [MOD m₀ * t] := c.2.1
  have hc2 : (c : ℕ) ≡ g.val [MOD s.minFac] := c.2.2
  have hJ : jacobiSym ((c : ℕ) : ℤ) s = -1 := by
    have e1 : jacobiSym ((c : ℕ) : ℤ) s.minFac = -1 := by
      rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
      have hcg : (((c : ℕ) : ℤ) : ZMod s.minFac) = g := by
        rw [Int.cast_natCast, (ZMod.natCast_eq_natCast_iff _ _ _).mpr hc2, ZMod.natCast_zmod_val]
      rwa [hcg]
    have e2 : jacobiSym ((c : ℕ) : ℤ) t = 1 := by
      have hct : (c : ℕ) ≡ 1 [MOD t] := Nat.ModEq.of_mul_left m₀ hc1
      have h' : (((c : ℕ) % t : ℕ) : ℤ) = ((1 % t : ℕ) : ℤ) := congrArg _ hct
      push_cast at h'
      rw [jacobiSym.mod_left' h', jacobiSym.one_left]
    have hsplit : jacobiSym ((c : ℕ) : ℤ) s = jacobiSym ((c : ℕ) : ℤ) (s.minFac * t) := by rw [← ht]
    rw [hsplit, jacobiSym.mul_right, e1, e2]
    norm_num
  refine ⟨c, Nat.ModEq.of_mul_right t hc1, ?_, hJ⟩
  have hg1 : Int.gcd ((c : ℕ) : ℤ) s = 1 := by
    by_contra hne
    have h0 := jacobiSym.eq_zero_iff_not_coprime.mpr hne
    rw [hJ] at h0
    norm_num at h0
  rwa [Int.gcd_natCast_natCast] at hg1

theorem sum_jac_cls_eq_zero (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) :
    ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) = 0 := by
  have hN : 0 < m₀ * s := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨u, hu1, hus, hJu⟩ := exists_jacobiSym_neg_one_in_residue_class m₀ s h1 hodd hsq hcop
  have hre := sum_clsB_mul_mod_eq_sum m₀ s a₀ u hN hu1 hus (fun x => (jacobiSym (x : ℤ) s : ℝ))
  simp only [jacobiSym_mul_mod_eq_mul, hJu, Int.cast_mul, Int.cast_neg, Int.cast_one, mul_neg, mul_one,
    Finset.sum_neg_distrib] at hre
  linarith

theorem main_twist_bound (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (hli : 0 < liX X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP e b X| ≤
      2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| := by
  have hN : 0 < m₀ * s := Nat.pos_of_ne_zero (NeZero.ne _)
  have hφ : (0 : ℝ) < ((m₀ * s).totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hN
  have hsum0 := sum_jac_cls_eq_zero m₀ s a₀ h1 hodd hsq hcop ha
  have hRHS : 0 ≤ 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| := by positivity
  rcases e with _ | ⟨χ, β⟩
  · simp only [mainAP]
    rw [← Finset.sum_mul, hsum0, zero_mul, abs_zero]
    simpa [mainAP] using hRHS
  · have hexp : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP (some (χ, β)) b X =
        -(liX (X ^ β) / ((m₀ * s).totient : ℝ)) *
          ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re := by
      simp only [mainAP]
      rw [Finset.mul_sum]
      have key : ∀ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) *
          ((liX X - (χ (b : ZMod (m₀ * s))).re * liX (X ^ β)) / ((m₀ * s).totient : ℝ)) =
          (jacobiSym (b : ℤ) s : ℝ) * (liX X / ((m₀ * s).totient : ℝ)) +
          -(liX (X ^ β) / ((m₀ * s).totient : ℝ)) *
            ((jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re) := fun b _ => by ring
      rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, hsum0, zero_mul, zero_add]
    have hre1 : ∀ b : ℕ, |(χ (b : ZMod (m₀ * s))).re| ≤ 1 := fun b =>
      (Complex.abs_re_le_norm _).trans (DirichletCharacter.norm_le_one χ _)
    by_cases hc : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s →
        χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)
    · have hLb := hG χ β rfl hc
      have hS : |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re| ≤
          ((clsB m₀ s a₀).card : ℝ) := by
        calc _ ≤ ∑ b ∈ clsB m₀ s a₀, |(jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ b ∈ clsB m₀ s a₀, (1 : ℝ) := Finset.sum_le_sum fun b _ => by
              rw [abs_mul]
              have hj : |(jacobiSym (b : ℤ) s : ℝ)| ≤ 1 := by
                rcases jacobiSym.trichotomy (b : ℤ) s with h | h | h <;> simp [h]
              calc _ ≤ 1 * 1 := mul_le_mul hj (hre1 b) (abs_nonneg _) zero_le_one
                _ = 1 := one_mul 1
          _ = ((clsB m₀ s a₀).card : ℝ) := by simp
      have hlow : ∀ b ∈ clsB m₀ s a₀, liX X / (2 * ((m₀ * s).totient : ℝ)) ≤ |mainAP (some (χ, β)) b X| := by
        intro b _
        have h3 : (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) ≤ r * liX X := by
          calc (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) ≤ |(χ (b : ZMod (m₀ * s))).re * liX (X ^ β)| :=
                le_abs_self _
            _ = |(χ (b : ZMod (m₀ * s))).re| * |liX (X ^ β)| := abs_mul _ _
            _ ≤ 1 * |liX (X ^ β)| := mul_le_mul_of_nonneg_right (hre1 b) (abs_nonneg _)
            _ ≤ r * liX X := by linarith
        refine le_trans ?_ (le_abs_self _)
        simp only [mainAP]
        rw [div_le_div_iff₀ (by positivity) hφ]
        have h4 : liX X / 2 ≤ liX X - (χ (b : ZMod (m₀ * s))).re * liX (X ^ β) := by nlinarith
        nlinarith
      rw [hexp, abs_mul, abs_neg, abs_div, abs_of_pos hφ]
      calc |liX (X ^ β)| / ((m₀ * s).totient : ℝ) *
            |∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re|
          ≤ r * liX X / ((m₀ * s).totient : ℝ) * ((clsB m₀ s a₀).card : ℝ) :=
            mul_le_mul (div_le_div_of_nonneg_right hLb hφ.le) hS (abs_nonneg _) (by positivity)
        _ = 2 * r * ∑ b ∈ clsB m₀ s a₀, liX X / (2 * ((m₀ * s).totient : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp
        _ ≤ 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP (some (χ, β)) b X| :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlow) (by linarith)
    · push_neg at hc
      obtain ⟨u, hu1, hus, hne⟩ := hc
      have hpt : ∀ b : ℕ, (((jacobiSym (((b * u) % (m₀ * s) : ℕ) : ℤ) s : ℝ)) : ℂ) *
          χ ((((b * u) % (m₀ * s) : ℕ)) : ZMod (m₀ * s)) =
          (((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) *
            ((((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s))) := by
        intro b
        rw [jacobiSym_mul_mod_eq_mul, ZMod.natCast_mod, Nat.cast_mul, map_mul]
        push_cast
        ring
      have hre := sum_clsB_mul_mod_eq_sum m₀ s a₀ u hN hu1 hus
        (fun x => (((jacobiSym (x : ℤ) s : ℝ)) : ℂ) * χ (x : ZMod (m₀ * s)))
      simp only [hpt] at hre
      rw [← Finset.mul_sum] at hre
      have hgcd : Int.gcd (u : ℤ) s = 1 := by rw [Int.gcd_natCast_natCast]; exact hus
      have hc1 : (((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) ≠ 1 := by
        rcases jacobiSym.eq_one_or_neg_one hgcd with h | h
        · rw [h] at hne ⊢
          intro hh
          apply hne
          push_cast at hh ⊢
          simpa using hh
        · rw [h] at hne ⊢
          intro hh
          apply hne
          push_cast at hh ⊢
          linear_combination -hh
      have hT : ∑ b ∈ clsB m₀ s a₀, (((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
        have h0 : ((((jacobiSym (u : ℤ) s : ℝ)) : ℂ) * χ (u : ZMod (m₀ * s)) - 1) *
            ∑ b ∈ clsB m₀ s a₀, (((jacobiSym (b : ℤ) s : ℝ)) : ℂ) * χ (b : ZMod (m₀ * s)) = 0 := by
          rw [sub_mul, hre, one_mul, sub_self]
        exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc1)
      have hS0 : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (χ (b : ZMod (m₀ * s))).re = 0 := by
        have h0 := congrArg Complex.re hT
        rw [Complex.re_sum] at h0
        simpa [Complex.re_ofReal_mul] using h0
      rw [hexp, hS0, mul_zero, abs_zero]
      exact hRHS

theorem twist_one (m₀ s a₀ : ℕ) [NeZero (m₀ * s)] (hm : 0 < m₀) (h1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : m₀.Coprime s) (ha : a₀.Coprime m₀) (X r k : ℝ)
    (e : Option (DirichletCharacter ℂ (m₀ * s) × ℝ)) (hX : 0 ≤ X) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2)
    (hli : 0 < liX X) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - mainAP e b X| ≤ k * mainAP e b X)
    (hG : ∀ (χ : DirichletCharacter ℂ (m₀ * s)) (β : ℝ), e = some (χ, β) →
      (∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime s → χ (u : ZMod (m₀ * s)) = ((jacobiSym (u : ℤ) s : ℤ) : ℂ)) →
      |liX (X ^ β)| ≤ r * liX X) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤
      (4 * r + 2 * |k|) * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) := by
  have hs : 0 < s := by omega
  obtain ⟨hd, hsumabs⟩ := twist_decomp m₀ s a₀ X hm hs hX (fun b => mainAP e b X) k hk hb
  beta_reduce at hd hsumabs
  have hmain := main_twist_bound m₀ s a₀ hm h1 hodd hsq hcop ha X r e hr0 hr hli hG
  have h2 : 2 * r * ∑ b ∈ clsB m₀ s a₀, |mainAP e b X| ≤
      2 * r * (2 * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hsumabs (by linarith)
  have h3 := abs_sub_abs_le_abs_sub (∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ))
    (∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainAP e b X)
  nlinarith [hd, hmain, h2, h3, abs_nonneg k]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailContour
section
open Complex MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_contour (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 800) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (Q z η : ℝ), χ ≠ 1 → 2 ≤ Q → (N : ℝ) ≤ Q →
      Formalism.HermitianLattices.ZeroFreeRegionGL2.ZeroFreeBox Q χ → 1 ≤ z → 0 < η → η ≤ 1 →
      ‖Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ ≤
        K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + δ) + z ^ 2 / Q) := by
  obtain ⟨KB, hKB0, hKB⟩ := tail_box_negLD δ hδ
  obtain ⟨C₀, hC₀, hR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  refine ⟨160 * KB + 32 * (1 + C₀), by positivity, ?_⟩
  intro N _ χ Q z η hχ hQ hNQ hbox hz hη hη1
  have hbox' : ∀ s : ℂ, 1 - 1 / 400 + δ ≤ s.re → |s.im| ≤ Q - 1 →
      ‖Formalism.ZeroFreeDirichlet.negLD χ s‖ ≤ KB * Real.log Q := hKB N χ Q hχ hQ hNQ hbox
  set σ₁ : ℝ := 1 - 1 / 400 + δ with hσ₁
  set T : ℝ := Q / 2 with hTdef
  set Lq : ℝ := Real.log Q with hLq
  have hT0 : 0 < T := by rw [hTdef]; linarith
  have hTQ : T ≤ Q - 1 := by rw [hTdef]; linarith
  have hσa : 0 < σ₁ := by rw [hσ₁]; linarith
  have hσb : σ₁ < 1 := by rw [hσ₁]; linarith
  have hσc : 1 / 2 ≤ σ₁ := by rw [hσ₁]; linarith
  have hσd : σ₁ ≤ 1 - 1 / 800 := by rw [hσ₁]; linarith
  have hLq2 : 1 / 2 ≤ Lq := by
    have := Real.log_le_log (by norm_num) hQ
    linarith [Real.log_two_gt_d9]
  have hzf : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ 2 → |w.im| ≤ T →
      DirichletCharacter.LFunction χ w ≠ 0 := fun w h1 _ h3 =>
    hbox w (by rw [hσ₁] at h1; linarith) (by linarith)
  have hz0 : 0 < z := by linarith
  set y1 : ℝ := z + z * η with hy1def
  have hy1 : 1 ≤ y1 := by rw [hy1def]; nlinarith
  have hy12 : y1 ≤ 2 * z := by rw [hy1def]; nlinarith
  have I1 := tail_shift_identity χ hχ y1 σ₁ T hy1 hσa hσb hT0 hzf
  have I0 := tail_shift_identity χ hχ z σ₁ T hz hσa hσb hT0 hzf
  have key : (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1)
      = (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.negLD χ 1 * y1)
        - (2 * Real.pi : ℂ) * (Formalism.ZeroFreeDirichlet.Schi χ z - Formalism.ZeroFreeDirichlet.negLD χ 1 * z) := by
    rw [hy1def]; push_cast; ring
  rw [I1, I0] at key
  have hcomb := (congrArg norm key).le.trans (tc_norm_comb _ _ _ _ _ _ _ _)

  have hE : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z →
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        2 * Real.pi * (8 * (1 + C₀) * (z ^ 2 / Q)) := by
    intro y hy hy2
    have h := Formalism.ZF.norm_integral_compl_le (fun t => Formalism.ZeroFreeDirichlet.Fchi χ y (((2 : ℝ) : ℂ) + (t : ℂ) * I))
      ((1 + C₀) * (4 * z ^ 2)) T (by positivity) hT0 (fun t ht => by
        have ht0 : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht; linarith
        refine (tc_right_pt χ C₀ (fun s hs => hR N χ s hs) y t (by linarith) ht0).trans ?_
        have hyy : y ^ 2 ≤ 4 * z ^ 2 := by nlinarith
        gcongr)
    refine h.trans (le_of_eq ?_)
    rw [hTdef]; field_simp; ring

  have hH : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * z → ∀ v : ℝ, |v| = T →
      ‖∫ x in σ₁..2, Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤ 16 * KB * Lq * (z ^ 2 / Q) := by
    intro y hy hy2 v hv
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ => Formalism.ZeroFreeDirichlet.Fchi χ y ((x : ℂ) + (v : ℂ) * I))
      (C := KB * Lq * (4 * z ^ 2) / T ^ 2) (a := σ₁) (b := 2) (fun x hx => by
        rw [Set.uIoc_of_le (by linarith)] at hx
        have hM := hbox' ((x : ℂ) + (v : ℂ) * I) (by simp; exact hx.1.le)
          (by simp; rw [hv]; exact hTQ)
        refine (tc_horiz_pt χ _ y T x v hy hT0 hv hx.2 hM).trans ?_
        have hyy : y ^ 2 ≤ 4 * z ^ 2 := by nlinarith
        have hM0 : 0 ≤ KB * Real.log Q := le_trans (norm_nonneg _) hM
        gcongr)
    refine h.trans ?_
    have hlen : |2 - σ₁| ≤ 2 := by rw [abs_of_pos (by linarith)]; linarith
    have hKL : 0 ≤ KB * Lq := by positivity
    calc KB * Lq * (4 * z ^ 2) / T ^ 2 * |2 - σ₁| ≤ KB * Lq * (4 * z ^ 2) / T ^ 2 * 2 := by gcongr
      _ = 32 * (KB * Lq) * (z ^ 2 / Q) / Q := by rw [hTdef]; field_simp; ring
      _ ≤ 32 * (KB * Lq) * (z ^ 2 / Q) / 2 := by gcongr
      _ = 16 * KB * Lq * (z ^ 2 / Q) := by ring

  have hV := tc_left_int χ hχ z η σ₁ T (KB * Lq) hz0 hη.le hη1 hσc hσd hT0.le
    (fun u hu => hzf _ (by simp) (by simp; linarith) (by simpa using hu))
    (fun u hu => hbox' _ (by simp) (by simpa using hu.trans hTQ))
  rw [← hy1def] at hV
  have hlog : Real.log (1 + 800 * T) ≤ 10 * Lq := by rw [hTdef, hLq]; exact tc_log_bound Q hQ
  have hLq0 : 0 ≤ Lq := by linarith
  set A : ℝ := z ^ 2 / Q with hAdef
  set Bv : ℝ := η * z ^ σ₁ with hBvdef
  have hA0 : 0 ≤ A := div_nonneg (sq_nonneg z) (by linarith)
  have hB0 : 0 ≤ Bv := mul_nonneg hη.le (Real.rpow_nonneg hz0.le _)
  have hV' : ‖(∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ y1 ((σ₁ : ℂ) + (u : ℂ) * I))
      - ∫ u in (-T)..T, Formalism.ZeroFreeDirichlet.Fchi χ z ((σ₁ : ℂ) + (u : ℂ) * I)‖ ≤ 160 * KB * Lq ^ 2 * Bv := by
    refine hV.trans ?_
    have hn : 0 ≤ KB * Lq * (4 * η * z ^ σ₁) :=
      mul_nonneg (mul_nonneg hKB0 hLq0) (mul_nonneg (by linarith) (Real.rpow_nonneg hz0.le _))
    calc KB * Lq * (4 * η * z ^ σ₁) * (4 * Real.log (1 + 800 * T))
        ≤ KB * Lq * (4 * η * z ^ σ₁) * (4 * (10 * Lq)) := by
          apply mul_le_mul_of_nonneg_left _ hn; linarith
      _ = 160 * KB * Lq ^ 2 * Bv := by rw [hBvdef]; ring
  have hE1 := hE y1 hy1 hy12
  have hE0 := hE z hz (by linarith)
  have hHa1 := hH y1 hy1 hy12 (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hHb1 := hH y1 hy1 hy12 T (abs_of_pos hT0)
  have hHa0 := hH z hz (by linarith) (-T) (by rw [abs_neg, abs_of_pos hT0])
  have hHb0 := hH z hz (by linarith) T (abs_of_pos hT0)
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [norm_mul, hn] at hcomb
  set X := ‖Formalism.ZeroFreeDirichlet.Schi χ y1 - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1‖ with hXdef
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hW : 0 ≤ 64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv := by
    have := mul_nonneg (mul_nonneg hKB0 hLq0) hA0
    have := mul_nonneg (mul_nonneg hKB0 (sq_nonneg Lq)) hB0
    linarith
  have hWW := le_mul_of_one_le_left hW hpi
  have h2X : 2 * Real.pi * X ≤
      2 * Real.pi * (16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv)) := by
    linarith
  have hXR : X ≤ 16 * (1 + C₀) * A + (64 * KB * Lq * A + 160 * KB * Lq ^ 2 * Bv) :=
    le_of_mul_le_mul_left h2X (by positivity)
  have p1 : 0 ≤ KB * Lq * A := mul_nonneg (mul_nonneg hKB0 hLq0) hA0
  have p2 : 0 ≤ (1 + C₀) * Lq ^ 2 * Bv := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg Lq)) hB0
  have p3 : 0 ≤ (1 + C₀) * A * (2 * Lq - 1) := mul_nonneg (mul_nonneg (by linarith) hA0) (by linarith)
  have hgoal : (160 * KB + 32 * (1 + C₀)) * Lq * (Lq * η * z ^ σ₁ + A) =
      160 * KB * Lq ^ 2 * Bv + 160 * KB * Lq * A + 32 * (1 + C₀) * Lq ^ 2 * Bv
        + 32 * (1 + C₀) * Lq * A := by rw [hBvdef]; ring
  rw [hgoal]
  linarith

end Formalism.HermitianLattices.Ext.BoxTail
end
end

