module

public import Mathlib
public import Formalism.PieriBlockIdeals.Bundle0002
public import Formalism.PieriBlockIdeals.PieriColumnMinors.Bundle0001

@[expose] public section

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.LocalComponentGL
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

theorem windowResidueCountEqZero_holds : NoResidue := by
  intro l b t κ U hU
  rw [mwCount]
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_of_forall_notMem
  intro u hu'
  simp only [Finset.mem_filter] at hu'
  obtain ⟨hu, x, hx, hxu⟩ := hu'
  have hd : (l : ℤ) ∣ u - x := Int.ModEq.dvd hxu
  rcases hU u hu.1 hu.2 x hx with ⟨h1, h2⟩ | h
  · have h0 := Int.eq_zero_of_abs_lt_dvd hd h2
    rw [h0, abs_zero] at h1
    exact lt_irrefl 0 h1
  · exact h hd

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.LogarithmEquivalence
section
noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

theorem eq_of_dvd_of_abs_lt_sq {L : ℝ} (hL : 0 ≤ L) {n : ℤ} (hn : n ≠ 0) (hnL : ((|n| : ℤ) : ℝ) < L ^ 2)
    {l l' : ℕ} (hl : l.Prime) (hl' : l'.Prime) (hLl : L < (l : ℝ)) (hLl' : L < (l' : ℝ))
    (hd : (l : ℤ) ∣ n) (hd' : (l' : ℤ) ∣ n) : l = l' := by
  by_contra hne
  have hcop : IsCoprime (l : ℤ) (l' : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hl hl').mpr hne
  have hmul : (l : ℤ) * l' ∣ |n| := by
    rw [dvd_abs]
    exact hcop.mul_dvd hd hd'
  have hle : (l : ℤ) * l' ≤ |n| := Int.le_of_dvd (abs_pos.mpr hn) hmul
  have hle' : (l : ℝ) * l' ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hle
  have hsq : L ^ 2 < (l : ℝ) * l' := by
    rw [sq]
    exact mul_lt_mul'' hLl hLl' hL hL
  linarith

theorem largePrimeDivisorCount_holds : PrimeCount := by
  intro L T P hL hT hP
  choose! f hfT hfd using fun l (hl : l ∈ P) => (hP l hl).2.2
  apply Finset.card_le_card_of_injOn f
  · intro l hl
    exact hfT l hl
  · intro l hl l' hl' heq
    have h1 := hT (f l) (hfT l hl)
    refine eq_of_dvd_of_abs_lt_sq hL h1.1 h1.2 (hP l hl).1 (hP l' hl').1 (hP l hl).2.1
      (hP l' hl').2.1 (hfd l hl) ?_
    rw [heq]
    exact hfd l' hl'

theorem residueIndicatorPrimeSum_holds : ISum := by
  intro h L xm xp mB P hL hhL hmB hmx hxx hxh hP
  obtain ⟨P', hP'⟩ : ∃ P' : Finset ℕ,
      P' = P.filter (fun l : ℕ => ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB) := ⟨_, rfl⟩
  have hmem : ∀ l, l ∈ P' ↔ l ∈ P ∧ ∃ y : ℤ, xm ≤ y ∧ y ≤ xp ∧ (l : ℤ) ∣ y - mB := by
    intro l
    rw [hP', Finset.mem_filter]
  choose! g hg1 hg2 hg3 using fun l (hl : l ∈ P') => ((hmem l).mp hl).2
  have hh1 : (1 : ℝ) ≤ h := by
    have : (1 : ℤ) ≤ h := by omega
    exact_mod_cast this
  have hlogh : 0 ≤ Real.log (h : ℝ) := Real.log_nonneg hh1
  have hterm : ∀ l ∈ P', Real.log (l : ℝ) ≤ Real.log (h : ℝ) := by
    intro l hl
    have hlP := ((hmem l).mp hl).1
    have hpos : 0 < g l - mB := by
      have := hg1 l hl
      omega
    have hdle : (l : ℤ) ≤ g l - mB := Int.le_of_dvd hpos (hg3 l hl)
    have hle : (l : ℤ) ≤ h := by
      have := hg2 l hl
      omega
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (hP l hlP).1.pos
    exact Real.log_le_log hl0 (by exact_mod_cast hle)
  have hcard : P'.card ≤ (Finset.Icc xm xp).card := by
    apply Finset.card_le_card_of_injOn g
    · intro l hl
      exact Finset.mem_Icc.mpr ⟨hg1 l hl, hg2 l hl⟩
    · intro l hl l' hl' heq
      have hlP := ((hmem l).mp hl).1
      have hlP' := ((hmem l').mp hl').1
      have hpos : 0 < g l - mB := by
        have := hg1 l hl
        omega
      have hlt : ((|g l - mB| : ℤ) : ℝ) < L ^ 2 := by
        have h1 : |g l - mB| ≤ (h : ℤ) := by
          rw [abs_of_pos hpos]
          have := hg2 l hl
          omega
        have h2 : ((|g l - mB| : ℤ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast h1
        linarith
      refine eq_of_dvd_of_abs_lt_sq hL hpos.ne' hlt (hP l hlP).1 (hP l' hlP').1 (hP l hlP).2
        (hP l' hlP').2 (hg3 l hl) ?_
      rw [heq]
      exact hg3 l' hl'
  have hcardR : ((Finset.Icc xm xp).card : ℝ) = ((xp - xm : ℤ) : ℝ) + 1 := by
    have h0 : (0 : ℤ) ≤ xp + 1 - xm := by omega
    rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg h0]
    push_cast
    ring
  have key : ∑ l ∈ P', Real.log (l : ℝ) ≤ (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ) := by
    calc ∑ l ∈ P', Real.log (l : ℝ) ≤ ∑ _l ∈ P', Real.log (h : ℝ) := Finset.sum_le_sum hterm
      _ = (P'.card : ℝ) * Real.log (h : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Finset.Icc xm xp).card : ℝ) * Real.log (h : ℝ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlogh
      _ = (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ) := by rw [hcardR]
  refine Eq.trans_le ?_ key
  rw [hP', Finset.sum_filter]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold IlInd
  split_ifs <;> simp

end Formalism.CohomologicalDescent
end
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.MaxValEqZeroOfLt
section
open Finset

namespace Formalism.CohomologicalDescent

theorem max_val_eq_zero_of_lt (l n : ℕ) (h : n < l) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l n = 0 := by
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hp : l.Prime
  · apply le_of_eq
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hdf : l ∣ n.factorial := hd.trans ⟨i.factorial * (n - i).factorial, by
      rw [← Nat.choose_mul_factorial_mul_factorial hi']; ring⟩
    have := (Nat.Prime.dvd_factorial hp).mp hdf
    omega
  · exact (Nat.factorization_eq_zero_of_not_prime _ hp).le

end Formalism.CohomologicalDescent
end

-- bundled from Formalism.PieriBlockIdeals.PieriColumnMinors.WeightExchangeChainHolds
section
noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

theorem map_cast_image_val_eq (l N : ℕ) (W : Fin N → ℤ) (hW : StrictAnti W) :
    Multiset.map (fun u : ℤ => (u : ZMod l)) (Finset.univ.image W).val =
      Multiset.map (fun a => ((W a : ℤ) : ZMod l)) Finset.univ.val := by
  rw [Finset.image_val_of_injOn hW.injective.injOn, Multiset.map_map]
  rfl

theorem sum_filter_block_eq (k j t q : ℕ) (U : Fin (k + j + t + q) → ℤ) (b : ℤ)
    (hblock : ∀ a : Fin (k + j + t + q), k + j ≤ (a : ℕ) → (a : ℕ) < k + j + t →
      U a = b + ((k + j + t - 1 - (a : ℕ) : ℕ) : ℤ)) :
    ∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a =
      ∑ s : Fin t, (b + ((s : ℕ) : ℤ)) := by
  refine Finset.sum_bij'
    (fun a ha => (⟨k + j + t - 1 - (a : ℕ), by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      omega⟩ : Fin t))
    (fun s _ => (⟨k + j + t - 1 - (s : ℕ), by
      have := s.isLt
      omega⟩ : Fin (k + j + t + q))) ?_ ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_univ _
  · intro s _
    have := s.isLt
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    ext
    simp only
    omega
  · intro s _
    have := s.isLt
    ext
    simp only
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [hblock a ha.1 ha.2]

theorem weightExchangeChain_holds : WEChain := by
  intro k j t q l h κ K _ _ U U' V V' b b' c c' kc kp hl htl hU hU' hV hV' hU0 hU'h hsum hblock hVb
    hprodU hprodV hkc hkp hmU hmV hfilt
  have hlink := contentLinkage_holds l K _ U U' c hl hprodU
  have hlinkV := contentLinkage_holds l K _ V V' c' hl hprodV
  have hmemU : ∀ s : Fin t, b + ((s : ℕ) : ℤ) ∈ Finset.univ.image U := by
    intro s
    have hs := s.isLt
    refine Finset.mem_image.mpr ⟨⟨k + j + t - 1 - (s : ℕ), by omega⟩, Finset.mem_univ _, ?_⟩
    have h1 : k + j + t - 1 - (k + j + t - 1 - (s : ℕ)) = (s : ℕ) := by omega
    rw [hblock _ (by simp only; omega) (by simp only; omega)]
    simp only [h1]
  have hmemV : ∀ s : Fin t, b' + ((s : ℕ) : ℤ) ∈ Finset.univ.image V := by
    intro s
    obtain ⟨a, ha⟩ := hVb s
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ha⟩
  have hKU : |∑ s, kc s| ≤ (mwCount l b t κ (Finset.univ.image U) : ℤ) * ((t : ℤ) + 2 * κ) := by
    refine shiftSumBound_holds l b t κ (Finset.univ.image U) kc hl.pos htl hmemU hkc ?_
    rw [map_cast_image_val_eq l _ U hU, hlink]
    exact hmU
  have hKV : |∑ s, kp s| ≤ (mwCount l b' t κ (Finset.univ.image V) : ℤ) * ((t : ℤ) + 2 * κ) := by
    refine shiftSumBound_holds l b' t κ (Finset.univ.image V) kp hl.pos htl hmemV hkp ?_
    rw [map_cast_image_val_eq l _ V hV, hlinkV]
    exact hmV
  have hfilt' : ∑ a ∈ Finset.univ.filter (fun a : Fin (k + j + t + q) => k + j + q ≤ (a : ℕ)), U' a ≤
      (∑ a ∈ Finset.univ.filter
        (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U a) +
        (l : ℤ) * (∑ s, kp s) - ∑ s, kc s := by
    rw [sum_filter_block_eq k j t q U b hblock]
    refine hfilt.trans (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact weightExchangeBound_holds k j t q l h κ _ _ U U' (∑ s, kc s) (∑ s, kp s) hU hU' hU0 hU'h hsum hfilt'
    hKU hKV

end Formalism.CohomologicalDescent
end
end

