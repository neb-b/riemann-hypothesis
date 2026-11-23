module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ValuationOneEqZero

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FrMemLetters
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Ord

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem llPos_lt (j : ℤ) (l l' : ℕ) (hll : l < l') (hl' : l' < (Fr.LLset j).card) : llPos Fr j l < llPos Fr j l' := by
  unfold llPos
  have hs := (Finset.sortedLT_sort (Fr.LLset j)).strictMono_get
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = (Fr.LLset j).card := Finset.length_sort _
  have e : ∀ k (hk : k < (Fr.LLset j).card), ((Fr.LLset j).sort (· ≤ ·)).getD k 0 =
      ((Fr.LLset j).sort (· ≤ ·))[k]'(by rw [hlen]; exact hk) := by
    intro k hk
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen, hk]
  rw [e l (by omega), e l' hl']
  exact hs (a := ⟨l, by rw [hlen]; omega⟩) (b := ⟨l', by rw [hlen]; exact hl'⟩) hll

private theorem fr_le_fr_of_le_of_valid (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i', i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i i' hii' hi'
  induction i', hii' using Nat.le_induction with
  | base => exact le_rfl
  | succ k hik ih => exact (ih (by omega)).trans (hV.2.2.1 j k (by omega)).le

private theorem llPos_mem_LLset' (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : llPos Fr j l ∈ Fr.LLset j := by
  unfold llPos
  have hlen : ((Fr.LLset j).sort (· ≤ ·)).length = (Fr.LLset j).card := Finset.length_sort _
  have e : ((Fr.LLset j).sort (· ≤ ·)).getD l 0 =
      ((Fr.LLset j).sort (· ≤ ·))[l]'(by rw [hlen]; exact hl) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, hlen, hl]
  rw [e, ← Finset.mem_sort (· ≤ ·)]
  exact List.getElem_mem _

theorem posU_lt (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (hab : a < b) (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a < posU Fr (Fr.LLset j).card j b := by
  have hm := fr_le_fr_of_le_of_valid hV j
  unfold posU
  split_ifs with ha hb hb
  · exact llPos_lt j a b hab hb
  · have h1 := llPos_mem_LLset' j a ha
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at h1
    exact lt_of_lt_of_le h1.1.2 (hm 0 (b - (Fr.LLset j).card) (Nat.zero_le _) (by omega))
  · omega
  · exact (hV.2.2.1 j (a - (Fr.LLset j).card) (by omega)).trans_le (hm _ _ (by omega) (by omega))

theorem posU_lt_iff (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (ha : a < (Fr.LLset j).card + r)
    (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a < posU Fr (Fr.LLset j).card j b ↔ a < b := by
  refine ⟨fun h => ?_, fun h => posU_lt hV j a b h hb⟩
  by_contra hn
  push_neg at hn
  rcases hn.lt_or_eq with h2 | h2
  · exact lt_asymm h (posU_lt hV j b a h2 ha)
  · subst h2
    exact lt_irrefl _ h

theorem posU_le_iff (hV : Fr.Valid L₁ N₁) (j : ℤ) (a b : ℕ) (ha : a < (Fr.LLset j).card + r)
    (hb : b < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j a ≤ posU Fr (Fr.LLset j).card j b ↔ a ≤ b := by
  rw [← not_lt, posU_lt_iff hV j b a hb ha, not_lt]

theorem posU_ll (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : posU Fr (Fr.LLset j).card j l = llPos Fr j l := by
  unfold posU
  rw [if_pos hl]

theorem posU_fr (j : ℤ) (i : ℕ) : posU Fr (Fr.LLset j).card j ((Fr.LLset j).card + i) = Fr.fr j i := by
  unfold posU
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

theorem w_lt_posU (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i u : ℕ) (hi : i < r) (hu : u < (Fr.LLset j).card + r) :
    Fr.fr (j - 1) i < posU Fr (Fr.LLset j).card j u := by
  have hfi : Fr.fr (j - 1) i ≤ Fr.fr (j - 1) (r - 1) := fr_le_fr_of_le_of_valid hV (j - 1) i (r - 1) (by omega) (by omega)
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  unfold posU
  split_ifs with hu'
  · have h1 := llPos_mem_LLset' j u hu'
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at h1
    exact lt_of_le_of_lt hfi h1.1.1
  · exact lt_of_le_of_lt hfi (lt_of_lt_of_le hgap (fr_le_fr_of_le_of_valid hV j 0 _ (Nat.zero_le _) (by omega)))

theorem fr_mem_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i : ℕ) (hi : i < r) : Fr.fr j i ∈ Fr.letters j := by
  have hm0 := fr_le_fr_of_le_of_valid hV (j - 1)
  have hm := fr_le_fr_of_le_of_valid hV j
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, hm i (r - 1) (by omega) (by omega)⟩, (hV.2.2.2.2.1 j i hi).1⟩
  exact (hm0 0 (r - 1) (Nat.zero_le _) (by omega)).trans (hgap.le.trans (hm 0 i (Nat.zero_le _) hi))

theorem w_mem_letters (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (i : ℕ) (hi : i < r) :
    Fr.fr (j - 1) i ∈ Fr.letters j := by
  have hm0 := fr_le_fr_of_le_of_valid hV (j - 1)
  have hm := fr_le_fr_of_le_of_valid hV j
  have hgap : Fr.fr (j - 1) (r - 1) < Fr.fr j 0 := by
    have h1 := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at h1
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨hm0 0 i (Nat.zero_le _) hi, ?_⟩, (hV.2.2.2.2.1 (j - 1) i hi).1⟩
  exact (hm0 i (r - 1) (by omega) (by omega)).trans
    (hgap.le.trans (hm 0 (r - 1) (Nat.zero_le _) (by omega)))

end Ord

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Imports
section

end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.SizeStepAlt
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem sizeStep' : ∃ CDn C₁ : ℝ, 0 < CDn ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ,
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (_hk : m + 1 = r + K) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ [NeZero F.J],
      SizeAt (K := K) p F (fun j : ZMod F.J => (F.LLset (segZ j)).card) (dT TT lam0)
        (CDn * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)) ∧
      (∀ (j : ZMod F.J) (u : ℕ), u < (fun j : ZMod F.J => (F.LLset (segZ j)).card) j + r →
        3 / 8 * slU F p (flatDeg lam0) Y (r + K) (fun j : ZMod F.J => (F.LLset (segZ j)).card) j u <
          Bo p F (flatDeg lam0) (segZ j) (posU F ((fun j : ZMod F.J => (F.LLset (segZ j)).card) j) (segZ j) u) / 2) ∧
      1 ≤ cPrime n' r TT.card c0 cpp cStar ∧ 1 ≤ F.J := by
  refine ⟨9, 4, by norm_num, by norm_num, ?_⟩
  intro C hC CLa p W Qq O Kf
  intro _ _ _ _ _ _ _ _ _ _
  intro ι σ j w n' m r
  intro _ _
  intro TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K
  intro _ _
  intro hk F nb B hD _
  have hD' := hD
  unfold DataII at hD'
  obtain ⟨-, hH, hF, -⟩ := hD'
  have hka : ((m + 1 : ℕ) : ℝ) ≤ a := k_le_a (by linarith) hH
  have hH' := hH
  unfold Hyps at hH'
  obtain ⟨hp13, hr2, hOrb, hN, hW, hY, -, hgap, -, -, hcs, hlast⟩ := hH'
  have hF' := hF
  unfold FramesOK at hF'
  obtain ⟨hF1, hV, -, -, -⟩ := hF'
  have hr : 1 ≤ r := by omega
  have hN1 : 1 ≤ orbitWindowCount r de h x := by
    unfold orbitWindowCount
    omega
  have hm : 2 ≤ m := by omega
  have hT : 1 ≤ TT.card := by
    by_contra hc
    have h0 : TT.card = 0 := by omega
    rw [h0, mul_zero] at hN
    have : 1 ≤ orbitWindowCount r de h x ^ 2 := Nat.one_le_pow _ _ hN1
    omega
  have hOrb' := hOrb
  unfold tableLineDegreeFive.OrbitHyp at hOrb'
  obtain ⟨-, -, hLU, -⟩ := hOrb'
  have hU : 1 ≤ goodU de := by omega
  have hG : goodG' r de h x ≠ 0 := by
    unfold goodG' goodEll
    exact Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by omega))
  have hA1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 m)
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hr1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hT1 : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hT
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hpl : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hQ1 : (1 : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 := one_le_pow₀ (one_le_pow₀ hp1)
  have hpQ : (p : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 :=
    le_trans (le_self_pow₀ hp1 hG) (le_self_pow₀ (one_le_pow₀ hp1) (by norm_num))
  have hc1 : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
  have hS : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ)) := by
    have : (0 : ℝ) ≤ (r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ) := by positivity
    linarith
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hC1 : (1 : ℝ) ≤ C := by linarith
  have hA3 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 3 := one_le_pow₀ hA1
  have hCT : C * (TT.card : ℝ) ≤ a := by
    have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * ((p : ℝ) ^ goodG' r de h x) ^ 5 *
        ((cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ))) * Y :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA3 hr1) hQ1) hS) hY1
    have h0 : (0 : ℝ) ≤ C * (TT.card : ℝ) := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 h0
    refine le_trans ?_ hlast
    calc C * (TT.card : ℝ) = C * (TT.card : ℝ) * 1 := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  have hQa : ((p : ℝ) ^ goodG' r de h x) ^ 5 ≤ a := by
    have h1 : (1 : ℝ) ≤ C * ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) *
        ((cStar : ℝ) + ((r : ℝ) * (TT.card : ℝ) * (c0 : ℝ) + 2 * (r : ℝ) * (n' : ℝ) * (cpp : ℝ))) * Y :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le hC1 hA3) hr1) hT1) hS) hY1
    have h0 : (0 : ℝ) ≤ ((p : ℝ) ^ goodG' r de h x) ^ 5 := by positivity
    have h2 := mul_le_mul_of_nonneg_left h1 h0
    refine le_trans ?_ hlast
    calc ((p : ℝ) ^ goodG' r de h x) ^ 5 = ((p : ℝ) ^ goodG' r de h x) ^ 5 * 1 := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  have hpa : (p : ℝ) ≤ a := le_trans hpQ hQa
  have h7 : (7 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 7 ≤ m + 1)
  have hlog : 1 ≤ Real.logb p a := by
    rw [← Real.logb_self_eq_one hpl]
    exact Real.logb_le_logb_of_le hpl (by linarith) hpa
  have hnb : NB p m r TT.card a := by
    refine ⟨by linarith, hpa, ?_, ?_, hlog, ?_⟩
    · have : 4 * (TT.card : ℝ) ≤ C * (TT.card : ℝ) := mul_le_mul_of_nonneg_right hC (by positivity)
      linarith
    · have : (r : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : r ≤ m + 1)
      linarith
    · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hT1 (one_le_pow₀ hA1)) hlog
  have hW' := hW
  unfold tableLineDegreeFive.WeightHyp at hW'
  obtain ⟨hBW, -, hab⟩ := hW'
  have hv : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp
  have hfd : ∀ s ∈ TT, a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a := by
    intro s hs
    obtain ⟨h0, -, hmid⟩ := (hBW s).1 hs
    have hl := hmid 1 (by omega) (by omega)
    have hl' : |((lam0 s 1 : ℤ) : ℝ)| ≤ (cpp : ℝ) := by exact_mod_cast hl
    obtain ⟨hl1, hl2⟩ := abs_le.mp hl'
    obtain ⟨haT1, haT2, -, -⟩ := hab s hs
    have hv0R : (0 : ℝ) ≤ ((aT s : ℤ) : ℝ) - ((lam0 s 1 : ℤ) : ℝ) := by linarith
    have hv0 : 0 ≤ aT s - lam0 s 1 := by exact_mod_cast hv0R
    have e : ((flatDeg lam0 s : ℕ) : ℝ) = ((aT s : ℤ) : ℝ) - ((lam0 s 1 : ℤ) : ℝ) := by
      unfold flatDeg
      rw [h0, ← Int.cast_natCast, Int.toNat_of_nonneg hv0, Int.cast_sub]
    rw [e]
    constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sizeAt_of (K := K) hk hF hr hnb hka hfd (fun j : ZMod F.J => (F.LLset (segZ j)).card) rfl (fun _ => rfl)
  · intro j u hu
    exact sl_lt_Bo hV hr p (by omega) (flatDeg lam0) a (by linarith)
      (fun s hs => (hfd s (by rw [hF1] at hs; exact hs)).1) Y (r + K) (by linarith) (by omega)
      (fun j : ZMod F.J => (F.LLset (segZ j)).card) (fun _ => rfl) j u hu
  · unfold cPrime
    omega
  · have hV' := hV
    unfold Frames.Valid at hV'
    exact hV'.1

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.VBBMonomialOne
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem vBB_monomial_one {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}
    (nu : σ →₀ ℕ) :
    vBB (O := O) p (monomial nu (1 : KK O)) = (((padicValNat p (expFact nu) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  unfold vBB
  rw [support_monomial, if_neg one_ne_zero, Finset.inf_singleton, coeff_monomial, if_pos rfl, valuation_one_eq_zero_alt, zero_add]

theorem monomial_mem_pol {Kf : Type} [Field Kf] {ι : Type} {n : ℕ} (d : ι → ℕ) (nu : ι × Fin n →₀ ℕ)
    (hnu : ∀ x, multideg nu x = d x) : (monomial nu (1 : Kf)) ∈ Pol Kf n d := by
  rw [Pol, mem_restrictSupport_iff]
  intro mo hmo
  have : mo = nu := by
    rw [Finset.mem_coe, mem_support_iff, coeff_monomial] at hmo
    by_contra h
    exact hmo (if_neg fun h' => h h'.symm)
  rw [this]
  exact hnu

theorem noAt (D : Formalism.BasicNotions.D7) (p : ℕ) [hpF : Fact p.Prime] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O))
    (hDA : DigAbs p O) (Fr : Frames n' r) {J : ℕ} [NeZero J] (cP : ℕ) (Dt : SignedChainData p O r J) :
    NoAt (K := K) p O Fr cP Dt := by
  intro dNo ka rho e nu hrho hJ hnu
  have hp := hpF.out
  have : CharZero (KK O) := dvr_fraction_field_char_zero hp S
  obtain ⟨_, _, hJ3, hJ4⟩ := hJ
  obtain ⟨W, hW⟩ : ∃ W, W = algebraMap O (KK O) w := ⟨_, rfl⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, n2 = padicValNat p (∏ x, (dNo x).factorial) := ⟨_, rfl⟩
  obtain ⟨vn, hvn⟩ : ∃ vn, vn = padicValNat p (expFact nu) := ⟨_, rfl⟩
  obtain ⟨Dno, hDno⟩ : ∃ Dno, Dno = DnoOf (K := K) p Dt.nL dNo := ⟨_, rfl⟩
  have hvW : ∀ n : ℕ, vK p (W ^ n) = (((n : ℚ) / 2 : ℚ) : WithTop ℚ) := fun n => by
    rw [hW]; exact vK_w_pow hp S w hw2 n
  have hWn0 : ∀ n : ℕ, W ^ n ≠ 0 := by
    intro n h
    have := hvW n
    rw [h, valuation_zero_alt] at this
    exact WithTop.top_ne_coe this
  have hpW : (p : KK O) = W ^ 2 := by rw [hW, ← map_pow, hw2, map_natCast]
  have hmon : (monomial nu (1 : KK O)) ∈ Pol (KK O) K dNo := monomial_mem_pol dNo nu hnu

  have hUpol : (W ^ vn)⁻¹ • (monomial nu (1 : KK O)) ∈ Pol (KK O) K dNo := Submodule.smul_mem _ _ hmon
  have hUBB : InBB (O := O) p ((W ^ vn)⁻¹ • (monomial nu (1 : KK O))) := by
    unfold InBB
    rw [vBB_smul _ (inv_ne_zero (hWn0 vn)), vK_inv _ _ (hvW vn), vBB_monomial_one, ← hvn, ← WithTop.coe_add]
    simp
  obtain ⟨hZ1, hZ2⟩ := hJ3 _ hUpol
  have hZBB := hZ2 hUBB
  rw [← hDno] at hZBB
  have hYint := coefGe_of_inBB S w hw2 dNo _ (Submodule.smul_mem _ ((p : KK O) ^ Dno) hZ1) hZBB
  rw [← hW, ← hn2] at hYint
  obtain ⟨cY, hcY⟩ : ∃ cY, cY = W ^ n2 * (p : KK O) ^ Dno * (W ^ vn)⁻¹ := ⟨_, rfl⟩
  have hY : cY • e (monomial nu 1) = W ^ n2 • (p : KK O) ^ Dno • e ((W ^ vn)⁻¹ • (monomial nu (1 : KK O))) := by
    rw [map_smul, smul_smul, smul_smul, hcY]
  rw [← hY] at hYint
  obtain ⟨Yy, hYy⟩ : ∃ Yy, Yy = cY • e (monomial nu 1) := ⟨_, rfl⟩
  rw [← hYy] at hYint
  have hYpol : Yy ∈ Pol (KK O) K dNo := by
    rw [hYy]
    exact Submodule.smul_mem _ _ (hJ3 _ hmon).1
  obtain ⟨lam, hlam1, hlam2⟩ := (hDA (TL J Dt.nL r × Fin K) (fun v => Fr.dist (segZ v.1.1) (posTL Fr v.1))
    (fun v => rho (v.1, Fin.natAdd r v.2)) (fun v => hrho _ _)).2 true cP
  have hlam3 : ∀ bn : TL J Dt.nL r × Fin K →₀ ℕ,
      geQ (vK p (binomCombF (K := KK O) lam bn - ((gamNo Fr p Dt.nL rho bn : ℚ) : KK O)⁻¹)) (cP : ℝ) := by
    intro bn
    have h := geQ_neg _ (hlam2 bn)
    rw [neg_sub, if_pos rfl] at h
    exact h
  refine ⟨diagK (fun bn => binomCombF (K := KK O) lam bn) Yy, cY, ⟨?_, diagK_mem_pol _ _ hYpol, ?_⟩, ?_, ?_⟩
  · intro bn
    rw [coeff_diagK]
    have := geQ_mul _ _ (geQ_binomCombF S lam bn) (hYint bn)
    rwa [add_zero] at this
  · intro j u hu
    rw [diagK_binomCombF]
    have h1 := (degree_truncation D (KK O) (TL J Dt.nL r) Dt.trueLet K (NSet Dt.nL j u) cP lam.support hlam1
      (fun m => algebraMap O (KK O) (lam m)) Yy).2
    have h2 : lam1S Dt.trueLet (NSet Dt.nL j u) Yy ≤ ((ka j u 0 : ℤ) : WithBot ℤ) := by
      rw [hYy]
      exact lowest_weight_le_of_isotypic D Dt.trueLet (NSet Dt.nL j u) (ka j u) _
        (Submodule.smul_mem _ _ (hJ4 (monomial nu 1) ⟨j, ⟨u, by omega⟩⟩))
    refine le_trans h1 (le_trans (add_le_add_left h2 _) ?_)
    rw [← WithBot.coe_add]
    push_cast
    exact le_rfl
  · refine ⟨(n2 : ℚ) / 2 + (Dno : ℚ) - (vn : ℚ) / 2, ?_, ?_⟩
    · rw [hcY, valuation_mul_alt, valuation_mul_alt, hvW, vK_inv _ _ (hvW vn), hpW, ← pow_mul, hvW, ← WithTop.coe_add,
        ← WithTop.coe_add]
      congr 1
      push_cast
      ring
    · rw [← hn2, ← hvn, ← hDno]
      push_cast
      exact le_rfl
  · rw [← hYy]
    intro bn
    rw [coeff_sub, coeff_diagK, coeff_diagK, ← sub_mul]
    have := geQ_mul _ _ (hlam3 bn) (hYint bn)
    rwa [add_zero] at this

end Formalism.MainNotions.Proposition5Numerics
end
end

