module

public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.OldestFar
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.FrRevInj

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.FortyEightBoundArith
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

namespace Ar

theorem arith1 (dw a Bo Yk Pg PL PD sl : ℝ) (hPg : 0 < Pg) (hPL : 0 < PL) (hYk : 0 < Yk) (hBo : 0 ≤ Bo)
    (ha : 0 ≤ a) (h1 : dw ≤ 3 * a / Pg) (h2 : a ≤ Bo * PD) (h3 : PD * PL ≤ Pg) (h4 : 48 * Yk ≤ PL)
    (h5 : Bo / Yk ≤ 2 * sl) : dw ≤ 1 / 8 * sl := by
  have e1 : a / Pg ≤ Bo / PL := by
    rw [div_le_div_iff₀ hPg hPL]
    nlinarith [mul_le_mul_of_nonneg_left h3 hBo, mul_le_mul_of_nonneg_right h2 hPL.le]
  have e2 : Bo / PL ≤ Bo / (48 * Yk) := div_le_div_of_nonneg_left hBo (by positivity) h4
  have e3 : Bo / (48 * Yk) = (Bo / Yk) / 48 := by
    field_simp
  have e4 : 3 * a / Pg = 3 * (a / Pg) := by ring
  linarith

theorem size_le_monomial_product (C k r N Q cS e Y : ℝ) (hC : 1 ≤ C) (hk : 1 ≤ k) (hr : 1 ≤ r) (hN : 1 ≤ N) (hQ : 1 ≤ Q)
    (hcS : 1 ≤ cS) (he : 0 ≤ e) (hY : 0 ≤ Y) : Y * k ^ 2 * Q ≤ C * k ^ 3 * r ^ 2 * N * Q ^ 5 * (cS + e) * Y := by
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have hQ4 : 1 ≤ Q ^ 4 := one_le_pow₀ hQ
  have hce : 1 ≤ cS + e := by linarith
  have hf : 1 ≤ C * k * r ^ 2 * N * Q ^ 4 * (cS + e) := by
    calc (1 : ℝ) = 1 * 1 * 1 * 1 * 1 * 1 := by norm_num
      _ ≤ C * k * r ^ 2 * N * Q ^ 4 * (cS + e) := by gcongr
  have h0 : 0 ≤ Y * k ^ 2 * Q := by positivity
  calc Y * k ^ 2 * Q = Y * k ^ 2 * Q * 1 := by ring
    _ ≤ Y * k ^ 2 * Q * (C * k * r ^ 2 * N * Q ^ 4 * (cS + e)) := mul_le_mul_of_nonneg_left hf h0
    _ = _ := by ring

theorem forty_eight_bound_arith (Y k N P : ℝ) (hY : 2 ≤ Y) (hk : 1 ≤ k) (hN : 1 ≤ N) (h : 256 * k ^ 2 * N * Y ^ 2 ≤ P) :
    48 * (Y * k ^ 2) ≤ P := by
  have h1 : 256 * k ^ 2 * Y ^ 2 ≤ 256 * k ^ 2 * N * Y ^ 2 := by
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 256 * k ^ 2 * Y ^ 2) (by linarith : (0:ℝ) ≤ N - 1)]
  have h2 : 48 * (Y * k ^ 2) ≤ 256 * k ^ 2 * Y ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg k) (by linarith : (0:ℝ) ≤ Y)) (by linarith : (0:ℝ) ≤ 256 * Y - 48)]
  linarith

end Ar


set_option maxHeartbeats 1000000 in
theorem arithCondition_of_one_le (C CLa : ℝ) (hC : 1 ≤ C) : RestArithStep C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk
    F nb B hD
  obtain ⟨_, H, hF, _⟩ := hD
  have hB := hyps_basic hC H
  obtain ⟨h1, h2, h3, h4, h5, h6, _, _, h9, _, h11, h12⟩ := H
  obtain ⟨hTT, hV, hG, _⟩ := hF
  have hr1 : 1 ≤ r := by omega
  have ha0 : (0 : ℝ) ≤ a := by linarith [hB.two_le_a]
  refine ⟨?_, ?_⟩
  · by_contra hc
    have hJ1 : F.J = 1 := by have := hV.1; omega
    have e := hV.2.1 0 (r - 1)
    rw [hJ1] at e
    simp only [Nat.cast_one, zero_add] at e
    have g := hG 1
    simp only [sub_self] at g
    have m0 := frame_row_monotone F L₁ _ hV 0 (r - 1) (by omega)
    have h3G := h3.2.2.2
    omega
  intro E' l hl ga hga J _ Dt hS dPl dNo rho hb hlow jj mm hmm
  obtain ⟨t1, t2, _, t5, _, _⟩ := hS
  obtain ⟨s, hs⟩ := seg_shift hV t1 (jj - 1)
  rw [sub_add_cancel jj 1] at hs
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 3 ≤ p)
  set q : ℝ := (p : ℝ)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq13 : q ≤ 1 / 3 := by
    rw [hq, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp3
  have hq1 : q < 1 := by linarith
  set g : ℕ := (F.fr (segZ jj) (r - 1) - F.fr (segZ jj - 1) (r - 1)).toNat with hg
  let t : Fin r → ℕ := fun m' => (F.fr (segZ jj - 1) (r - 1) - F.fr (segZ jj - 1) (r - 1 - m'.val)).toNat
  have ht : Function.Injective t := by
    intro u v huv
    have huv' : (F.fr (segZ jj - 1) (r - 1) - F.fr (segZ jj - 1) (r - 1 - u.val)).toNat =
        (F.fr (segZ jj - 1) (r - 1) - F.fr (segZ jj - 1) (r - 1 - v.val)).toNat := huv
    have l1 := frame_entry_le_last F L₁ _ hV (segZ jj - 1) (r - 1 - u.val) (by omega)
    have l2 := frame_entry_le_last F L₁ _ hV (segZ jj - 1) (r - 1 - v.val) (by omega)
    have hu := u.isLt
    have hv := v.isLt
    apply Fin.ext
    rcases lt_trichotomy u.val v.val with c | c | c
    · have := frame_entries_strictMono F L₁ _ hV (segZ jj - 1) (r - 1 - v.val) (r - 1 - u.val) (by omega) (by omega)
      omega
    · exact c
    · have := frame_entries_strictMono F L₁ _ hV (segZ jj - 1) (r - 1 - u.val) (r - 1 - v.val) (by omega) (by omega)
      omega

  have hterm : ∀ m' : Fin r, ((dPl ⟨jj - 1, Sum.inr m'⟩ -
      multideg (plMon F p hk Dt.nL (l.mapDomain (castV hk) + ga)) ⟨jj - 1, Sum.inr m'⟩ : ℕ) : ℝ) /
        (Dt.P (jj - 1) m' : ℝ) ≤ 2 * a * q ^ g * q ^ t m' := by
    intro m'
    have hd := Ar.deg_le F p hk Dt.nL hV hr1 t2 (G2d F (flatDeg lam0) E') l hl ga hga dPl dNo rho hb hlow
      ⟨jj - 1, Sum.inr m'⟩
    have htop := (posTL_seg F hV hr1 t2 (⟨jj - 1, Sum.inr m'⟩ : TL J Dt.nL r)).2.2
    have hG2 : G2d F (flatDeg lam0) E' (posOf n' (posTL F (⟨jj - 1, Sum.inr m'⟩ : TL J Dt.nL r))) ≤
        flatDeg lam0 (posOf n' (posTL F (⟨jj - 1, Sum.inr m'⟩ : TL J Dt.nL r))) := by
      unfold G2d
      rw [if_pos htop]
      exact Nat.sub_le _ _
    have hfd := (flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 _ (hTT ▸ htop)).2
    have s1 := hs (r - 1)
    have s2 := hs (r - 1 - m'.val)
    have hlowP : lowP F p (⟨jj - 1, Sum.inr m'⟩ : TL J Dt.nL r) = p ^ t m' := by
      show p ^ (F.fr (segZ (jj - 1)) (r - 1) - F.fr (segZ (jj - 1)) (r - 1 - m'.val)).toNat =
        p ^ (F.fr (segZ jj - 1) (r - 1) - F.fr (segZ jj - 1) (r - 1 - m'.val)).toNat
      congr 1
      omega
    have hP : Dt.P (jj - 1) m' = p ^ g := by
      unfold SignedChainData.P
      rw [t5, hg]
      congr 1
      omega
    rw [hlowP] at hd
    set nn : ℕ := dPl ⟨jj - 1, Sum.inr m'⟩ -
      multideg (plMon F p hk Dt.nL (l.mapDomain (castV hk) + ga)) ⟨jj - 1, Sum.inr m'⟩ with hnn
    have h3' : ((p ^ t m' * nn : ℕ) : ℝ) ≤ 2 * a := le_trans (by exact_mod_cast le_trans hd hG2) hfd
    push_cast at h3'
    have hpt : (0 : ℝ) < (p : ℝ) ^ t m' := by positivity
    have hn : (nn : ℝ) ≤ 2 * a * q ^ t m' := by
      rw [hq, inv_pow, ← div_eq_mul_inv, le_div_iff₀ hpt]
      linarith
    rw [hP]
    push_cast
    calc (nn : ℝ) / (p : ℝ) ^ g = nn * q ^ g := by rw [hq, inv_pow, div_eq_mul_inv]
      _ ≤ 2 * a * q ^ t m' * q ^ g := mul_le_mul_of_nonneg_right hn (by positivity)
      _ = 2 * a * q ^ g * q ^ t m' := by ring
  have hinv : (1 - q)⁻¹ ≤ 3 / 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hA : 0 ≤ 2 * a * q ^ g := by positivity
  have hsum : dwB F hk Dt dPl (l.mapDomain (castV hk) + ga) jj ≤ 3 * a / (p : ℝ) ^ g := by
    unfold dwB
    calc _ ≤ ∑ m' : Fin r, 2 * a * q ^ g * q ^ t m' := Finset.sum_le_sum fun m' _ => hterm m'
      _ = 2 * a * q ^ g * ∑ m' : Fin r, q ^ t m' := by rw [Finset.mul_sum]
      _ ≤ 2 * a * q ^ g * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left (geom_inj_le t ht q hq0 hq1) hA
      _ ≤ 2 * a * q ^ g * (3 / 2) := mul_le_mul_of_nonneg_left hinv hA
      _ = 3 * a / (p : ℝ) ^ g := by rw [hq, inv_pow, div_eq_mul_inv]; ring

  have hi0 : r - 1 - mm.val < r := by omega
  have ex0 : posU F (Dt.nL jj) (segZ jj) (Dt.nL jj + (r - 1 - mm.val)) = F.fr (segZ jj) (r - 1 - mm.val) :=
    posU_fr' (Fr := F) _ _ _
  unfold slU
  rw [ex0]
  have hx := posU_mem' hV hr1 (segZ jj) ((F.LLset (segZ jj)).card + (r - 1 - mm.val)) (by omega)
  rw [posU_fr] at hx
  have hfar := Ar.oldest_far hV hr1 (segZ jj) (r - 1 - mm.val) hi0
  have hy := oldest_mem_segment_letters F L₁ _ hV hr1 (segZ jj) _ hx.1 hx.2
  unfold Frames.letters at hy
  simp only [Finset.mem_filter, Finset.mem_Icc] at hy
  set y : ℤ := F.oldest (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) with hydef
  set Dd : ℕ := F.dist (segZ jj) y with hDd
  have hDd' : Dd = (F.fr (segZ jj) (r - 1) - y).toNat := rfl
  have hdeg := (flatDeg_bounds (by have := hB.m_ge; omega) ha0 h5 _ (hTT ▸ hy.2)).1
  have hPD : (0 : ℝ) < (p : ℝ) ^ Dd := by positivity
  have hBoe : Bo p F (flatDeg lam0) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) =
      (flatDeg lam0 (posOf n' y) : ℝ) / (p : ℝ) ^ Dd := rfl
  set Bv : ℝ := Bo p F (flatDeg lam0) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) with hBv
  have hBo0 : 0 ≤ Bv := by rw [hBoe]; positivity
  have hBoa : a ≤ Bv * (p : ℝ) ^ Dd := by rw [hBoe, div_mul_cancel₀ _ hPD.ne']; exact hdeg
  have hpow : (p : ℝ) ^ Dd * (p : ℝ) ^ (L₁ + 1) ≤ (p : ℝ) ^ g := by
    rw [← pow_add]
    apply pow_le_pow_right₀ hp1
    omega
  have hkk : ((r + K : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := by rw [hk]
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hNN : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hY2 := hB.two_le_Y
  have hY0 : (0 : ℝ) < Y := by linarith
  have hden : 0 < Y * ((r + K : ℕ) : ℝ) ^ 2 := by rw [hkk]; positivity
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1
  have hQ0 : (0 : ℝ) < (p : ℝ) ^ goodG' r de h x := by linarith
  have hcS : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
  have hsz := le_trans (Ar.size_le_monomial_product C ((m + 1 : ℕ) : ℝ) r TT.card ((p : ℝ) ^ goodG' r de h x) cStar
    ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) Y hC hk1 hrr hNN hQ1 hcS (by positivity) hY0.le) h12
  have hDG : Dd ≤ goodG' r de h x := by
    have g1 := hG (segZ jj)
    have g2 := frame_row_monotone F L₁ _ hV (segZ jj - 1) (r - 1) (by omega)
    omega
  have hX1 : (1 : ℝ) ≤ Bv / (Y * ((r + K : ℕ) : ℝ) ^ 2) := by
    rw [le_div_iff₀ hden, one_mul, hkk]
    have c1 : (p : ℝ) ^ Dd ≤ (p : ℝ) ^ goodG' r de h x := pow_le_pow_right₀ hp1 hDG
    have c2 : Bv * (p : ℝ) ^ Dd ≤ Bv * (p : ℝ) ^ goodG' r de h x := mul_le_mul_of_nonneg_left c1 hBo0
    exact le_of_mul_le_mul_right (by linarith) hQ0
  have f1 : (1 : ℤ) ≤ sl p F (flatDeg lam0) Y (r + K) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) := by
    unfold sl
    exact Int.le_floor.2 (by rw [Int.cast_one]; exact hX1)
  have f2 : Bv / (Y * ((r + K : ℕ) : ℝ) ^ 2) <
      (sl p F (flatDeg lam0) Y (r + K) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have f1' : (1 : ℝ) ≤ (sl p F (flatDeg lam0) Y (r + K) (segZ jj) (F.fr (segZ jj) (r - 1 - mm.val)) : ℝ) := by
    exact_mod_cast f1
  have h48 : 48 * (Y * ((r + K : ℕ) : ℝ) ^ 2) ≤ (p : ℝ) ^ (L₁ + 1) := by
    rw [hkk]
    have z1 : (p : ℝ) ^ ((L₁ : ℤ) - 1) ≤ (p : ℝ) ^ ((L₁ + 1 : ℕ) : ℤ) :=
      zpow_le_zpow_right₀ hp1 (by push_cast; omega)
    rw [zpow_natCast] at z1
    exact Ar.forty_eight_bound_arith Y _ _ _ hY2 hk1 hNN (le_trans h9 z1)
  exact Ar.arith1 _ a Bv _ ((p : ℝ) ^ g) ((p : ℝ) ^ (L₁ + 1)) ((p : ℝ) ^ Dd) _ (by positivity) (by positivity) hden hBo0
    ha0 hsum hBoa hpow h48 (by linarith)

end Formalism.MainNotions.PairMembershipBlocks
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.MultidegSingle
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.TraceSpectra
open Formalism.MainNotions.G.WittFrameLocaliserOrders

namespace LkD

section MD

variable {ι : Type*} {n : ℕ}

theorem multideg_add (a b : ι × Fin n →₀ ℕ) (x : ι) : multideg (a + b) x = multideg a x + multideg b x := by
  simp [multideg, Finset.sum_add_distrib]

theorem multideg_zero (x : ι) : multideg (0 : ι × Fin n →₀ ℕ) x = 0 := by
  simp [multideg]

theorem multideg_smul (k : ℕ) (a : ι × Fin n →₀ ℕ) (x : ι) : multideg (k • a) x = k * multideg a x := by
  simp [multideg, Finset.mul_sum]

theorem multideg_single (v : ι × Fin n) (k : ℕ) (x : ι) :
    multideg (Finsupp.single v k) x = if v.1 = x then k else 0 := by
  unfold multideg
  by_cases h : v.1 = x
  · rw [if_pos h, Finset.sum_eq_single v.2]
    · have hv : v = (x, v.2) := by
        obtain ⟨v1, v2⟩ := v
        simp only at h
        rw [h]
      rw [Finsupp.single_apply, if_pos hv]
    · intro c _ hc
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hc (congrArg Prod.snd e).symm
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro c _
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (congrArg Prod.fst e)

end MD

theorem ne_pred {J : ℕ} (hJ : 2 ≤ J) (j : ZMod J) : j ≠ j - 1 := by
  intro h
  haveI : Fact (1 < J) := ⟨by omega⟩
  have h1 : (1 : ZMod J) = 0 := by linear_combination h
  exact one_ne_zero h1

section Phi

variable {p : ℕ} {n' r : ℕ} [NeZero n'] [NeZero r] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J)

theorem ph_ll (j : ZMod J) (l : Fin (Dt.nL j)) (a : Fin r) :
    Dt.ph (X (ML.ll j l, a)) = monomial (Finsupp.single ((⟨j, Sum.inl l⟩ : TL J Dt.nL r), a) 1) 1 := by
  rw [SignedChainData.ph, aeval_X]
  rfl

theorem ph_lab (j : ZMod J) (m : Fin r) (a : Fin r) :
    Dt.ph (X (ML.lab j m, a)) = monomial (Finsupp.single ((⟨j, Sum.inr m⟩ : TL J Dt.nL r), a) 1) 1 := by
  rw [SignedChainData.ph, aeval_X]
  rfl

theorem ph_wc (j : ZMod J) (m : Fin r) (a : Fin r) :
    Dt.ph (X (ML.wc j m, a)) = monomial (Finsupp.single ((⟨j, Sum.inr m⟩ : TL J Dt.nL r), a) (Dt.P j m)) 1 := by
  rw [SignedChainData.ph, aeval_X]
  exact X_pow_eq_monomial

theorem PhiJ_X (j : ZMod J) (v : ℤ × Fin r) (hv : v.1 ∈ Fr.letters (segZ j)) :
    PhiJ Fr Dt j (X v) = Dt.ph (X (mlOf Fr Dt.nL j v.1, v.2)) := by
  rw [PhiJ, AlgHom.comp_apply, chi, aeval_X, if_pos hv]

theorem PhiJ_X_mon (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (hJ : 2 ≤ J) (j : ZMod J)
    (v : ℤ × Fin r) (hv : v.1 ∈ Fr.letters (segZ j)) :
    ∃ e : TL J Dt.nL r × Fin r →₀ ℕ, PhiJ Fr Dt j (X v) = monomial e 1 ∧
      ∀ m' : Fin r, multideg e ⟨j - 1, Sum.inr m'⟩ =
        Dt.P (j - 1) m' * (if v.1 = Fr.fr (segZ j - 1) (r - 1 - m'.val) then 1 else 0) := by
  have hne := ne_pred hJ j
  have hr : 1 ≤ r := NeZero.one_le
  rw [PhiJ_X Dt j v hv]
  have hord := hV.2.2.2.1 (segZ j - 1)
  rw [sub_add_cancel] at hord
  rcases Formalism.MainNotions.NormalSetCounting.restSpec n' r Fr L₁ N₁ hV J Dt.nL hnL j v.1 hv with ⟨l, hy, hml⟩ | ⟨m, hy, hml⟩ | ⟨m, hy, hml⟩
  · rw [hml]
    refine ⟨_, ph_ll Dt j l v.2, fun m' => ?_⟩
    rw [multideg_single, if_neg (fun h => hne (congrArg Sigma.fst h)), if_neg, mul_zero]
    intro h
    have h1 := (Formalism.MainNotions.NormalSetCounting.ll_between hnL j l).1
    have h2 := frame_entry_le_last Fr L₁ N₁ hV (segZ j - 1) (r - 1 - m'.val) (by omega)
    omega
  · rw [hml]
    refine ⟨_, ph_lab Dt j m v.2, fun m' => ?_⟩
    rw [multideg_single, if_neg (fun h => hne (congrArg Sigma.fst h)), if_neg, mul_zero]
    intro h
    have h1 := frame_row_monotone Fr L₁ N₁ hV (segZ j) (r - 1 - m.val) (by omega)
    have h2 := frame_entry_le_last Fr L₁ N₁ hV (segZ j - 1) (r - 1 - m'.val) (by omega)
    omega
  · rw [hml]
    refine ⟨_, ph_wc Dt (j - 1) m v.2, fun m' => ?_⟩
    rw [multideg_single]
    by_cases hmm : m = m'
    · subst hmm
      rw [if_pos rfl, if_pos hy, mul_one]
    · rw [if_neg, if_neg, mul_zero]
      · intro h
        rw [hy] at h
        exact hmm (Formalism.MainNotions.NormalSetCounting.fr_rev_inj hV _ h)
      · intro h
        have h3 := eq_of_heq (Sigma.mk.inj_iff.1 h).2
        exact hmm (Sum.inr.inj h3)

theorem PhiJ_monomial (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (hJ : 2 ≤ J) (j : ZMod J)
    (μ : ℤ × Fin r →₀ ℕ) : (∀ v ∈ μ.support, v.1 ∈ Fr.letters (segZ j)) →
    ∃ ν : TL J Dt.nL r × Fin r →₀ ℕ, (∀ c : KK O, PhiJ Fr Dt j (monomial μ c) = monomial ν c) ∧
      ∀ m' : Fin r, multideg ν ⟨j - 1, Sum.inr m'⟩ =
        Dt.P (j - 1) m' * multideg μ (Fr.fr (segZ j - 1) (r - 1 - m'.val)) := by
  induction μ using Finsupp.induction_linear with
  | zero =>
    intro _
    refine ⟨0, fun c => ?_, fun m' => by rw [multideg_zero, multideg_zero, mul_zero]⟩
    exact MvPolynomial.algHom_C _ c
  | add f g hf hg =>
    intro h
    obtain ⟨ν1, a1, b1⟩ := hf (fun v hv => h v (by
      rw [Finsupp.mem_support_iff] at hv ⊢
      rw [Finsupp.add_apply]
      omega))
    obtain ⟨ν2, a2, b2⟩ := hg (fun v hv => h v (by
      rw [Finsupp.mem_support_iff] at hv ⊢
      rw [Finsupp.add_apply]
      omega))
    refine ⟨ν1 + ν2, fun c => ?_, fun m' => ?_⟩
    · have e : (monomial (f + g) c : MvPolynomial (ℤ × Fin r) (KK O)) = monomial f c * monomial g 1 := by
        rw [monomial_mul, mul_one]
      rw [e, map_mul, a1, a2, monomial_mul, mul_one]
    · rw [multideg_add, multideg_add, b1, b2, mul_add]
  | single v k =>
    intro h
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨0, fun c => ?_, fun m' => by rw [Finsupp.single_zero, multideg_zero, multideg_zero, mul_zero]⟩
      rw [Finsupp.single_zero]
      exact MvPolynomial.algHom_C _ c
    · have hv : v.1 ∈ Fr.letters (segZ j) := h v (by rw [Finsupp.mem_support_iff, Finsupp.single_eq_same]; exact hk0)
      obtain ⟨e, he, hm⟩ := PhiJ_X_mon Dt hV hnL hJ j v hv
      refine ⟨k • e, fun c => ?_, fun m' => ?_⟩
      · have e1 : (monomial (Finsupp.single v k) c : MvPolynomial (ℤ × Fin r) (KK O)) = C c * X v ^ k := by
          rw [X_pow_eq_monomial, C_mul_monomial, mul_one]
        rw [e1, map_mul, map_pow, he, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, monomial_pow, one_pow,
          C_mul_monomial, mul_one]
      · rw [multideg_smul, hm, multideg_single]
        split_ifs <;> ring

end Phi

end LkD

theorem lkDeg : LkDeg := by
  intro p _ n' r _ _ O _ _ _ Fr L₁ N₁ hV J _ Dt hS hJ j F hF δ hδ ν hν m'
  have hFs := congrArg (PhiJ Fr Dt j) F.as_sum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hFs
  rw [hFs] at hν
  obtain ⟨μ, hμ, hν'⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hν)
  obtain ⟨ν0, a0, b0⟩ := LkD.PhiJ_monomial Dt hV hS.2.1 hJ j μ (fun v hv =>
    (mem_supported.1 hF) (Finset.mem_coe.2 ((mem_vars_iff_mem_support v).2 ⟨μ, hμ, hv⟩)))
  rw [a0] at hν'
  have := support_monomial_subset hν'
  rw [Finset.mem_singleton] at this
  rw [this, b0, hδ μ hμ]

theorem lkVars : LkVars := by
  intro p n' r _ _ O _ _ _ Fr J _ Dt j
  let s : Set (TL J Dt.nL r × Fin r) :=
    {v | (∃ l, v.1 = ⟨j, Sum.inl l⟩) ∨ ∃ (j' : ZMod J) (m' : Fin r), v.1 = ⟨j', Sum.inr m'⟩}
  have hmon : ∀ (x : TL J Dt.nL r × Fin r) (k : ℕ), x ∈ s →
      (monomial (Finsupp.single x k) (1 : KK O)) ∈ supported (KK O) s := by
    intro x k hx
    rw [← X_pow_eq_monomial]
    refine Subalgebra.pow_mem _ ?_ _
    rw [supported_eq_adjoin_X]
    exact Algebra.subset_adjoin (Set.mem_image_of_mem _ hx)
  have hX : ∀ u : ℤ × Fin r, PhiJ Fr Dt j (X u) ∈ supported (KK O) s := by
    intro u
    unfold PhiJ chi
    rw [AlgHom.comp_apply, aeval_X]
    split_ifs with hu
    · unfold mlOf
      split_ifs with h1 h2 h3
      · rw [LkD.ph_ll]; exact hmon _ _ (Or.inl ⟨_, rfl⟩)
      · rw [LkD.ph_lab]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
      · rw [LkD.ph_wc]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
      · rw [LkD.ph_lab]; exact hmon _ _ (Or.inr ⟨_, _, rfl⟩)
    · rw [map_zero]; exact Subalgebra.zero_mem _
  have hall : ∀ F : MvPolynomial (ℤ × Fin r) (KK O), PhiJ Fr Dt j F ∈ supported (KK O) s := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.algHom_C]; exact Subalgebra.algebraMap_mem _ a
    | add f g hf hg => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hf hg
    | mul_X f u hf => rw [map_mul]; exact Subalgebra.mul_mem _ hf (hX u)
  intro F v hv
  exact (mem_supported.1 (hall F)) (Finset.mem_coe.2 hv)

end Formalism.MainNotions.PairMembershipBlocks
end
end

