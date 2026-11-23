module

public import Development.AutomorphicArithmetic.DedekindLFunctions.SplitInertia

@[expose] public section

open Finset

noncomputable section

namespace Deduction

open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

lemma ch_top_main_eq {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type}
    [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (D : ArithData H) (N : ℕ)
    (ell : AddChar (E0 × H) ℂ → ℂ) (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H)) (hId : IdentU Dd tr D N ell TT a w eT eP) (u0 : U0) :
    Dd.Main u0 = ∑ t ∈ TT, ∑ j : Fin m, (MAIN ell (a t) (w (tr u0) j)).re := by
  obtain ⟨ha, hw, hg, hL, -⟩ := hId
  have hf : (f : ℝ) = (#(PhiSet (H := H)) : ℝ) := by
    have := Fintype.card_congr eP
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    exact_mod_cast this
  have hsum : ∀ g : E0 × H → ℝ, ∑ ρ : Fin f, g (eP ρ) = ∑ x ∈ PhiSet, g x := by
    intro g
    rw [← Finset.sum_coe_sort PhiSet]
    exact Equiv.sum_comp eP (fun x => g x)
  unfold Data.Main
  simp only [ha, hw, hg, hL, hsum, hf]
  rw [Finset.sum_comm]
  rw [← Finset.sum_coe_sort TT]
  rw [← Equiv.sum_comp eT]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => ?_
  simp [MAIN, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  left
  left
  exact hsum (fun x => Real.log (w (tr u0) j x))

theorem ch_top {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (tr : U0 → H) (C : Consts) (Xpp eK K : ℝ)
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (eT : Top ≃ TT) (eP : Fin f ≃ PhiSet (H := H))
    (h1 : IdentU Dd tr D N ell TT a w eT eP) (h2 : SizeData₂ Dd C Xpp) (h3 : ErrWindows Dd C Xpp eK K) (h4 : BNBoundsU Dd T2)
    (h5 : LargeX Dd.x Dd.ε K C.cHH eK) (u : U0) :
    gapA D N ell TT a w (tr u) ≤
      Dd.x ^ (CErr C * Dd.ε) * errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
  have hmain := ch_top_main_eq Dd tr D N ell TT a w eT eP h1 u
  have hask := h1.2.2.2.2 u
  have hgap : gapA D N ell TT a w (tr u) = Dd.ASK u - Dd.Main u := by
    rw [hask, hmain]
    unfold gapA
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_sub_distrib]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := h2
  have hle := each_unit_bound_statement Dd C Xpp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u
  have herr : ErrX5at Dd C Xpp u ≤ Dd.x ^ (CErr C * Dd.ε) * ErrText Dd := by
    obtain ⟨⟨hx, hε, hε1, hb, hxb, hnT, hm, hxm, heK, hk1, hkx, hka, hL0, hL, hLa0, hLa, hb', hkb', hX0,
      hXa, haT, hB0, hNc, hlW, hdel, -, -, hC⟩, het⟩ := h3
    obtain ⟨c1, c1', c2, c2', c3, c3', c4, c4', c5, c5', c6, c6', c7, c7', hD, hLs, hHH⟩ := hC
    obtain ⟨hlog, hbig⟩ := h5
    have hx0 : 0 < Dd.x := by linarith only [hx]
    have hy : 1 ≤ Dd.x ^ Dd.ε := Real.one_le_rpow hx hε.le
    have hyD : 1 ≤ Dd.x ^ (C.eDiv * Dd.ε) := Real.one_le_rpow hx (mul_nonneg hD hε.le)
    have hyL : 1 ≤ Dd.x ^ (C.eLoss * Dd.ε) := Real.one_le_rpow hx (mul_nonneg hLs hε.le)
    have hb0 : 0 ≤ Dd.b := by linarith only [hb]
    have hbxb : Dd.b ≤ Dd.x * Dd.b := le_mul_of_one_le_left hb0 hx
    have hba : Dd.b ≤ Dd.a := hbxb.trans hxb
    have ha1 : 1 ≤ Dd.a := hb.trans hba
    have hM : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hk : 0 < Dd.k := by linarith only [hk1]
    have hmx : (m : ℝ) ≤ Dd.x := by
      refine hm.trans ?_
      calc Dd.x ^ ((1 : ℝ) / 2 + Dd.ε / 2) ≤ Dd.x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hε1])
        _ = Dd.x := Real.rpow_one _
    have hMk : (m : ℝ) ≤ Dd.k := (le_mul_of_one_le_left hM hx).trans hxm
    have hMb : (m : ℝ) * Dd.b ≤ Dd.a := (mul_le_mul_of_nonneg_right hmx hb0).trans hxb
    have hsA0 : 0 ≤ Dd.sumA := Finset.sum_nonneg (fun t _ => (haT t).1)
    have hsA : Dd.sumA ≤ 2 * (Dd.nT * Dd.a) := by
      unfold Data.sumA Data.nT
      calc ∑ t, Dd.aT t ≤ ∑ _t : Top, 2 * Dd.a := Finset.sum_le_sum (fun t _ => (haT t).2)
        _ = 2 * ((Fintype.card Top : ℝ) * Dd.a) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    have hlWk : Real.log (Fintype.card (W u) : ℝ) ≤ Dd.a :=
      ((hlW u).trans (sub_three_mul_log_two_le hk.le)).trans hka
    have hlk0 : 0 ≤ Real.log Dd.k := Real.log_nonneg hk1
    have hlk : Real.log Dd.k ≤ (1 + eK) * Dd.x ^ Dd.ε := log_le_of_le_rpow hx heK hk hkx hlog hy
    have hxH : 1 ≤ Dd.x ^ C.cHH := Real.one_le_rpow hx hHH
    have hlH0 : 0 ≤ Real.log (1 + Dd.x ^ C.cHH) := Real.log_nonneg (by linarith only [hxH])
    have hlH : Real.log (1 + Dd.x ^ C.cHH) ≤ (1 + C.cHH) * Dd.x ^ Dd.ε :=
      log_one_add_rpow_le hx hHH hlog hy
    obtain ⟨hdI0, hdI⟩ := inv_one_sub_le_two hdel
    have hpow : Dd.x ^ (CErr C * Dd.ε)
        = Dd.x ^ (C.eDiv * Dd.ε) * Dd.x ^ (C.eLoss * Dd.ε) * Dd.x ^ Dd.ε * Dd.x ^ Dd.ε * Dd.x ^ Dd.ε := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
      congr 1
      unfold CErr
      ring
    rw [hpow]
    unfold KBig at hbig
    have := core_ineq (nT := Dd.nT) (a := Dd.a) (b := Dd.b) (b' := Dd.b') (k := Dd.k) (L := Dd.L) (La := Dd.La)
      (B0 := Dd.B0) (Nc := Dd.Nc) (M := (m : ℝ)) (sA := Dd.sumA)
      (lW := Real.log (Fintype.card (W u) : ℝ)) (lk := Real.log Dd.k)
      (lH := Real.log (1 + Dd.x ^ C.cHH)) (dI := (1 - Dd.delBar)⁻¹)
      (et := (Dd.etaBar + 4 * Real.sqrt Dd.eBar) * (Dd.x ^ C.cHH * Dd.b)) (Xpp := Xpp)
      (y := Dd.x ^ Dd.ε) (yD := Dd.x ^ (C.eDiv * Dd.ε)) (yL := Dd.x ^ (C.eLoss * Dd.ε)) (K := K)
      (h := 1 + C.cHH) (g := 1 + eK)
      hy hyD hyL hnT ha1 hb0 hba hM hk hMk hMb hL0 hL hLa0 hLa hb' hkb' hX0 hXa hsA0 hsA hB0 hNc hlWk
      hlk0 hlk hlH0 hlH hdI0 hdI het c1 c1' c2 c2' c3 c3' c4 c4' c5 c5' c6 c6' c7 c7'
      (by linarith only [hHH]) (by linarith only [heK]) hbig
    unfold ErrX5at UBar5 MLo5 Data.Vvar Data.LoP ErrText
    exact this
  have hnT : Dd.nT = (TT.card : ℝ) := by
    unfold Data.nT
    have := Fintype.card_congr eT
    rw [Fintype.card_coe] at this
    exact_mod_cast this
  have htext : ErrText Dd ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card H) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold ErrText errorBracketSizeWindows
    rw [hnT]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    gcongr
    · exact h4.1
    · exact h4.2
  have hpow : 0 ≤ Dd.x ^ (CErr C * Dd.ε) := Real.rpow_nonneg s1.1.le _
  rw [hgap]
  calc Dd.ASK u - Dd.Main u ≤ _ := by linarith
    _ ≤ _ := herr
    _ ≤ _ := mul_le_mul_of_nonneg_left htext hpow

end Deduction

end
