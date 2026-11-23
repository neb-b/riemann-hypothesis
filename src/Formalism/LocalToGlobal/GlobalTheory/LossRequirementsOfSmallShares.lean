module

public import Formalism.LocalToGlobal.GlobalTheory.Bundle0004
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.PowFourLtCeilThresholdPrime
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.DiscriminantSettingSatisfied

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Loss7

open Formalism.BasicNotions Formalism.MainNotions Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.PrimeWindowSizeBounds Formalism.LFunctionChainParameters.SmallOrderPrimeLosses Formalism.L2.GlobalTheoryTheory.Loss

section AtRecord

variable {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts)

theorem cands_eq : cands L K = sAt L K := rfl

theorem card_lifts (D : D7) : (SizeData₂.lifts D).card = D.R.m := by
  simp [SizeData₂.lifts]

theorem card_TTv (D : D7) : (TTv D).card = D.host.TT.card := by
  have h := pb_sum_TTv (D := D) (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ, Fintype.card_coe] at h
  exact_mod_cast h


open Classical in
theorem bad_card_at (p : ℕ) : ((TTv D).filter (fun n => badAt X p n)).card = (badTops X p).card := by
  have h := pb_sum_TTv (D := D) (fun n => if badAt X p n then (1 : ℝ) else 0)
  rw [Finset.sum_boole] at h
  have h2 : (∑ t : D.host.TT, if badAt X p (t : D.R.A).val then (1 : ℝ) else 0) = ((badTops X p).card : ℝ) := by
    rw [badTops, Finset.card_filter]
    push_cast
    rw [← Finset.sum_coe_sort D.host.TT]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [badAt, pb_cast]
  exact_mod_cast h.trans h2

end AtRecord

theorem loss_setting_family : LossSettingFamily := by
  classical
  intro D L X K Cr C bo P H hG tie hbo hLa hp0 hTT hB hW
  obtain ⟨-, -, -, -, -, -, -, ea, -, eθ⟩ := side_at X K Cr C bo H P tie hbo hLa hp0
  have hx0 : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hSig : ∀ p, 0 ≤ G.Sig X K (G.aL L) (G.bL L) p :=
    fun p => Lnk.Sig_nonneg X K H.Knn H.kapI _ _ p
  refine ⟨?_, ?_, fun p _ => hSig p, ?_, ?_, ?_, fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · unfold TTv; exact hTT.image _
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_PsAt hp
    exact ⟨h1, fun h => two_not_inert _ (h ▸ h2)⟩
  · unfold ChW_at at hW
    unfold lhsW
    rw [eθ, tie.x, ← cands_eq]
    have e9 : L.sc.x ^ (-9 : ℝ) = (L.sc.x ^ 9)⁻¹ := by
      rw [Real.rpow_neg hx0.le]
      congr 1
      exact_mod_cast Real.rpow_natCast L.sc.x 9
    rw [← e9]
    exact hW
  · unfold ChBadp_at at hB
    unfold badPrimeLogWeightedCount
    rw [card_TTv, tie.x, tie.ε]
    simp only [bad_card_at]
    exact hB
  · intro _ p _
    have h := Lnk.ioP_le X K p (hG.2.1 p) (hSig p)
    rw [card_lifts, card_TTv, ea]
    exact h
  · exact lossHyp_at X K Cr C bo H hG P tie hbo hLa hp0
  · exact firstHyp_at X K Cr C bo H (T_not_inert _) P tie
  · intro p _ h
    obtain ⟨h1, h2⟩ := second_spec X K p h
    rw [eθ]
    exact ⟨(mem_sAt K).mpr h1, h2⟩
  · intro p hp h n hn
    have hn' : n ∈ TTv D ∧ n ∉ (ldAt X K C bo).TTp p := by
      simpa only [Finset.mem_sdiff] using hn
    exact unserved_bad X K Cr C bo H (T_not_inert _) p hp h n (Finset.mem_sdiff.mpr hn')

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem losses_of_small_share_weight (hTT : ChosenTT Fm) (hBad : ChosenBadp Fm) (hG : LinkG Fm) : Lnk.LossesSmallShares Fm := by
  classical
  obtain ⟨Cord, hCord, hJ⟩ := joint_discriminant_eventually
  obtain ⟨xT, hTT⟩ := hTT
  obtain ⟨xB, hBad⟩ := hBad
  obtain ⟨C, xG, δ, hδ, hG⟩ := hG
  obtain ⟨xA, hAsk⟩ := Lnk.askIsF Fm
  obtain ⟨e, K, x0, hW⟩ := windows_ev Fm C 0 Cord hCord δ hδ
  have heps : 0 < eps := Lnk.fam_eps_pos Fm
  have heps4 : eps < 1 / 4 := by
    obtain ⟨i⟩ := Fm.Ix_zero
    have := (Fm.L 0 i).sc.eps_lt
    rw [Fm.L_eps 0 i] at this
    linarith
  obtain ⟨x1, hJ'⟩ := hJ eps e K heps heps4
  refine ⟨3 * |K| + 13, max (max x0 xT) (max xB (max xG (max xA x1))), by positivity, fun x hxx i hWi => ?_⟩
  have e0 : x ≥ x0 := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hxx
  have eT : x ≥ xT := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hxx
  have eB : x ≥ xB := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxx
  have eG : x ≥ xG := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hxx
  have eA : x ≥ xA := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)) hxx
  have e1 : x1 ≤ x := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
    (le_max_right _ _)) hxx
  obtain ⟨hx, h3, hW⟩ := hW x e0
  obtain ⟨hW, hp0⟩ := hW i
  set bo : ℝ := (Fm.L x i).sc.b ^ δ x with hbo
  have hbo0 : 0 ≤ bo := Real.rpow_nonneg (Real.exp_pos _).le _
  set P : Par := par Fm x i C bo 0 Cord with hP
  have tie : ParTie P (Fm.L x i) Fm.GK C bo Fm.Cr := parTie (i0 := i) hx i C bo 0 Cord
  have hH : PtH (Fm.Gx x i) Fm.GK Fm.Cr := ptH Fm hx h3 i
  have hLa : 0 ≤ (Fm.L x i).LaG := by
    have h1 := (Fm.sizes x hx i).2.2.2.2.2.2.2.2.1.1
    exact le_trans (Real.rpow_nonneg (lt_trans one_pos (Fm.L x i).sc.one_lt_alt).le _) h1
  have hne : (Fm.D x i).host.TT.Nonempty := by
    rw [← Finset.card_pos]
    have h1 := (hTT x eT i).1
    have hx0 : 0 < (Fm.L x i).sc.x := lt_trans one_pos (Fm.L x i).sc.one_lt_alt
    have h2 : 0 < (Fm.L x i).sc.delta1 * (Fm.D x i).R.n / 2 := by
      have : 0 < (Fm.L x i).sc.delta1 := Real.rpow_pos_of_pos hx0 _
      have h4 : (0 : ℝ) < (Fm.D x i).R.n := lt_of_lt_of_le one_pos (Lnk.one_le_n _)
      positivity
    exact_mod_cast lt_of_lt_of_le h2 h1
  have hS := loss_setting_family (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Fm.GK Fm.Cr C bo P hH (hG x eG i) tie hbo0 hLa hp0 hne
    (hBad x eB i) hWi
  have hPx : P.x = x := Fm.L_x x i hx
  have hPe : P.ε = eps := Fm.L_eps x i
  obtain ⟨hc1, hc2⟩ := hJ' P hPe rfl (by rw [hPx]; exact e1) (discriminant_windows_of P e K hW) ℕ ℕ ℕ Unit _ _ _ _ _ _ _ _ _ hS
  have hPC0 : 0 ≤ P.C := le_max_right _ _
  have hPCK : P.C ≤ K := hW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hU : unitU P (SizeData₂.lifts (Fm.D x i)).card (TTv (Fm.D x i)).card =
      ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b := by
    unfold unitU; rw [card_lifts, card_TTv, pd_b tie]
  have hU0 : 0 ≤ ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hone : (Fm.L x i).sc.x ^ ((0 : ℝ) * (Fm.L x i).sc.eps) = 1 := by rw [zero_mul, Real.rpow_zero]
  have hKabs : K ≤ |K| := le_abs_self K
  have hbig : (3 * P.C + 13) * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) ≤
      (3 * |K| + 13) * (Fm.D x i).host.TT.card * (Fm.D x i).R.m * (Fm.L x i).sc.b *
        (Fm.L x i).sc.x ^ ((0 : ℝ) * (Fm.L x i).sc.eps) := by
    rw [hone, mul_one]
    have := mul_le_mul_of_nonneg_right (show 3 * P.C + 13 ≤ 3 * |K| + 13 by linarith) hU0
    simpa [mul_assoc] using this
  have hsmall : ((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b ≤
      (3 * P.C + 13) * (((Fm.D x i).host.TT.card : ℝ) * (Fm.D x i).R.m * (Fm.L x i).sc.b) := by
    have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 * P.C + 13 by linarith) hU0
    linarith
  constructor
  · have h2 := hc2 ()
    rw [IO_at (Fm.Gx x i) Fm.GK Fm.Cr hH, hU] at h2
    linarith
  · intro e' m' AD N TT' a w hr hAD hcut
    rw [hAsk x eA i e' m' AD N TT' a w hr hAD hcut]
    have h1 := hc1 ()
    rw [Ga_at (Fm.Gx x i) Fm.GK Fm.Cr C bo hH, hU, tie.d, ASK_at (Fm.Gx x i) Fm.GK Fm.Cr C bo hH] at h1
    linarith

end Family

theorem stLoss7 : ThickDensitySizeWindowsForAllFamilies := fun _ Fm h1 h2 h3 => losses_of_small_share_weight Fm h1 h2 h3

section Size

variable {D : D7} {L : SizeData₂ D}

end Size

section Family

variable {eps : ℝ} (Fm : FamP eps)

theorem loss_requirements_of_small_shares (C0 CH : ℝ) (h : ChosenE Fm C0 CH) (hW : ChosenWall Fm) : WeightVectorSmallSharesSeven Fm C0 CH := by
  obtain ⟨C5, c6, Cb, h5, h6, hb, hT2, hTT, hBad, hQD, hThin, hPr, hCode⟩ := h
  exact ⟨C5, c6, h5, h6, Lnk.thick_density_of_construction Fm hT2, hTT, Lnk.chosenBadp_of_old Fm Cb hb.le hTT hBad,
    chosenWS_of_wall (Fm := Fm) hW, hQD, hThin, hPr, hCode⟩

end Family

end Formalism.L2.GlobalTheoryTheory.Loss7

end
