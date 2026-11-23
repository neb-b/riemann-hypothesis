module

public import Mathlib
public import Development.AutomorphicArithmetic.CharacterBoxes.Supply
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.DesignS
section
noncomputable section

namespace UpperTheory.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.DC GlobalTheory.Fc NumberField

theorem designS : ∀ (Q : Par → PtProp) (cT : ℝ → ℝ → ℝ) (la : ℝ) (G : FReq), 1 < la → DC.MinkDiv →
    KitCPW la (fun κ => ((withDuty (DC.withObj (Q κ))).and DC.WallPt).and G.pt) →
    DC.DesignChoices (DC.WithTw fun Fm => (∃ κ : Par, Link κ Fm ∧ DC.cls (Q κ) Fm) ∧ G.cls la Fm) 3 cT := by
  rintro Q cT la G hla hM ⟨ε0, hε0, hK⟩
  refine ⟨min ε0 (1 / 53), lt_min hε0 (by norm_num), fun eps he hle K => ?_⟩
  have he52 : eps < 1 / 52 := lt_of_le_of_lt (hle.trans (min_le_right _ _)) (by norm_num)
  obtain ⟨CT2, C8, C5, c6, Cb, K0, hC8, hC5, hc6, hCb, hK⟩ := hK eps he (hle.trans (min_le_left _ _)) he52
  obtain ⟨C, hStd, hCT2, hCp, hLK, hLK0, hGK⟩ := exists_std_large (thrTu K (cT eps 9)) K0 CT2 C8 hC8
  obtain ⟨c1, hK⟩ := hK C hStd hCT2 hCp hLK0
  obtain ⟨c1', hN⟩ := szRow_numAt eps he he52 C hStd
  obtain ⟨c2, hK⟩ := hK (max c1 c1') (le_max_left _ _)
  obtain ⟨c2', hN⟩ := hN (max c1 c1') (le_max_right _ _)
  obtain ⟨x0, S, hK⟩ := hK (max c2 c2') (le_max_left _ _)
  obtain ⟨x0', hN⟩ := hN (max c2 c2') (le_max_right _ _)
  have hx1 : (1 : ℝ) < max 2 (max x0 x0') := lt_of_lt_of_le one_lt_two (le_max_left _ _)
  have hK' : ∀ s : Scale, s.eps = eps → max 2 (max x0 x0') ≤ s.x → S.Mem s →
      ∃ k : Kit C (max c1 c1') (max c2 c2') s, ∀ i, (k.pt i).Has (((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt).and G.pt) ∧
        ThickSetLowerBound (k.pt i).L ∧ ChBad_at (k.pt i).ta.Gx Cb ∧ ChQD_at (k.pt i).D (k.pt i).L.sc.x (k.pt i).L.sc.eps C5 :=
    fun s hs hx hm => hK s hs (((le_max_left _ _).trans (le_max_right _ _)).trans hx) hm
  choose k hk using hK'
  have hnum : ∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L) ∧ ChTT_at ((k s h h' h'').pt i).L ∧
      ChCode_at ((k s h h' h'').pt i).L 3 C.P.CF := by
    intro s h h' h'' i
    refine hN _ _ ?_ ?_ ((k s h h' h'').val i) ((k s h h' h'').arith i)
    · rw [(k s h h' h'').sc_eq i]; exact h
    · rw [(k s h h' h'').sc_eq i]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans h'
  obtain ⟨Fm, hFx, hPre, hOut, hMid, hLast, hTu, hQ, hR, -, hWn, -⟩ :=
    exists_famP_of_kits eps C _ _ _ la S he he52 hx1 hla.le hStd hGK k (fun s h h' h'' i => (hnum s h h' h'' i).1)
  replace hOut : Fm.cOut = C.cOut := hOut
  have hall := hR (fun D L Gx => (ThickSetLowerBound L ∧ ChBad_at Gx Cb ∧ ChQD_at D L.sc.x L.sc.eps C5) ∧
      (Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) ∧
      Fintype.card D.what₂.Word = ⌈3 * GamL L ^ 2 * L.sc.x ^ C.P.CF⌉₊)
    (fun s h h' h'' i => ⟨(hk s h h' h'' i).2, hnum s h h' h'' i, ((k s h h' h'').val i).words⟩)
  have hCF : (1 : ℝ) ≤ C.P.CF := hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  have hc := hQ ((withDuty (DC.withObj (Q ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩))).and DC.WallPt) (fun s h h' h'' i => (hk s h h' h'' i).1.1)
  have hGc : G.cls la Fm := ⟨fun y => by
      obtain ⟨Y, a, b⟩ := S.windows y
      exact ⟨Y, a, fun x c d => hWn ▸ b x c d⟩,
    hQ G.pt (fun s h h' h'' i => (hk s h h' h'' i).1.2)⟩
  obtain ⟨hFix, hWin⟩ := fix_and_win_of_numAt eps C Fm hStd hOut (fun x i => (hall x i).2.1.1)
  have hCYL : Fm.CYL = 9 := hFix.2.2.2.2.2.2.2.1
  have hlt : ∀ x, x ≥ Fm.x1 + 1 → Fm.x1 < x := fun x hx => by linarith
  have hLarge : Fm.Large (thrTu K (cT eps 9)) C.P.CF := by
    unfold FamP.Large
    rw [hPre, hOut, hMid, hLast]
    exact hLK
  have hTw : TwGood Fm := classOf_twPt Fm fun x hx i => (hc x hx i).1.1.2.2.2
  have hQD : ChosenQD Fm C5 := by
    refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have := (hall x i).1.2.2
    rwa [Fm.L_x x i (hlt x hx), Fm.L_eps x i] at this
  have hreq := classOf_reqPt Fm fun x hx i => ⟨(hc x hx i).2, (hc x hx i).1.2.2.1, (hc x hx i).1.2.2.2.1⟩
  have hDG : DGamDvdF Fm := ⟨Fm.x1 + 1, fun x hx i u => (hc x (hlt x hx) i).1.1.2.2.1 _ (hM _) u⟩
  have hTame : TameDistinctF Fm := ⟨Fm.x1 + 1, fun x hx i => (hc x (hlt x hx) i).1.1.2.1⟩
  have hCFeq : Fm.CF = C.P.CF := by
    have := congrArg (fun f : ℝ → List ℝ => (f 0).getD 9 0) hMid
    simpa [FamP.cMid, FC.cMid] using this
  have hUp : CodeUpF Fm 3 C.P.CF := by
    refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h := (hall x i).2.2
    rw [Fm.L_x x i (hlt x hx)] at h
    have hx0 : (0 : ℝ) ≤ x := by have := Fm.one_lt_family_threshold; linarith
    rw [h]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hT2 : ThickSetEventually Fm := ⟨0, fun x _ i => (hall x i).1.1⟩
  have hTT : ChosenTT Fm := ⟨0, fun x _ i => (hall x i).2.1.2.1⟩
  have hBad : ChosenBad Fm Cb := ⟨0, fun x _ i => (hall x i).1.2.1⟩
  have hCode : ChosenCode Fm 3 C.P.CF := ⟨0, fun x _ i => (hall x i).2.1.2.2⟩
  have hLink : Link ⟨eps, C, max c1 c1', max c2 c2', C5, c6, Cb⟩ (setTu Fm (cT eps 9)) := by
    refine ⟨rfl, ⟨hC5, hc6, hCb⟩, hStd, hPre, ?_, hMid, hLast⟩
    show (setTu Fm C.CTu).cOut = _
    rw [← hTu]
    exact hOut
  refine ⟨setTu Fm (cT eps 9), C.P.CF, C5, Cb, ⟨⟨⟨_, hLink, (setTu_cls _ Fm _).2 ⟨hc, hFix, hWin⟩⟩, hGc⟩, hTw⟩, zero_le_one.trans hCF,
    (setTu_large Fm K _ _).2 hLarge, hC5, hCb, hT2, hTT, hBad, hQD, hCode, hreq.2.1, hreq.2.2, hDG, ?_, hTame, hCFeq, hUp,
    hCYL.le⟩
  show cT eps Fm.CYL ≤ cT eps 9
  rw [hCYL]

end UpperTheory.Top

end
end

-- bundled from Development.AutomorphicArithmetic.CharacterBoxes.KitS
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

open GlobalTheory.Fc

theorem kitS : ∀ (Q : Par → PtProp) (la : ℝ) (G : FReq), DC.HostWW la G.req → ObjCP Q →
    KitCPW la (fun κ => ((withDuty (Q κ)).and DC.WallPt).and G.pt) := by
  intro Q la G hHost hObj
  obtain ⟨εH, hεH, hHost⟩ := hHost
  obtain ⟨εO, hεO, hObj⟩ := hObj
  refine ⟨min εH εO, lt_min hεH hεO, fun eps he he0 he1 => ?_⟩
  obtain ⟨CT2, C8, C5, c6, Cb, KW, h8, h5, h6, hb, hHost⟩ := hHost eps he (he0.trans (min_le_left _ _)) he1
  obtain ⟨KO, hObj⟩ := hObj eps C8 C5 c6 Cb he (he0.trans (min_le_right _ _)) he1 h8
  refine ⟨CT2, C8, C5, c6, Cb, KW.sup KO, h8, h5, h6, hb, fun C hC hT hP hL => ?_⟩
  obtain ⟨hLW, hLO⟩ := fc_large_of_sup hL
  obtain ⟨c1, hObj⟩ := hObj C hC hP hLO
  obtain ⟨c1', hHost⟩ := hHost C hC hT hP hLW
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, hObj⟩ := hObj cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hHost⟩ := hHost cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨xO, hObj⟩ := hObj ch ((le_max_left _ _).trans hch)
  obtain ⟨xH, S, hHost⟩ := hHost ch ((le_max_right _ _).trans hch)
  have hmid := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hG : 0 ≤ C.CGam := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  have hF : 0 ≤ C.P.CF := zero_le_one.trans (hmid _ (by simp [FC.cMid]))
  obtain ⟨xC, hCode⟩ := exists_injective_words eps C.CGam C.P.CF he he1 hG hF
  obtain ⟨xq, hq⟩ := small_prime_lt eps C8 he h8
  refine ⟨max (max xH xO) (max xC xq), S, fun s hs hx hmem => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨hxH, hxO⟩, hxC, hxq⟩ := hx
  obtain ⟨R, H, q0, a, b, hRV, hHT, hH, hqH, h0, hWin, hW, hGq⟩ := hHost s hs hxH hmem
  obtain ⟨c, hc, -⟩ := hCode s R hs hxC hRV
  have hHT' : H.CT2 = C.CT2 := hHT.trans hT.symm
  have hn : 0 < R.n := R.toFrame.ord_pos
  have hq0 : (q0 : ℝ) < s.X' := by
    have hqp : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
    have hdp : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    have hn' : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
    exact hq s _ q0 hs hxq (by positivity) hH.1.log_cond_le hH.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.1
  choose pt hsc hval har hfrom hcan hhas using
    fun i : Fin R.n => hObj s R H q0 a b _ c i.1 hs hxO hRV hHT' (by show HostGood s C.P.Cpde C5 c6 Cb H q0; rw [hP]; exact hH) hqH hWin rfl hc i.2
  choose eW heW using fun i => (hfrom i).words
  refine ⟨⟨Fin R.n, ⟨⟨0, hn⟩⟩, pt, hsc, hval, har, fun i i' => ?_, _, eW, fun i i' u u' h => ?_, fun i0 u0 hu => ?_⟩,
    fun i => ?_⟩
  · exact GlobalTheory.EX.TieSame.same_of_from C cD ch (pt i) (pt i') R H a b _ c _ _ ((hsc i).trans (hsc i').symm) (hval i) (hval i')
      (hfrom i) (hfrom i') (hcan i) (hcan i')
  · funext l
    rw [heW i u l, heW i' u' l, h]
  · rw [(hfrom i0).1] at hu
    exact ⟨⟨u0, hu⟩, (hfrom ⟨u0, hu⟩).2.2.2.2.2.2.2.2.2.1⟩
  · have hd := DC.has_withDuty_wall_and_choices (C8 := C8) (c6 := c6) (q0 := q0) (pt i) hC hHT' (by rw [hsc i]; exact hH)
      (by rw [hsc i]; exact hq0) h0 (by rw [hsc i]; exact hW) (hval i) (hfrom i) (hcan i) (hhas i)
    exact ⟨⟨hd.1, G.at_of_from (hfrom i) (by rw [hsc i]; exact hGq)⟩, hd.2⟩

end UpperTheory.Top
end

