module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QuotientBoundOfKillDetectConstantRoom
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientBound_of_kill_detect_constantRoom : Known → ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ) (large₂ : SizeData₂ D) (Ck Ch Ah C₀ A₀ Cd Ad : ℝ), GlobalTheory.RunIn.GamAt T → InR D j → j < D.R.m → Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (recB h) j ka → KillQ h j ka CR Tt cc → DetectQ h j ka CR Tt cc → 1 ≤ zBase large₂ → 0 ≤ C₀ → 0 ≤ Cd → RoomAt large₂ j ka CR Tt cc C₀ A₀ →
    Real.log (@Module.finrank T.Q.c.F ((recB h).Cusp j ka) _
      ((recB h).acgC j ka).toAddCommMonoid ((recB h).modC j ka) : ℝ) ≤
      WeightFamilies.PPv D large₂ Cd Ad * ka.size →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.QAt large₂ (recB h) j ka CR Ck Ch Ah (Ch + 3 * C₀ + Cd) (max Ah (max A₀ Ad)) Tt cc := by
  intro hK D T h j ka CR Tt cc large₂ Ck Ch Ah C₀ A₀ Cd Ad hG hj hjm hlat hkill hdet hz hC₀ hCd hroom hdim
  have hbound : Formalism.MainNotions.Gaps.EtaleWeightGaps.QAt large₂ (recB h) j ka CR Ck Ch Ah (Ch + 3 * C₀ + Cd) (max Ah (max A₀ Ad)) Tt cc := by
    intro hCR hOb hn hlast hsize hT hc hTc
    have hzpos : 0 < zBase large₂ := by linarith
    have hCh : 0 ≤ Ch := by
      have h1 : (1 : ℝ) ≤ WeightFamilies.degO (recB h) := by
        unfold WeightFamilies.degO
        exact_mod_cast Module.finrank_pos
      have h2 : 0 ≤ Ch * zBase large₂ ^ Ah := (Real.log_nonneg h1).trans hOb.1
      exact nonneg_of_mul_nonneg_left h2 (Real.rpow_pos_of_pos hzpos _)
    have hA : (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka) : ℝ) ≤ ka.size := by
      have h1 := absA_add_le_size T h.pins hj ka
      have h2 : (0 : ℝ) ≤ (fdeg D.host.E : ℝ) * ka.n := by positivity
      linarith
    have hk : (0 : ℝ) ≤ ka.size := (Nat.cast_nonneg _).trans hA
    have hnpos : 0 < nAt D j ka CR Tt cc := Nat.succ_pos _
    obtain ⟨hfin, hsum⟩ := beSum_holds D.host.E (recB h).KO (nAt D j ka CR Tt cc)
      (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka)) hnpos
    have hP₀ : 0 ≤ C₀ * zBase large₂ ^ A₀ := mul_nonneg hC₀ (Real.rpow_pos_of_pos hzpos _).le
    have hsum' := hsum.trans ((mul_le_mul_of_nonneg_right hroom.2.2 (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hA hP₀))
    have hlog := log₂ (recB h) j ka CR Tt cc hlat.toIsLattice
    obtain ⟨hr1, hr2⟩ := room_of_bounds (Ah := Ah) hz hk hCh hC₀ hCd hroom.1 hroom.2.1 (hlog.trans hdim) hsum'
    refine qat_of_bridge' large₂ (recB h) j ka CR Ck Ch Ah _ _ Tt cc hlat
      (qbridge_of_numGood D large₂ (recB h) j ka CR Ch Ah _ _ Tt cc
        (beOf D.host.E (nAt D j ka CR Tt cc) (GlobalTheory.ArcCM.absA (T.Q.Dw j) (wtA ka)))
        (CarchAt D j ka CR Tt cc) (BdegAt large₂ j ka CR Tt cc) hlat (fun la => ?_) hfin hr2
        (recB_supN_conj h j ka) hr1 fun F hF => ?_) hCR hOb hn hlast hsize hT hc hTc
    · unfold beOf
      positivity
    · by_contra hno
      refine hF (hdet F fun K₁ i1 i2 i3 d hd => ?_)
      by_contra hne
      have hle : cutR T.C j ka ≤ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n :=
        (cutR_le T.C j ka).trans (cusp_le_sec _ _ _ _ _)
      obtain ⟨⟨ψ, hψ⟩, hdeg⟩ :=
        cfOf_linear_and_degree hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d (wtA ka) ka.n
      let φ := ψ.comp (Submodule.inclusion hle)
      have hφ : ∀ G : (recB h).Cusp j ka, φ G = cfOf d.yF d.μ d.jj G.1 := fun G => hψ _
      refine hno ⟨K₁, i1, i2, i3, φ, fun G hGm => ?_, ?_, ?_⟩
      · exact (hφ G).trans (hkill K₁ d hd G hGm)
      · exact fun h0 => hne ((hφ F).symm.trans h0)
      · obtain ⟨hstd, ⟨s⟩⟩ := hd
        obtain ⟨hgood, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
        obtain ⟨hpq, hr, -⟩ := hnum j hj
        have hLa := RunNum.one_le_LaAt D j ka CR Tt cc
        have hc : 0 ≤ pDeg large₂.logOm + (1 / 2) * Real.log (LaAt D j ka CR Tt cc) := by
          have := Real.log_nonneg hLa
          unfold pDeg
          positivity
        have hμ := hdeg F.1 (hle F.2) hne
        obtain ⟨hN, hNd⟩ := valLine_ndeg_le hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s large₂.logOm d.μ ka.n hLa
          (lamDegSt_logOm₂ hK D T large₂ h.pins)
        refine ⟨s.valLine d.μ ka.n, hN, hNd.trans ?_,
          _root_.GlobalTheory.ArcCM.valLine_conj hK _ _ _ _ _ K₁ _ _ _ _ _ _ _ s _ _, ?_, ?_⟩
        · unfold BdegAt
          refine mul_le_mul_of_nonneg_left ?_ hc
          rw [hμ, hf, hpq, Nat.mul_div_cancel_left _ two_pos]
          push_cast
          exact RunNum.absA_add_le_size T h.pins j hj ka
        · intro la w hw G hGm hne'
          rw [hφ] at hne' ⊢
          exact _root_.GlobalTheory.ArcCM.cfOf_fin_bound hK _ _ _ _ (T.Q.Xo j) T.Q.c K₁ d _ _ _ s
            (modelsAt_of_good_level hK _ _ _ _ _ _ (hpq ▸ hr) hgood) hstd hLa la w hw (wtA ka) ka.n G.1
            ⟨hle G.2, fun v hv => hGm la v hv⟩ hne'
        · intro em G _ hne'
          have hpos : 0 < (recB h).supN j ka (em.comp (algebraMap T.Q.c.F K₁)) G := by
            refine lt_of_le_of_ne ((recB h).supN_nonneg j ka _ G) fun h0 => hne' ?_
            rw [((recB h).supN_eq_zero j ka _ G).1 h0.symm]
            exact map_zero _
          have harch := RunNum.arch_all hK h j ka CR Tt cc hG hj K₁ d hstd s em G
          rw [hφ] at hne' ⊢
          have hnorm : 0 < ‖em (cfOf d.yF d.μ d.jj G.1)‖ := norm_pos_iff.2 ((map_ne_zero em).2 hne')
          have hlog := Real.log_le_log (mul_pos hnorm (hN.2 em)) harch
          rwa [Real.log_mul hnorm.ne' (hN.2 em).ne', Real.log_mul hpos.ne' (Real.exp_pos _).ne',
            Real.log_exp] at hlog
  exact hbound
