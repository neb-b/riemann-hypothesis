module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsRealisationPrimeDataCurveLiftingStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.RunPrimeData


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_primeData_heights : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (CL : ℝ), FnAlgClosed (Xo := (T.Q.Xo j)) (c := T.Q.c) → PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → 0 < CL → (∀ w : WeightFamilies.Wt D j, LAMwAt large₂ (recB h.toLawsCore) j w CL 2) → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → G.TiedTh S (gcR large₂ (recB h.toLawsCore)) → (∀ la, InBasis G la) → Real.log G.del ≤ 1041 * Zb D large₂ ^ 3 → CombBound G S (cc D large₂ C2 A2 7 wL) nus → ∃ Qf : ∀ la, LocalPointData (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn) ∧ Heights Qf (gcR large₂ (recB h.toLawsCore)) (phR large₂ (recB h.toLawsCore) CL wL) (prwR large₂) (WeightFamilies.PPv D large₂ 200000 2) := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus CL hAlg hP hC hCL hLam G hGen hEta hTh hBas hdel hComb
  obtain ⟨hG, hT⟩ := GlobalTheory.Reg.genFrEx_and_genFromTest _ _ _ _ (T.Q.Xo j) T.Q.c
  haveI : Finite (Comp (T.Q.Xo j) T.Q.c) := CompFin.finite_comp _ _
  letI : Fintype (Comp (T.Q.Xo j) T.Q.c) := Fintype.ofFinite _
  obtain ⟨g0, hcur⟩ := _root_.GlobalTheory.RunJoin.curveHyp_of_run D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hG hP hC G hGen hEta
  have hinj := GlobalTheory.Reg.genValInj_record D T h j hj hG
  have hspl := GlobalTheory.Reg.compSplit_record D T h j hj hG
  have hbirA := fun ka wL wF G => (GlobalTheory.Reg.birSt_of_ratios_trdeg D T h j hj hG ka wL wF G).2
  have hbir := hbirA _ _ _ _ hcur.2.1
  obtain ⟨hL, hZ, hc0, hO, hPet, hP16⟩ := small_rows hP
  obtain ⟨hW, hN, hlogN, -, hlow⟩ := hGen
  obtain ⟨-, h3, hn, hn0, hDF, h2, hPO, -, hcg, -⟩ := GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N 1 hj hP hCL hN one_pos hlogN (by
      rw [Nat.cast_one, Real.log_one]; positivity)
  obtain ⟨y, hw, hc, ht, hl⟩ := GlobalTheory.T.exists_realisationPrimeData_curve_lifting D T h j hj hG (hT hG) ka wL wF
    (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 hcur hinj hspl hbir hbirA hn0
    (fun hjm => (hEta hjm).2.1.2) (gcR large₂ (recB h.toLawsCore)) (prwR large₂) Tn
  refine ⟨_, hc, ht, hl, ?_⟩
  rcases Nat.eq_zero_or_pos G.del with hd0 | hd0
  · exact GlobalTheory.RunJoin.NoPoint.heights_no_point D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S G _ _ _ _ _ hd0 hBas hc
  have hlc := (GlobalTheory.RunJoin.lamConst_lamR_rows D _ _ j (recPJ h j hj) large₂ H C2 A2 CT
    ka wL wF Tn nP nW h0 CL G.N G.del hj hP hCL hN hd0 hlogN hdel).1
  have hlN : Real.log G.N + 1 / 2 ≤ prwR large₂ * (wL.size - 1) := by
    have := hW.2.2.1
    unfold prwR
    linarith
  have hW' : G.TiedW S (gcR large₂ (recB h.toLawsCore)) (prwR large₂) :=
    ⟨hW.1, hW.2.1, by linarith, hW.2.2.2⟩
  obtain ⟨-, -, -, hH1, hH2, -, hH4, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, PLam, lNc, hPL, hlNc, hI1, w2, hw2, t2, ht2, hnz2, hs2⟩ := hH4
  have hPI : PI4 D j PLam lNc ≤ max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) :=
    (auxiliaryCuspFormConstant_monotone D j hPL hlNc).trans (le_max_right _ _)
  have hsz : (0 : ℝ) ≤ wL.size := by linarith
  have hdm : (0 : ℝ) ≤ (WeightFamilies.dimY D j : ℝ) := Nat.cast_nonneg _
  have hs2' : ∀ σ, Real.log ((recB h.toLawsCore).supN j w2 σ t2) ≤
      max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) * (WeightFamilies.dimY D j : ℝ) * wL.size := fun σ =>
    (hs2 σ).trans (by gcongr)
  have hth' : ∀ i, G.th' i ∈ (recB h.toLawsCore).Mlat j wF := fun i => hH2.2.1 (hTh i).1
  have hO2 : Real.log (|(NumberField.discr T.Q.c.F : ℝ)| ^ (1 / (Module.finrank ℚ T.Q.c.F : ℝ))) ≤ PO D large₂ := by
    have hd : (0 : ℝ) < |(NumberField.discr T.Q.c.F : ℝ)| :=
      abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero T.Q.c.F)
    rw [Real.log_rpow hd, one_div, inv_mul_eq_div]
    exact hO.2
  have hprw : 1 ≤ prwR large₂ := by unfold prwR; linarith
  obtain ⟨hA1, hA2⟩ := GlobalTheory.RunJoin.combAlg_of_tiedW D T h j hj ka wL wF S nus G _ _ _ hW hComb
  rcases lt_or_eq_of_le hj.2 with hjm | hjm
  · obtain ⟨hi, hec, -, hes, hea, hem⟩ := hEta hjm
    obtain ⟨w1, hw1, t1, ht1, hnz1, hs1⟩ := hI1 hjm
    refine GlobalTheory.T.heightInequalities_indefinite_liftIndex D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (cc D large₂ C2 A2 7 wL) (thR wL) w1 t1
      (hn ▸ hw1) ht1 hnz1 (fun σ => (hs1 σ).trans (by gcongr)) hi hem hec.2 hes hc0 hcg (hA1 hjm) hlow hea
  · refine GlobalTheory.T.heightInequality_definite_liftIndex D T h j hj hG ka wL wF _ S g0 hcur hinj hspl hbir y hw hc ht hjm hAlg h3 hn0 hBas large₂ _ _ _ _
      (max 1 (PN D large₂)) (lamR large₂ CL wL) _ (p14R wL) (200000 * zBase large₂ ^ 2) (PO D large₂) CL 2 nus w2 t2 hW' hTh hth' hw2 ht2
      hnz2 hs2' hH1 (le_max_right _ _) (hLam _) hlc (by linarith) hDF hlN hO.1 hO2 (le_max_left _ _) (le_max_left _ _)
      (le_max_left _ _) (le_max_left _ _) hPet (le_max_left _ _) hP16 hprw hPO rfl (hA2 hjm) ?_
    intro σ hσ k x hx
    have h1 := hlow σ hσ k x hx
    have h2 : I2.phiFD ((T.U j σ).X k) (thR wL) x = 0 :=
      GlobalTheory.phiFD_eq_zero_at_last_index D T h j hj hjm _ _ _ (runOK_of_pageOK hP) σ hσ k x hx
    rw [h2, mul_zero, add_zero] at h1
    exact h1


end GlobalTheory.RunPrimeData
