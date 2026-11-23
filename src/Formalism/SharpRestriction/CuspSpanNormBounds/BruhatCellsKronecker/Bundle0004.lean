module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CfgTopFalseIff
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CriticalThresholdLowerBound
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.OwnEvIntro
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyCriticalLevelLowerBound
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

theorem v_ge_of_hyp {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ}
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : 1 ≤ D.host.v := by
  dsimp only [StandingHypotheses] at hH
  exact hH.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ka_pos_of {D : D7} (hv : 1 ≤ D.host.v) : 0 < D.host.ka := by
  show 0 < Real.pi / D.host.v
  exact div_pos Real.pi_pos (by linarith)

theorem gg_pos (D : D7) : 0 < gg D := by
  unfold gg
  exact mul_pos (Nat.cast_pos.mpr (D.host.g_prime 0).pos) (Nat.cast_pos.mpr (D.host.g_prime 1).pos)

theorem VV_pos (D : D7) (τ : D.what₂.Tau) : 0 < VV D τ := by
  unfold VV
  exact mul_pos (D.dsig_pos τ) (Finset.prod_pos fun i _ => by positivity)

theorem last_shifted_parameter_eq {D : D7} {C0 : ℝ} (hD : StandingNumericalData D C0) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2 := by
  dsimp only [StandingNumericalData] at hD
  exact hD.2.2.2.2.1 u τ

theorem critical_level_ratio_le_exp {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT C1 : ℝ} (h40 : 40 ≤ Cl)
    (hC1 : Real.exp (3 / 4) ≤ C1) : LocalBesselAndTopKernel.SecondBoundHyp D large₂ C0 C' Cl Cg cb Cu cT CT C1 := by
  rintro ⟨hD, hH, -⟩ u u' τ
  have ok := cfg_ok hD hH τ
  have sm := cfg_small hH h40 τ
  have hka := ka_pos_of (v_ge_of_hyp hH)
  have hrd : 0 < D.host.rdE := Formalism.MainNotions.S.rdE_pos D
  have hTW := Formalism.FourierDecayAlt.P.critical_threshold_words (cfgOf D τ) (deOf D u) (deOf D u') D.host.ka D.host.rdE
    (gg D) (VV D τ) ok sm.hvth (isWord_deOf D u) (isWord_deOf D u') hka hrd (gg_pos D) (VV_pos D τ)
  rw [← Tcrit_eq D u τ hka.le, ← Tcrit_eq D u' τ hka.le, ← Vand_u D u τ (last_shifted_parameter_eq hD u τ),
    ← Vand_u D u' τ (last_shifted_parameter_eq hD u' τ)]
  exact le_trans (le_of_eq hTW.1) (hTW.2.2.trans hC1)

theorem cfg_aeff (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) : (cfgOf D τ).aeff = aEff D u τ := by
  simp only [aEff, uOne_one D u τ]
  by_cases h : S.IsTop D τ
  · simp [cfgOf, Sz.Cfg.aeff, h]
  · have hk : 1 ≤ D.R.k - 1 := by
      have := D.R.m_add_three_le_k
      omega
    have hv := cfg_v D τ 1 le_rfl hk
    simp [cfgOf, Sz.Cfg.aeff, h] at hv ⊢
    first | exact hv | linarith | simp [hv]

theorem cfg_aeff_pos {D : D7} {τ : D.what₂.Tau} (ok : (cfgOf D τ).Ok) : 0 < (cfgOf D τ).aeff := by
  generalize cfgOf D τ = c at ok ⊢
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast ok.hk
  have hD := ok.hDel
  have hv0 := ok.hv0
  have hv1 : 0 ≤ c.v 1 := by
    unfold Sz.Cfg.v
    push_cast
    nlinarith
  have ha := ok.ha
  unfold Sz.Cfg.aeff
  split_ifs with ht
  · obtain ⟨hbp, -⟩ := ok.htop ht
    have hb1 := ok.hb1
    exact div_pos (mul_pos (by nlinarith) (by linarith)) (mul_pos (by linarith) (by linarith))
  · nlinarith

theorem cOne_ge {c : Sz.Cfg} {bb : ℝ} (ok : c.Ok) (sm : c.Small bb) : 1 / 5 ≤ Sz.cOne c bb := by
  have hk : (4 : ℝ) ≤ c.k := by exact_mod_cast ok.hk
  have hm : (2 : ℝ) ≤ c.m := by exact_mod_cast ok.hm
  have hD := ok.hDel
  have hE : 9 / 10 ≤ Real.exp (-(2 * c.m * Real.log bb / c.k)) := by
    have h := Real.add_one_le_exp (-(2 * c.m * Real.log bb / c.k))
    linarith [sm.hmu]
  have hV : 0 ≤ c.vthp ∧ c.vthp ≤ 1 / 10 := by
    unfold Sz.Cfg.vthp
    split_ifs with ht
    · obtain ⟨hbp, -⟩ := ok.htop ht
      have hb1 := ok.hb1
      have hvth := sm.hvth
      unfold Sz.Cfg.vth at hvth
      have hbp0 : 0 < c.bp := by linarith
      rw [div_le_iff₀ (by linarith)] at hvth
      constructor
      · positivity
      · rw [div_le_iff₀ hbp0]
        nlinarith [mul_nonneg (sub_nonneg.mpr hm) (mul_nonneg (by linarith : (0 : ℝ) ≤ c.k)
          (by linarith : (0 : ℝ) ≤ c.Del))]
    · norm_num
  unfold Sz.cOne
  rw [le_div_iff₀ (by linarith [hV.1])]
  norm_num
  linarith [hV.1, hV.2, hE]

theorem critical_level_lower_bound {D : D7} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT ep0 CV C3' : ℝ} (h40 : 40 ≤ Cl)
    (hep : ep0 ≤ 1 / 2) (hC3 : 1 ≤ C3') : LocalBesselAndTopKernel.LocalTiedPairs D large₂ C0 C' Cl Cg cb Cu cT CT ep0 CV C3' := by
  rintro ⟨hD, hH, -⟩ hG u τ
  have ok := cfg_ok hD hH τ
  have sm := cfg_small hH h40 τ
  have hv1 := v_ge_of_hyp hH
  have hka := ka_pos_of hv1
  have hH' := hH
  dsimp only [StandingHypotheses] at hH'
  obtain ⟨-, -, hmf, hfk, -, -, -, -, -, -, -, hg1, -, -, -, hbO, -, -, -, -, -, -, -, -, -⟩ := hH'
  have hm2 : 2 ≤ D.R.m := ok.hm
  have hk16n : 16 ≤ D.R.k :=
    le_trans (le_trans (by norm_num) (Nat.pow_le_pow_left hm2 4)) (hmf.trans hfk)
  have hk16 : (16 : ℝ) ≤ D.R.k := by exact_mod_cast hk16n
  have hb1 : 1 ≤ large₂.sc.b := sm.hbb
  have hrd1 : 1 ≤ D.host.rdE := by
    have hvdef : D.host.v = D.host.rdE / 2 := rfl
    linarith
  have hka_eq : D.host.ka = 2 * Real.pi / D.host.rdE := by
    show Real.pi / D.host.v = _
    rw [show D.host.v = D.host.rdE / 2 from rfl]
    field_simp
  have hg0 : (16 : ℝ) ^ 8 ≤ (D.host.g 0 : ℝ) := by
    have h16 : (16 : ℝ) ≤ (D.R.k : ℝ) * large₂.sc.b := by nlinarith
    exact le_trans (pow_le_pow_left₀ (by norm_num) h16 8) hg1
  have hg1' : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast (D.host.g_prime 1).one_lt.le
  have hgg : 2 * Real.pi ≤ gg D := by
    unfold gg
    nlinarith [Real.pi_le_four]
  obtain ⟨hG1, hG2⟩ := hG τ
  have hVVpos := VV_pos D τ
  have hvpos : 0 < vand (lamSH D.R (D.hc τ)) := by
    by_contra hneg
    push_neg at hneg
    have h3 : Real.exp (CV * D.R.k * D.R.m * large₂.sc.L) * vand (lamSH D.R (D.hc τ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hneg
    linarith
  have hFD : Sz.FormalDegreeLower (cfgOf D τ) (1 / 2) (VV D τ) := by
    unfold Sz.FormalDegreeLower
    rw [Vand_lam D τ]
    nlinarith
  have hTL := Formalism.FourierDecayAlt.P.critical_threshold_lower_bound (cfgOf D τ) D.R.rS large₂.sc.b (deOf D u) D.host.ka D.host.rdE
    (gg D) (VV D τ) ok (m_eq D) sm (isWord_deOf D u) hrd1 hka_eq hgg hFD
  rw [← Tcrit_eq D u τ hka.le, ← Vand_u D u τ (last_shifted_parameter_eq hD u τ), ← cfg_aeff D u τ]
  refine le_trans ?_ hTL
  show _ ≤ Sz.cOne (cfgOf D τ) large₂.sc.b * gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ *
    (∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j) / (cfgOf D τ).aeff
  have hpow : D.host.ka ^ (-((D.R.m : ℝ) - 1)) = (D.host.ka ^ (D.R.m - 1))⁻¹ := by
    rw [Real.rpow_neg hka.le, show ((D.R.m : ℝ) - 1) = ((D.R.m - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega : 1 ≤ D.R.m)]
      simp, Real.rpow_natCast]
  rw [hpow]
  have hkC : (D.R.k : ℝ) ^ (-C3') ≤ 1 / 5 := by
    have h1 : (D.R.k : ℝ) ^ (-C3') ≤ (D.R.k : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (D.R.k : ℝ)⁻¹ ≤ (16 : ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).2 hk16
    linarith
  have hc1 := cOne_ge ok sm
  have hP : 0 ≤ ∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j := by
    refine Finset.prod_nonneg fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    exact le_trans (le_max_of_le_left (Real.rpow_nonneg (by linarith) _)) (hbO τ j h1 h2).1
  have hA : 0 ≤ gg D ^ D.R.m * (D.host.ka ^ (D.R.m - 1))⁻¹ * (∏ j ∈ Finset.Icc 1 D.R.m, bOne D τ j)
      / (cfgOf D τ).aeff := by
    have h1 := cfg_aeff_pos ok
    have h2 := gg_pos D
    positivity
  have key := mul_le_mul_of_nonneg_right (hkC.trans hc1) hA
  exact (le_of_eq (by ring)).trans (key.trans (le_of_eq (by ring)))

variable {eps : ℝ}

theorem family_critical_level_ratio (Fm : FamP eps) {C0 Cg cb Cu cT CT C1 : ℝ} (h40 : 40 ≤ sCl Fm)
    (hC1 : Real.exp (3 / 4) ≤ C1) : LocalBesselAndTopKernel.TheoremThreePassage Fm C0 Cg cb Cu cT CT C1 :=
    ⟨0, fun x _ i hh => critical_level_ratio_le_exp h40 hC1 hh⟩

theorem family_critical_level_lower_bound (Fm : FamP eps) {C0 Cg cb Cu cT CT ep0 CV C3' : ℝ} (h40 : 40 ≤ sCl Fm)
    (hep : ep0 ≤ 1 / 2) (hC3 : 1 ≤ C3') (hg : LocalBesselAndTopKernel.FamilyTopBound Fm C0 Cg cb Cu cT CT ep0 CV) :
    LocalBesselAndTopKernel.LocalSplitExponents Fm C0 Cg cb Cu cT CT C3' := by
  obtain ⟨x0, hx0⟩ := hg
  refine ⟨x0, fun x hx i hh => ?_⟩
  exact critical_level_lower_bound (C0 := C0) (CV := CV) (ep0 := ep0) h40 hep hC3 hh (hx0 x hx i hh)

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyFormalDegreeLowerBound
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset MeasureTheory
open scoped InnerProductSpace

private theorem szh_sf_inner_lemma (N : ℕ) (a : Fin N) :
    ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ((N - ((a : ℕ) + 1)).factorial : ℝ) := by
  rw [Finset.prod_nbij (fun b : Fin N => (b : ℕ)) (t := Finset.Ico ((a : ℕ) + 1) N)
    (g := fun j : ℕ => ((j : ℝ) - ((a : ℕ) : ℝ))) ?_ ?_ ?_ ?_]
  · rw [Finset.prod_Ico_eq_prod_range]
    have e : ∀ k ∈ range (N - ((a : ℕ) + 1)),
        ((((a : ℕ) + 1 + k : ℕ) : ℝ) - ((a : ℕ) : ℝ)) = ((k + 1 : ℕ) : ℝ) := by
      intro k _
      push_cast
      ring
    rw [Finset.prod_congr rfl e, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [Finset.mem_Ico]
    exact ⟨hb, b.2⟩
  · intro x _ y _ hxy
    exact Fin.ext hxy
  · intro j hj
    simp only [Finset.coe_Ico, Set.mem_Ico] at hj
    refine ⟨⟨j, hj.2⟩, ?_, rfl⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    show (a : ℕ) < j
    omega
  · intro b _
    rfl

theorem szh_sf (N : ℕ) :
    ∏ a : Fin N, ∏ b ∈ univ.filter (fun b : Fin N => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      ∏ i ∈ range N, (i.factorial : ℝ) := by
  simp_rw [szh_sf_inner_lemma]
  refine (Fin.prod_univ_eq_prod_range (fun i : ℕ => ((N - (i + 1)).factorial : ℝ)) N).trans ?_
  refine Eq.trans ?_ (Finset.prod_range_reflect (fun i : ℕ => (i.factorial : ℝ)) N)
  apply Finset.prod_congr rfl
  intro i _
  show ((N - (i + 1)).factorial : ℝ) = ((N - 1 - i).factorial : ℝ)
  rw [show N - (i + 1) = N - 1 - i by omega]

theorem szh_fdegHC {N : ℕ} (lam : Fin N → ℝ) (h : StrictAnti lam) :
    Formalism.QuantumDeterminants.fdegHC lam = vand lam / ∏ i ∈ range N, (i.factorial : ℝ) := by
  unfold Formalism.QuantumDeterminants.fdegHC vand
  rw [szh_sf]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact abs_of_pos (sub_pos.mpr (h hb))

theorem szh_vand_nonneg {N : ℕ} (lam : Fin N → ℝ) (h : StrictAnti lam) : 0 ≤ vand lam := by
  unfold vand
  apply Finset.prod_nonneg
  intro a _
  apply Finset.prod_nonneg
  intro b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
  exact sub_nonneg.mpr (h hb).le

section Rec

variable (D : D7)

theorem szh_lam_node (τ : D.what₂.Tau) (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : ¬ a.1 < D.R.k - 1) :
    lamSH D.R (D.hc τ) a = -bOne D τ (a.1 - (D.R.k - 1) + 1) := by
  unfold lamSH lamS bOne
  simp [h]
  split_ifs <;> simp

theorem szh_eps_cloud (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.1 < D.R.k - 1) : epsSH D.R a = true := by
  unfold epsSH epsS
  simp [h]

theorem szh_eps_first (a : Fin (2 * D.R.rS + D.R.k + 1)) (h : a.1 = D.R.k - 1) : epsSH D.R a = true := by
  unfold epsSH epsS
  simp [h]

variable {D} {large₂ : SizeData₂ D} {C0 C' Cl Cg cb Cu cT CT : ℝ}

theorem szh_anti (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) : StrictAnti (lamSH D.R (D.hc τ)) := by
  have hr := dimS_eq D.R
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hd, -, -, hCl⟩ := hH
  have hk0 : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hm0 : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  have hpos : 0 < Cl * ↑D.R.k * ↑D.R.m ^ 4 + ↑D.R.r * ↑D.R.m ^ 10 :=
    add_pos_of_pos_of_nonneg (mul_pos (mul_pos hCl hk0) (pow_pos hm0 4)) (by positivity)
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  unfold lamSH
  have h := hd τ (Fin.cast hr (Fin.castSucc i))
    (by have := i.2; simp only [Fin.coe_cast, Fin.coe_castSucc]; omega)
  have e : ∀ hh, (⟨(Fin.cast hr (Fin.castSucc i) : ℕ) + 1, hh⟩ : Fin D.R.r) = Fin.cast hr i.succ :=
    fun hh => Fin.ext (by simp)
  rw [e] at h
  linarith

theorem szh_hc (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) := by
  refine ⟨szh_anti hH τ, fun a => ?_⟩
  obtain ⟨j, hj⟩ := D.R.k_even
  have hn : (((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) - 1) / 2 = ((D.R.rS + j : ℕ) : ℝ) := by
    rw [hj]
    push_cast
    ring
  rw [hn]
  unfold lamSH lamS
  split_ifs with h1 h2
  · obtain ⟨z, hz⟩ := (D.hc τ).v_int ⟨_, h1⟩
    exact ⟨z - ((D.R.rS + j : ℕ) : ℤ), by rw [hz]; push_cast; ring⟩
  · obtain ⟨z, hz⟩ := (D.hc τ).b_int ⟨_, h2⟩
    exact ⟨-z - ((D.R.rS + j : ℕ) : ℤ), by rw [hz]; push_cast; ring⟩
  · exact ⟨-((D.R.rS + j : ℕ) : ℤ), by push_cast; ring⟩

theorem szh_gap (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ))
      (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
  have hr := dimS_eq D.R
  have hrdef : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hkm := D.R.m_add_three_le_k
  have hanti := szh_anti hH τ
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, -⟩ := hH
  have key : ∀ a b : Fin (2 * D.R.rS + D.R.k + 1), a < b → epsSH D.R a ≠ epsSH D.R b →
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L ≤
        lamSH D.R (D.hc τ) a - lamSH D.R (D.hc τ) b := by
    intro a b hab he
    have hab' : (a : ℕ) < b := hab
    have hbo := b.2
    have hb1 : ¬ (b : ℕ) < D.R.k - 1 := by
      intro h1
      exact he (by rw [szh_eps_cloud D a (by omega), szh_eps_cloud D b h1])
    have hb2 : (b : ℕ) ≠ D.R.k - 1 := by
      intro h2
      exact he (by rw [szh_eps_cloud D a (by omega), szh_eps_first D b h2])
    have hac : a ≤ (⟨(b : ℕ) - 1, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) := by
      show (a : ℕ) ≤ (b : ℕ) - 1
      omega
    have hlac := hanti.antitone hac
    have e1 := szh_lam_node D τ ⟨(b : ℕ) - 1, by omega⟩ (by show ¬ (b : ℕ) - 1 < D.R.k - 1; omega)
    have e2 := szh_lam_node D τ b hb1
    have i1 : (b : ℕ) - 1 - (D.R.k - 1) + 1 = (b : ℕ) - (D.R.k - 1) := by omega
    simp only [i1] at e1
    have hg := hgap τ ((b : ℕ) - (D.R.k - 1)) (by omega) (by omega)
    linarith
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact (key a b h hab).trans (le_abs_self _)
  · subst h
    exact absurd rfl hab
  · rw [abs_sub_comm]
    exact (key b a h (Ne.symm hab)).trans (le_abs_self _)

theorem szh_b_sq (large₂ : SizeData₂ D) : large₂.sc.b ^ (2 : ℝ) = Real.exp (2 * large₂.sc.L) := by
  unfold Formalism.BasicNotions.Scale.b
  rw [← Real.exp_mul]
  congr 1
  ring

theorem szh_k_le (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (h1 : 1 ≤ Cl) (τ : D.what₂.Tau) :
    (D.R.k : ℝ) ≤ Real.exp (2 * large₂.sc.L) := by
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hkC : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ Cl := by
    calc (D.R.k : ℝ) = (D.R.k : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (D.R.k : ℝ) ^ Cl := Real.rpow_le_rpow_of_exponent_le hk1 h1
  unfold StandingHypotheses at hH
  simp only [] at hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hb, -⟩ := hH
  have hj := hb τ 1 le_rfl (by have := D.R.two_le_m; omega)
  refine hkC.trans ((le_max_left _ _).trans (hj.1.trans (hj.2.trans (le_of_eq ?_))))
  first
    | exact szh_b_sq large₂
    | (unfold Formalism.BasicNotions.Scale.b; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring)

end Rec

end Formalism.MainNotions.BridgeLemma

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.ParabolicSumAdmissibleOfParabolic
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt Formalism.MainNotions.S.UnitaryVolumeMass MeasureTheory Formalism.QuantumDeterminants
open scoped ENNReal InnerProductSpace

section HS

variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsNormSq_eq_sum (A : Wq →L[ℂ] Wp) :
    hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ Wq i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_nonneg (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum]; positivity

def hsVec (A : Wq →L[ℂ] Wp) : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  WithLp.toLp 2 (fun i => A (stdOrthonormalBasis ℂ Wq i))

theorem hsVec_norm_sq (A : Wq →L[ℂ] Wp) : ‖hsVec A‖ ^ 2 = hsNormSq A := by
  rw [hsNormSq_eq_sum, PiLp.norm_sq_eq_of_L2]
  rfl

theorem hsNormSq_real_smul (c : ℝ) (A : Wq →L[ℂ] Wp) : hsNormSq (((c : ℝ) : ℂ) • A) = c ^ 2 * hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [_root_.smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end HS

section Rec

variable (D : D7) (large₂ : SizeData₂ D)

theorem jhUnit_le {W : LocW D.R.k D.R.rS} (w w' : D.what₂.Word) (A : LocS W)
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (νR : Measure (Mt D.R.k D.R.rS))
    (γ : MatKR D.R.k D.R.rS) (wt B : ℝ) (hB : 0 ≤ B)
    (h : ENNReal.ofReal (wt * hsNormSq (A.J νR γ)) ≤ ENNReal.ofReal B * MMv D w w' A μsec) :
    wt * hsNormSq (jhUnit D w w' A μsec νR γ) ≤ B := by
  unfold jhUnit
  rw [hsNormSq_real_smul]
  by_cases hM : (MMv D w w' A μsec).toReal = 0
  · rw [hM, Real.zero_rpow (by norm_num)]
    simpa using hB
  · have hpos : 0 < (MMv D w w' A μsec).toReal := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hM)
    have htop : MMv D w w' A μsec ≠ ⊤ := fun e => hM (by rw [e]; rfl)
    rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul hB] at h
    have h2 : wt * hsNormSq (A.J νR γ) ≤ B * (MMv D w w' A μsec).toReal :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hpos.le)).1 h
    have h3 : ((MMv D w w' A μsec).toReal ^ (-(1 / 2 : ℝ))) ^ 2 = ((MMv D w w' A μsec).toReal)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_neg_one]
      norm_num
    rw [h3]
    calc wt * (((MMv D w w' A μsec).toReal)⁻¹ * hsNormSq (A.J νR γ))
        = (wt * hsNormSq (A.J νR γ)) * ((MMv D w w' A μsec).toReal)⁻¹ := by ring
      _ ≤ (B * (MMv D w w' A μsec).toReal) * ((MMv D w w' A μsec).toReal)⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hpos.le)
      _ = B := by field_simp

end Rec

section Fam

variable {eps : ℝ} (Fm : FamP eps)

end Fam

end Formalism.MainNotions.BridgeLemma

end
end

