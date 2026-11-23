module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegBoundOfClaimNumbers
section
namespace GlobalTheory.CovHSNum


set_option maxHeartbeats 1000000 in
theorem deg_bound_of_claim_numbers : ∀ (T D : ℕ) (PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c : ℝ), 1 ≤ D → 3 * D + 5 ≤ T → 1 ≤ PP → 1 ≤ b → Real.log b ≤ PP → (T : ℝ) * PP ≤ Real.sqrt b → z = 7 * ((D : ℝ) ^ 2 / T + D * ρ) → 0 ≤ ρ → z ≤ 1 / 2 → z * (PP * kap) ≤ b → 0 ≤ kap → 1 ≤ n → 1 ≤ Λ → 1 ≤ β → 1 ≤ ΛD → 1 ≤ ΛT → 1 ≤ δ → 0 < d → Real.log n ≤ PP → Real.log β ≤ PP → Real.log δ ≤ PP → Real.log Λ ≤ PP * (kap / T + 1) → Real.log ΛD ≤ PP * kap → Real.log ΛT ≤ PP * kap → J ≤ 4 * (D * PP * (kap / T + 1) + T * PP) + 2 * PP * (kap / T) * D → (1 - z) * d ≤ ((T - 1).choose D : ℕ) * δ → Formalism.NormVectorIdentities.Items.HSClaimS 26 T D n 1 Λ β ΛD ΛT J δ h d deg → 0 ≤ c → deg - d * c ≤ degM → ((T - 1).choose D : ℕ) * δ * ((T : ℝ) * h - 3 * ((D : ℝ) + 1) * |h| - 26 * (26 * (D : ℝ) ^ 2 + 2 * z * T) * Real.log (2 + |h|) - (4000 * b + 2 * c)) ≤ degM := by
  intro T D PP kap b z ρ n Λ β ΛD ΛT J δ h d deg degM c hD1 hDT hPP hb hlogb hTPP hz hρ hz2 hzk hkap hn hΛ hβ hΛD hΛT hδ hd hlogn hlogβ hlogδ hlogΛ hlogΛD hlogΛT hJ hcmp hclaim hc hdeg
  have hT8 : (8:ℝ) ≤ T := by exact_mod_cast (by omega : 8 ≤ T)
  have hD1r : (1:ℝ) ≤ D := by exact_mod_cast hD1
  have hDTr : (D:ℝ) + 1 ≤ T := by exact_mod_cast (by omega : D + 1 ≤ T)
  have hTpos : (0:ℝ) < T := by linarith
  have hT0 : (T:ℝ) ≠ 0 := hTpos.ne'

  have hs0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hs2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt b := by
    have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ b from hb)
    rwa [Real.sqrt_one] at this
  have hsb : Real.sqrt b ≤ b := by nlinarith [mul_le_mul_of_nonneg_left hs1 hs0]
  have hTPPb : (T:ℝ) * PP ≤ b := le_trans hTPP hsb
  have hTPP0 : 0 ≤ (T:ℝ) * PP := by positivity
  have hTPP2 : ((T:ℝ) * PP) ^ 2 ≤ b := by
    calc ((T:ℝ) * PP) ^ 2 ≤ (Real.sqrt b) ^ 2 := pow_le_pow_left₀ hTPP0 hTPP 2
      _ = b := hs2
  have hTs : (T:ℝ) ≤ Real.sqrt b := le_trans (by nlinarith) hTPP
  have hlogT : Real.log T ≤ PP / 2 := by
    have := Real.log_le_log hTpos hTs
    rw [Real.log_sqrt (by linarith)] at this
    linarith
  have hlogD : Real.log D ≤ Real.log T := Real.log_le_log (by linarith) (by linarith)
  have hlogΛ0 : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hlogβ0 : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlog1 : Real.log (1 + Real.log Λ) ≤ Real.log Λ := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log Λ by linarith)
    linarith
  have hprod : Real.log (n * D * δ * (1 + Real.log Λ)) =
      Real.log n + Real.log D + Real.log δ + Real.log (1 + Real.log Λ) := by
    have h1 : (0:ℝ) < n := by linarith
    have h2 : (0:ℝ) < D := by linarith
    have h3 : (0:ℝ) < δ := by linarith
    have h4 : (0:ℝ) < 1 + Real.log Λ := by linarith
    rw [Real.log_mul (mul_pos (mul_pos h1 h2) h3).ne' h4.ne',
      Real.log_mul (mul_pos h1 h2).ne' h3.ne', Real.log_mul h1.ne' h2.ne']

  have hD2T0 : 0 ≤ (D:ℝ) ^ 2 / T := by positivity
  have hDρ : 0 ≤ (D:ℝ) * ρ := mul_nonneg (by positivity) hρ
  have hz0 : 0 ≤ z := by rw [hz]; linarith
  have hD2z : (D:ℝ) ^ 2 ≤ z * T / 7 := by
    have e : z * T / 7 = (D:ℝ) ^ 2 + D * ρ * T := by rw [hz]; field_simp
    rw [e]; have := mul_nonneg hDρ hTpos.le; linarith
  have hD2T : (D:ℝ) ^ 2 ≤ T / 14 := by nlinarith [mul_le_mul_of_nonneg_right hz2 hTpos.le]

  have hq0 : 0 ≤ kap / T := div_nonneg hkap hTpos.le
  obtain ⟨q, hq⟩ : ∃ q : ℝ, kap / T = q := ⟨_, rfl⟩
  have hkq : kap = q * T := by rw [← hq]; field_simp
  rw [hq] at hlogΛ hJ hq0
  rw [hkq] at hzk hlogΛD hlogΛT
  clear hq hkq hkap
  have hl0 : Real.log Λ + 26 * Real.log (n * D * δ * (1 + Real.log Λ)) ≤
      27 * (PP * (q + 1)) + 65 * PP := by
    rw [hprod]; linarith
  have key := _root_.GlobalTheory.CovNum.deg_lower_of_claim T D n Λ β ΛD ΛT J δ h d deg z (27 * (PP * (q + 1)) + 65 * PP)
    (by omega) hD1 hn hΛ hβ hΛD hΛT hδ hd hz0 hz2 hcmp hl0 hclaim

  have hPPq : 0 ≤ PP * q := mul_nonneg (by linarith) hq0
  have F1 : (D:ℝ) ^ 2 * (PP * q) ≤ b / 7 := by
    linarith [mul_le_mul_of_nonneg_right hD2z hPPq]
  have F2 : (D:ℝ) ^ 2 * PP ≤ b / 14 := by
    linarith [mul_le_mul_of_nonneg_right hD2T (show (0:ℝ) ≤ PP by linarith)]
  have hDD2 : (D:ℝ) ≤ (D:ℝ) ^ 2 := by nlinarith
  have hDPPq : (D:ℝ) * (PP * q) ≤ b / 7 := by
    linarith [mul_le_mul_of_nonneg_right hDD2 hPPq]
  have hDPP : (D:ℝ) * PP ≤ b := by
    linarith [mul_le_mul_of_nonneg_right (show (D:ℝ) ≤ T by linarith) (show (0:ℝ) ≤ PP by linarith)]
  have t1 : J ≤ 9 * b := by linarith
  have hDlogT : (D:ℝ) ^ 2 * Real.log T ≤ (D:ℝ) ^ 2 * (PP / 2) :=
    mul_le_mul_of_nonneg_left hlogT (sq_nonneg _)
  have t2 : 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) ≤ 300 * b := by
    linarith
  have t3 : ((T:ℝ) + D + 1) * Real.log β ≤ 2 * b := by
    have := mul_le_mul (show (T:ℝ) + D + 1 ≤ 2 * T by linarith) hlogβ hlogβ0 (by linarith)
    linarith
  have hG : Formalism.NormVectorIdentities.Items.hsG D n + 2 ≤ 5 * D * PP := by
    unfold Formalism.NormVectorIdentities.Items.hsG
    have a1 := mul_le_mul_of_nonneg_left hlogn (show (0:ℝ) ≤ D + 1 by linarith)
    have a2 := mul_le_mul_of_nonneg_left hPP (show (0:ℝ) ≤ D by linarith)
    have a3 := mul_le_mul_of_nonneg_right hD1r (show (0:ℝ) ≤ PP by linarith)
    nlinarith
  have hG0 : 0 ≤ Formalism.NormVectorIdentities.Items.hsG D n + 2 := by
    unfold Formalism.NormVectorIdentities.Items.hsG; positivity
  have hTDPP : (T:ℝ) * D * PP ≤ b := by
    have e1 : (T:ℝ) * D * PP ≤ T * T * PP := by
      have := mul_le_mul_of_nonneg_left (show (D:ℝ) ≤ T by linarith) hTPP0
      linarith
    have e2 : (T:ℝ) * T * PP ≤ T * T * PP * PP := by
      have := mul_le_mul_of_nonneg_left hPP (mul_nonneg hTPP0 hTpos.le)
      linarith
    linarith only [e1, e2, hTPP2]
  have t4 : ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) ≤ 10 * b := by
    have := mul_le_mul (show (T:ℝ) + D ^ 2 ≤ 2 * T by linarith) hG hG0 (by linarith)
    linarith
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have p1 := mul_le_mul_of_nonneg_left hlogΛD hz0
  have p2 := mul_le_mul_of_nonneg_left hlogΛT hz0
  have p3 : z * ((T:ℝ) * Real.log β) ≤ (1/2) * ((T:ℝ) * PP) :=
    mul_le_mul hz2 (mul_le_mul_of_nonneg_left hlogβ hTpos.le) (mul_nonneg hTpos.le hlogβ0) (by norm_num)
  have p4 : z * ((T:ℝ) * Real.log 2) ≤ (1/2) * ((T:ℝ) * 1) :=
    mul_le_mul hz2 (mul_le_mul_of_nonneg_left hl2.le hTpos.le) (mul_nonneg hTpos.le hl20) (by norm_num)
  have p5 : z * ((T:ℝ) * PP) ≤ (1/2) * ((T:ℝ) * PP) :=
    mul_le_mul_of_nonneg_right hz2 hTPP0
  have t5 : 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) +
      Real.log ΛD + Real.log ΛT) ≤ 200 * b := by
    linarith

  set B : ℝ := (((T - 1).choose D : ℕ) : ℝ) * δ with hB
  have hB0 : 0 ≤ B := by positivity
  have hR : J + 26 * (D:ℝ) ^ 2 * ((27 * (PP * (q + 1)) + 65 * PP) + Real.log T) + ((T:ℝ) + D + 1) * Real.log β +
      ((T:ℝ) + D ^ 2) * (Formalism.NormVectorIdentities.Items.hsG D n + 2) + 2 * z * ((T:ℝ) * (Real.log 2 + (27 * (PP * (q + 1)) + 65 * PP) + Real.log β / 2) +
      Real.log ΛD + Real.log ΛT) ≤ 4000 * b := by linarith
  have hd2 : d ≤ 2 * B := by linarith [mul_le_mul_of_nonneg_right hz2 hd.le]
  have hdc := mul_le_mul_of_nonneg_right hd2 hc
  have hBR := mul_le_mul_of_nonneg_left hR hB0
  linarith

end GlobalTheory.CovHSNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DilatedFlatDatumIsSBHalfTameKernel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.DilFlat

theorem eToEAf_int' {D : D7} (x : 𝓞 D.host.E) : eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨(x : D.host.E), ⟨x, rfl⟩⟩, rfl⟩)

theorem isSBHalf_dilFlat : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∀ Gc : ℂ, IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i _ ξR Q _ eQ hq ϖ hϖ _ Gc
  suffices hΦ : IsSBHalf eQ (lattice₂ R i) (fun x => flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) by
    obtain ⟨h1, k, hk, h2, h3⟩ := hΦ
    exact ⟨fun t ht => h1 t (right_ne_zero_of_mul ht), k, hk, fun v hv hv' t => by simp only [h2 v hv hv' t],
      fun t ht => h3 t (right_ne_zero_of_mul ht)⟩
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hinfQ := GlobalTheory.PlaceDatum.infPart_idemSum hq
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ
  have hu : IsUnit (incA D (ϖ : D.host.E)) := (Ne.isUnit hϖE).map _
  have hc : eToEAf D (ϖ : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := eToEAf_int' ϖ
  have hfr : ∀ x : WO (Vc D i) (Wc D i), ∀ a b,
      frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x) a b =
        eToEAf D (ϖ : D.host.E) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x a b := by
    intro x a b
    have hm : ((dil i (ϖ : D.host.E) x : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (AE D)).map (toEAf D)) =
        eToEAf D (ϖ : D.host.E) • (x : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (AE D)).map (toEAf D) := by
      ext a' b'
      simp only [dil, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_mul]
      rfl
    simp only [frMapO]
    rw [hm, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  have hhalf : ∀ x : WO (Vc D i) (Wc D i), IsHalf eQ (dil i (ϖ : D.host.E) x) ↔ IsHalf eQ x := by
    intro x
    refine ⟨fun h a b => hu.mul_left_cancel ?_, fun h a b => ?_⟩
    · have := h a b
      simp only [dil, Matrix.map_apply] at this
      rw [← this]; ring
    · simp only [dil, Matrix.map_apply]
      rw [mul_left_comm, h a b]
  have key : (fun x => flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) = fun x =>
      if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x)) then
        omegaFlat Q (Wc D i).rank ξR (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x)))
      else 0 := by
    funext x
    unfold flatDat
    by_cases h : IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x))
    · rw [if_pos h, if_pos ⟨(hhalf x).2 h.1, h.2⟩]
    · rw [if_neg h, if_neg fun h' => h ⟨(hhalf x).1 h'.1, h'.2⟩]
  rw [key]
  refine GlobalTheory.PlaceDatum.isSBHalf_of_red eQ _ (fun x => frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (dil i (ϖ : D.host.E) x))
    ?_ ?_ ?_ Q _ fun y y' h => GlobalTheory.FlatVecExist.omegaFlat_congr _ _ _ h
  · intro x u k a b
    simp only [hfr, GlobalTheory.PlaceDatum.frMapO_add]
    ring
  · obtain ⟨M, hM, h⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO sV.1.fg sW.1.fg (R.βV i) (R.βW i)
    refine ⟨M, hM, fun u hu' a b => ?_⟩
    simp only [hfr]
    rw [mul_left_comm]
    exact mul_mem hc (h u hu' a b)
  · obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sV)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ sW) (R.βV i) (R.βW i)
    have hI : Ideal.span {ϖ} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hϖ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {ϖ}))
    set n := Ideal.absNorm (Ideal.span {ϖ})
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => hI (Ideal.absNorm_eq_zero_iff.1 h0)
    have hnE : eToEAf D ((y : 𝓞 D.host.E) : D.host.E) * eToEAf D (ϖ : D.host.E) = (n : EAf D) := by
      rw [← RingHom.map_mul, ← map_natCast (eToEAf D)]
      congr 1
      exact_mod_cast hy
    refine ⟨K * n, Nat.mul_pos hK hn, fun t ht hti => ?_⟩
    have hnt : IsHalf eQ (n • t) := fun a b => by
      change eQ * (n • t a b) = n • t a b
      rw [mul_smul_comm, ht a b]
    have hfn : ∀ a b, frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (n • t) a b =
        (n : EAf D) * frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) t a b := fun a b => by
      have := GlobalTheory.PlaceDatum.frMapO_add (R.βV i) (R.βW i) 0 t n a b
      rw [zero_add] at this
      rw [this]
      simp [frMapO]
    rw [← smul_smul]
    refine h _ (GlobalTheory.PlaceDatum.infPart_of_half hinfQ hnt) fun a b => ?_
    rw [hfn, ← hnE, mul_assoc, ← hfr]
    exact mul_mem (eToEAf_int' y) (hti a b)

end GlobalTheory.DilFlat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPairLatticeTheta
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DblUnitaryBox

section Alg

variable {A α β : Type} [CommRing A] [Fintype β] [DecidableEq β]

end Alg

section Meas

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

local instance (priority := high) measTup : MeasurableSpace (κ → AF F) := borel _

local instance borelTup : BorelSpace (κ → AF F) := ⟨rfl⟩

theorem integrable_normSq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    Integrable (fun x => ‖φ x‖ ^ 2) μ :=
  (schA_memLp_two F κ μ hμ φ hφ).integrable_norm_pow two_ne_zero

theorem lintegral_eq_ofReal (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖φ x‖ ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_normSq μ hμ hφ) (Filter.Eventually.of_forall fun x => by positivity)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem integral_mul_star_eq (μ : Measure (κ → AF F)) (hμ : μ.IsAddHaarMeasure) (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ φ ∈ schA F κ, T φ ∈ schA F κ)
    (hT : ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {φ₁ φ₂ : (κ → AF F) → ℂ}
    (h₁ : φ₁ ∈ schA F κ) (h₂ : φ₂ ∈ schA F κ) :
    ∫ x, T φ₁ x * star (T φ₂ x) ∂μ = ∫ x, φ₁ x * star (φ₂ x) ∂μ := by
  have hn : ∀ φ ∈ schA F κ, ∫ x, ‖T φ x‖ ^ 2 ∂μ = ∫ x, ‖φ x‖ ^ 2 ∂μ := fun φ hφ => by
    have h := hT φ hφ
    rw [lintegral_eq_ofReal μ hμ (hp φ hφ), lintegral_eq_ofReal μ hμ hφ] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => by positivity)
      (integral_nonneg fun x => by positivity)).1 h
  have hm : ∀ f ∈ schA F κ, ∀ g ∈ schA F κ, ∀ c : ℂ, f + c • g ∈ schA F κ := fun f hf g hg c =>
    (schA F κ).add_mem hf ((schA F κ).smul_mem c hg)
  have pol : ∀ (f : (κ → AF F) → ℂ), f ∈ schA F κ →
      ∀ (g : (κ → AF F) → ℂ), g ∈ schA F κ → ∫ x, f x * star (g x) ∂μ =
      (((∫ x, ‖(f + (1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) - ((∫ x, ‖(f + (-1 : ℂ) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) +
        Complex.I * ((∫ x, ‖(f + Complex.I • g) x‖ ^ 2 ∂μ : ℝ) : ℂ) -
        Complex.I * ((∫ x, ‖(f + (-Complex.I) • g) x‖ ^ 2 ∂μ : ℝ) : ℂ)) / 4 := fun f hf g hg => by
    have hi : ∀ c : ℂ, Integrable (fun x => ((‖(f + c • g) x‖ ^ 2 : ℝ) : ℂ)) μ := fun c =>
      (integrable_normSq μ hμ (hm f hf g hg c)).ofReal
    simp only [← integral_complex_ofReal]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hi _) (hi _),
      ← integral_add, ← integral_sub, ← integral_div]
    rotate_left
    · exact ((hi _).sub (hi _)).add ((hi _).const_mul _)
    · exact (hi _).const_mul _
    · exact (hi _).sub (hi _)
    · exact (hi _).const_mul _
    congr 1
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
      map_add, map_mul, map_neg, map_one, Complex.conj_I, Complex.star_def]
    linear_combination ((f x * (starRingEnd ℂ) (g x)) / 2 - (g x * (starRingEnd ℂ) (f x)) / 2) * Complex.I_mul_I
  rw [pol _ (hp _ h₁) _ (hp _ h₂), pol _ h₁ _ h₂]
  simp only [← hn _ (hm _ h₁ _ h₂ _), map_add (f := _), map_smul]


end Meas

section Shape

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {M : Type} [AddCommGroup M] [Module (AF F) M]
  {Bf : M → M → AF F}

attribute [local instance] measTup borelTup

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Shape

section Lagr

variable {R A α β m κ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype α] [DecidableEq α] [Fintype κ]
  {Bf : Matrix α β A → Matrix α β A → R} (co : Darboux Bf κ)



end Lagr

section Value

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] measTup borelTup

end Value

end GlobalTheory.DblUnitaryBox

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfMemBadPrimes
section
noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.BadLog

theorem logSum_le_log {B : Finset ℕ} {N : ℕ} (hN : N ≠ 0) (h : ∀ p ∈ B, p.Prime ∧ p ∣ N) : logSum B ≤ Real.log N := by
  have h1 : ∏ p ∈ B, p ∣ N :=
    (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) fun p hp =>
      Nat.mem_primeFactors.2 ⟨(h p hp).1, (h p hp).2, hN⟩).trans (Nat.prod_primeFactors_dvd N)
  have h0 : ∀ p ∈ B, (p : ℝ) ≠ 0 := fun p hp => by exact_mod_cast (h p hp).1.ne_zero
  unfold logSum
  rw [← Real.log_prod h0, ← Nat.cast_prod]
  refine Real.log_le_log ?_ (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h1)
  exact_mod_cast Finset.prod_pos fun p hp => (h p hp).1.pos

variable {D : D7} {L : SizeData₂ D}

theorem log_level_le (P : ParameterChoice' D L) :
    LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 ≠ 0 ∧
    Real.log ((LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 : ℕ) : ℝ) ≤ (2 * |P.CYL| + 17) * zBase L := by
  have hn : 0 < D.R.n := D.R.ord_pos
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by unfold Ranks.f; omega : 1 ≤ D.R.f)
  have hr : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ D.R.r)
  have hk : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hc0 : LevelStarExponents.condE D ≠ 0 := by
    unfold LevelStarExponents.condE
    exact mul_ne_zero (mul_ne_zero D.host.QS_pos.ne' D.host.hyp.1.ne_zero) D.host.hyp.2.1.ne_zero
  have hc1 : (1 : ℝ) ≤ LevelStarExponents.condE D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hc0
  have hc : Real.log (LevelStarExponents.condE D) ≤ L.sc.L := by
    have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ L.t_win.1
    have a : (LevelStarExponents.condE D : ℝ) ^ 36 ≤ L.sc.b ^ ((1 : ℝ) / 2) :=
      (le_mul_of_one_le_right (by positivity) ht).trans P.condE_le
    have b := Real.log_le_log (by positivity) a
    rw [Real.log_pow, Real.log_rpow hb, Scale.b, Real.log_exp] at b
    push_cast at b
    linarith
  obtain ⟨Y, y1, -, y3, y4⟩ := P.g_Y
  have hY : 0 < Y := lt_of_lt_of_le (by positivity) y1
  have hg0 : ∀ i, (0 : ℝ) < D.host.g i := fun i => hY.trans_le (y4 i).1
  have l2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have l15 : Real.log 15 ≤ 14 := by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 15 by norm_num)]
  have hg : ∀ i, Real.log (D.host.g i) ≤ 1 + |P.CYL| * L.sc.L := fun i => by
    have a := Real.log_le_log (hg0 i) (y4 i).2
    rw [Real.log_mul two_ne_zero hY.ne'] at a
    have b : P.CYL * L.sc.L ≤ |P.CYL| * L.sc.L := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith
  have hz : L.sc.L ≤ zBase L := by
    unfold zBase
    exact le_mul_of_one_le_left (by linarith) (one_le_mul_of_one_le_of_one_le hf hr)
  refine ⟨mul_ne_zero (mul_ne_zero hc0 (mul_ne_zero ?_ ?_)) (by norm_num), ?_⟩
  · exact_mod_cast (hg0 0).ne'
  · exact_mod_cast (hg0 1).ne'
  have a0 := hg0 0
  have a1 := hg0 1
  push_cast
  rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_mul a0.ne' a1.ne']
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hz (by positivity))
  linarith [hg 0, hg 1]

theorem dvd_of_mem_badPrimes {T : Core D} (hQ : T.Q.Pins) {j : ℕ} {Y : Deep T j} {e : ℕ} {o : ℝ} (h : Y.Good e o)
    {p : ℕ} (hp : p ∈ badPrimes T.Q.H Y.d.l₂) : p.Prime ∧ p ∣ LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 := by
  obtain ⟨hp, h'⟩ := mem_badPrimes.1 hp
  refine ⟨hp, ?_⟩
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * 15 ^ e := by rw [← h.pd, h.lev.1.2.1, hQ.2.1.1]
  have key : ∀ a, a ∣ LevelStarExponents.condE D → a ∣ LevelStarExponents.condE D * (D.host.g 0 * D.host.g 1) * 15 := fun a ha =>
    (ha.mul_right _).mul_right _
  have cD : ∀ a : ℕ, a.Prime → (a : ℤ) ∣ NumberField.discr D.host.E → a ∣ LevelStarExponents.condE D := D.host.der.discr_primes.1
  have c2 : 2 ∣ LevelStarExponents.condE D := cD 2 Nat.prime_two D.host.der.discr_primes.2.1
  have cd : D.host.d ∣ LevelStarExponents.condE D := cD _ D.host.hyp.2.1 D.host.der.discr_primes.2.2
  rcases h' with rfl | h' | h' | h' | h'
  · exact key _ c2
  · rw [h', hQ.1.1]; exact key _ cd
  · exact key _ (cD p hp (Int.natCast_dvd.2 h'))
  · rw [hM] at h'
    rcases (Nat.Prime.dvd_mul hp).1 h' with h' | h'
    · exact (h'.mul_left _).mul_right _
    · exact (hp.dvd_of_dvd_pow h').mul_left _
  · rw [h.lev.2] at h'
    exact absurd (Nat.dvd_one.1 h') hp.ne_one

end GlobalTheory.BadLog

end
end

