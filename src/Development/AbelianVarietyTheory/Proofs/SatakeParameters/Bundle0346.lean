module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0339
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MInvFdOfCharts
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0013
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.SameChart
public import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
public import Formalism.LocalToGlobal.InertKernelTheory.ScalG
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepLt
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.GlobalTheory.GL3.IsIntegralOfMemQbar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetStepScalarEq
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem half_rank_cast (R : Ranks) (j : ℕ) : (((R.N j / 2 : ℕ) : ℤ) : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ : Even (R.N j) := R.k_even.add (R.t_odd.add_one.mul_left j)
  have h1 : R.N j / 2 = a := by omega
  rw [h1, ha]
  push_cast
  ring

theorem target_scalar : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La' : (sysS H X std).Lt (j + 1)),
      dPow (mM d (j + 1) hj La').1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d (j + 1) hj La' =
        d.uT S j La' * kT J j hj La'.1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj La'
  have hjm : j < D.R.m := hj
  have hW := (_root_.GlobalTheory.TwV.DelA.wtOK_sites S j hjm ⟨La'.1⟩).dv
  obtain ⟨e, he, hmu⟩ := _root_.GlobalTheory.TwV.muT_det_ratA S j hjm
  have hG := _root_.GlobalTheory.TwV.DelB.gMat_det S (j + 1) hj
  set γ := d.gam (j + 1) hj La' with hγ
  have hmem : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj) := d.mem (j + 1) hj La'
  have hmuγ := hmu (j + 1) hj γ hmem
  have hgd := (hG.2 γ hmem).1
  have hq0 : (gMat J (j + 1) hj 1).det ≠ 0 := left_ne_zero_of_mul_eq_one hG.1
  have hdm : (mM d (j + 1) hj La').1.det * γ.1.det = (uB J (j + 1) hj La'.1).1.det := by
    have h1 : (γ⁻¹).1.det * γ.1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    simp only [mM, uB, Units.val_mul, Matrix.det_mul]
    linear_combination ((J.A.crd (j + 1) hj).1.det * (bAt J (j + 1) hj La'.1).1.det) * h1
  have hsd : ∀ τ, (D.chTw u μ).sDiv j τ = e τ - ((D.R.N j / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [(D.chTw u μ).sDiv_eq j hjm τ, Int.cast_sub, D.hcW_e, he τ, half_rank_cast]
    simp only [sExp, Nat.add_sub_cancel]
  simp only [dPow, sPt, Dec.uT, dif_pos hj, kT, hW, hsd]
  rw [← hγ, hmuγ, hgd]
  have hP : ∀ τ x, TaylorLogMetric.embT D τ x = embT D τ x := fun _ _ => rfl
  simp only [hP, map_mul]
  rw [← Finset.prod_zpow]
  have hb : ∀ τ, embT D τ (uB J (j + 1) hj La'.1).1.det ≠ 0 := fun τ => by
    rw [map_ne_zero, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hg0 : ∀ τ, embT D τ γ.1.det ≠ 0 := fun τ => by
    rw [map_ne_zero, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hq : ∀ τ, embT D τ (gMat J (j + 1) hj 1).det ≠ 0 := fun τ => by
    rw [map_ne_zero]
    exact hq0
  have hm : ∀ τ, embT D τ (mM d (j + 1) hj La').1.det = embT D τ (uB J (j + 1) hj La'.1).1.det / embT D τ γ.1.det := fun τ => by
    rw [eq_div_iff (hg0 τ), ← map_mul, hdm]
  simp only [hm]
  set n : ℤ := ((D.R.N j / 2 : ℕ) : ℤ)
  set c : ℤ := cTw D (j + 1)
  have key : ∀ τ, (embT D τ (uB J (j + 1) hj La'.1).1.det / embT D τ γ.1.det) ^ (-(e τ - n - c)) *
      embT D τ (uB J (j + 1) hj La'.1).1.det ^ (-c) =
      embT D τ γ.1.det ^ e τ * (embT D τ γ.1.det * embT D τ (gMat J (j + 1) hj 1).det) ^ (-(n + c)) *
        (embT D τ (uB J (j + 1) hj La'.1).1.det ^ (-(e τ - n)) * embT D τ (gMat J (j + 1) hj 1).det ^ (n + c)) := fun τ => by
    have h1 := hb τ
    have h2 := hg0 τ
    have h3 := hq τ
    simp only [div_zpow, mul_zpow, zpow_neg, zpow_sub₀ h1, zpow_sub₀ h2, zpow_add₀ h1, zpow_add₀ h2, zpow_add₀ h3]
    field_simp
  have hprod := Finset.prod_congr rfl (fun τ (_ : τ ∈ Finset.univ) => key τ)
  simp only [Finset.prod_mul_distrib] at hprod
  linear_combination (d.chi (j + 1) hj La' * ((D.chiD ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) La'.1 La'.2)) : ℂˣ) : ℂ) ^ c) * hprod

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPair
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.KerInert.ScalM (qbar_zpow_mem lamC_mul_mem lamC_inv_mem lamC_zpow_mem)

noncomputable section

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem scal_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, -, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  obtain ⟨hp5, -, hIn, -, -, -, hχ, -, -⟩ := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by omega
  intro j hj L0 hL0 La' hLa'
  have hj' : j < D.R.m := hmm ▸ hj
  have hL0lat : ((sysS H X std).Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat _ S.hfin j L0 hL0
  obtain ⟨hAdm, -, -, -, -, -, -, -⟩ := hPair j hj L0 La' hL0lat hLa'
  obtain ⟨hN, hN', hsd, hsd'⟩ := hAdm
  obtain ⟨ha, -, hu⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN hsd).1
  obtain ⟨ha', -, hu'⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN' hsd').1
  obtain ⟨hU0, hord0⟩ := _root_.GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length S hD hS j hj'.le L0 hL0lat
  obtain ⟨hU1, hord1⟩ := _root_.GlobalTheory.TwV.Xc.latticeTuplePoint_det_normOne_order_eq_neg_length S hD hS (j + 1) hj' La' hLa'
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj' La'.1
  have hm1 := S.law.mu_alg j hj' _ hU1
  have hm0 := S.law.mu_alg j hj' _ hU0
  have hn1 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU1
  have hn0 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU0

  have hcf : Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    unfold Base.chiFac
    exact TaylorLogMetric.Qbar.mul_mem (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _)
  have hcfn : ‖TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La'))‖ = 1 := by
    unfold Base.chiFac
    rw [lamC_mul_mem S.lam (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _), lamC_zpow_mem S.lam ha,
      lamC_zpow_mem S.lam ha', norm_mul, norm_zpow, norm_zpow, hu, hu', one_zpow, one_zpow, mul_one]
  have hmr : S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hm1 (TaylorLogMetric.Qbar.inv_mem hm0)
  refine ⟨?_, ?_⟩
  · unfold KG.scalG
    exact TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
      (qbar_zpow_mem ha' _)
  have hexp : TaylorLogMetric.lamC S.lam (KG.scalG (J.fd std) t.χ S.muT j L0 La') =
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
        (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) := by
    unfold KG.scalG
    rw [lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
        (qbar_zpow_mem ha' _),
      lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _),
      lamC_mul_mem S.lam hmr (TaylorLogMetric.Qbar.inv_mem hcf), lamC_inv_mem S.lam hcf, lamC_zpow_mem S.lam ha, lamC_zpow_mem S.lam ha']
  have hp0 : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hB' : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ = 1 := by
    rw [lamC_mul_mem S.lam hm1 (TaylorLogMetric.Qbar.inv_mem hm0), lamC_inv_mem S.lam hm0, norm_mul, norm_mul, norm_inv, norm_zpow,
      hn1, hn0, ← zpow_neg, ← mul_assoc, ← zpow_add₀ hp0, ← zpow_add₀ hp0]
    convert zpow_zero (‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖) using 2
    simp only [hord1, hord0, KG.expG, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun v _ => by ring
  rw [hexp]
  calc ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
        (TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
          (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))‖
      = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
          TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, norm_mul, norm_mul, norm_mul, norm_inv, norm_zpow, norm_zpow, hcfn, hu, hu',
          one_zpow, one_zpow, inv_one, mul_one, mul_one, mul_one]
    _ = 1 := hB'
    _ ≤ 1 := le_rfl

end GlobalTheory.TwV.Xc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedPolynomialComplexPointEvaluation
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

open MvPolynomial

theorem transpC_eval_aeval {σ κ : Type} (x : κ → ℂ) (g : σ → MvPolynomial κ ℂ) (Q : MvPolynomial σ ℂ) :
    eval x (aeval g Q) = eval (fun i => eval x (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

theorem transpC_map_eval {σ Kc : Type} [CommRing Kc] (ι : ℂ →+* Kc) (x : σ → ℂ) (R : MvPolynomial σ ℂ) :
    eval (fun i => ι (x i)) (map ι R) = ι (eval x R) := by
  induction R using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, map_X, eval_X, eval_X, map_mul]

theorem transpC_hom_aeval {σ ι' κ : Type} (φ : MvPolynomial ι' (MvPolynomial κ ℂ) →+* ℂ) (hφ : ∀ c, φ (C (C c)) = c)
    (g : σ → MvPolynomial ι' (MvPolynomial κ ℂ)) (Q : MvPolynomial σ ℂ) :
    φ (aeval g Q) = eval (fun i => φ (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.algebraMap_apply, hφ]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
  | mul_X p v hp => rw [map_mul, map_mul, hp, map_mul, aeval_X, eval_X]

theorem evFr_scalar_of_wtPol (D : D7) {N : ℕ} (ν : D.what₂.Tau → Fin N → ℕ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (hQ : Q ∈ WtPol ℂ ν) (s : D.what₂.Tau → ℂ) (hs : ∀ τ, s τ ≠ 0) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) :
    GL3Theta.evFr D Q (fun τ => s τ • y τ) = (∏ τ, ∏ r, s τ ^ ν τ r) * GL3Theta.evFr D Q y := by
  have hB : IsBor (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) := fun τ =>
    ⟨fun r c hcr => by simp [Matrix.one_apply_ne hcr.ne'], fun r => by simp [hs τ]⟩
  have h1 : colSub (fun τ => s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) Q = _ := hQ _ hB
  have h2 := congrArg (eval (fun k : GL3Theta.FrV D N => y k.1 k.2.1 k.2.2)) h1
  simp only [colSub, transpC_eval_aeval, smul_eval] at h2
  have h3 : (∏ τ, ∏ r, (s τ • (1 : Matrix (Fin N) (Fin N) ℂ)) r r ^ ν τ r) = ∏ τ, ∏ r, s τ ^ ν τ r := by simp
  rw [h3] at h2
  unfold GL3Theta.evFr
  rw [← h2]
  refine congrArg (fun x => eval x Q) ?_
  funext k
  simp [Matrix.smul_apply, Matrix.one_apply, mul_comm]

theorem transpC_polDY_eval (D : D7) {N N' : ℕ} (hle : N ≤ N') (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (GL3Theta.FrV D N) ℂ)
    (d : D.what₂.Tau → Matrix (Fin N) (Fin N') ℂ) (f' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) :
    MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D N' => f' k.1 k.2.1 k.2.2)) (fun k : GL3Theta.Idx D N N' => d k.1 k.2.2 k.2.1)
        (polDY D s Q (N' := N')) =
      GL3Theta.evFr D Q (fun τ => s τ • (d τ * f' τ).submatrix id (Fin.castLE hle)) := by
  unfold polDY
  rw [transpC_hom_aeval _ (fun c => by simp)]
  unfold GL3Theta.evFr
  refine congrArg (fun x => MvPolynomial.eval x Q) ?_
  funext k
  have hk : ((k.2.2 : Fin N) : ℕ) < N' := lt_of_lt_of_le k.2.2.2 hle
  simp [dfr, Matrix.mul_apply, Finset.mul_sum, hk]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, mul_comm (f' k.1 b _)]
  rfl

theorem evD_trDY_polDY : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → ∀ (d : D.what₂.Tau → Matrix (Fin (D.R.N j)) (Fin (D.R.N (j + 1))) ℂ) (f' : D.what₂.Tau → Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) ℂ), (∀ τ, (f' τ).det ≠ 0) → evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) * ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) = ι ((∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f')) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ s hs d f' hf
  classical
  have h' := rkT X D hN
  obtain ⟨-, hsz, -, hle, -⟩ := _root_.GlobalTheory.TwV.DelA.size_first_last_rows X D pos j hN ν hν
  have hco := (GlobalTheory.T.operatorPolynomial_coeffs_weight_extended_by_zero D (rk_le X D hN) s ν Q hQ).1
  have hreal : ∀ α, Realises X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)
      (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) := by
    intro α
    obtain ⟨R, hR⟩ := _root_.GlobalTheory.TwV.DelA.realises_of_wtPol X D pos j h' (extNu _ ν) hle _ (hco α)
    exact selOf_mem (relPhi X D pos (j + 1) h' (wT X D pos j)) _ (Submodule.mem_map.2 ⟨(_, R), hR, rfl⟩)
  let F : Fr1 D (D.R.N (j + 1)) := ⟨f', fun τ => isUnit_iff_ne_zero.2 (hf τ)⟩
  have hval : ∀ α, (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) *
      valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) f' =
      (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' := by
    intro α
    have := hreal α F
    rw [ev1_eq_prod_det_pow_mul_valZ] at this
    exact this
  have hD : evD X D pos ι hN d f' (trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) =
      ι (∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        valZ X D pos (j + 1) h' (phiC X D pos (j + 1) h' (wT X D pos j) (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α)) f' *
          ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
    unfold trDY
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    unfold evD
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
    unfold phi0
    rw [dite_eq_left h', map_mul, map_prod]
    congr 1
    · unfold valZ
      exact transpC_map_eval ι _ _
    · unfold Finsupp.prod
      refine Finset.prod_congr rfl fun k _ => ?_
      simp [eIdx, map_pow]
  have hP : ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k =
      (∏ τ, s τ ^ szT X D pos j τ) * GL3Theta.evFr D Q (dfr X D hN d f') := by
    let φ : MvPolynomial (GL3Theta.Idx D (D.R.N j) (D.R.N (j + 1))) (MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ) →+* ℂ :=
      MvPolynomial.eval₂Hom (MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (j + 1)) => f' k.1 k.2.1 k.2.2))
        (fun k => d k.1 k.2.2 k.2.1)
    have e1 : φ (polDY D s Q (N' := D.R.N (j + 1))) = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support,
        GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k := by
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
      rfl
    have e2 : φ (polDY D s Q (N' := D.R.N (j + 1))) = GL3Theta.evFr D Q (fun τ => s τ • dfr X D hN d f' τ) :=
      transpC_polDY_eval D (rk_le X D hN) s Q d f'
    have e3 : ∀ τ, ∏ r, s τ ^ ν τ r = s τ ^ szT X D pos j τ := by
      intro τ
      rw [hsz τ, Finset.prod_pow_eq_pow_sum, ← Nat.cast_sum, zpow_natCast]
    rw [← e1, e2, evFr_scalar_of_wtPol D ν Q hQ s hs]
    simp only [e3]
  rw [hD, ← map_mul]
  congr 1
  rw [Finset.sum_mul]
  calc _ = ∑ α ∈ (polDY D s Q (N' := D.R.N (j + 1))).support, (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) *
        (GL3Theta.evFr D (AddMonoidAlgebra.coeff (polDY D s Q (N' := D.R.N (j + 1))) α) f' * ∏ k ∈ α.support, d k.1 k.2.2 k.2.1 ^ α k) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [← mul_assoc, ← hval α]
        ring
    _ = _ := by rw [← Finset.mul_sum, hP, mul_assoc]

end GlobalTheory.TwV.DelA

end
end

