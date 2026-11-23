module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCW
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj CoordinateScalingProducts

theorem coordW_exact (r k : ℕ) (T T' sc : ℝ) (hk : 1 ≤ k) (hT : 0 < T) (hT' : 0 < T') (hsc : 0 < sc)
    (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
      ENNReal.ofReal ((2 ^ (r + 1) * nrm r sc * lamW r k sc)⁻¹) *
        ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) := by
  have hlam0 : ∀ a, lam r sc a ≠ 0 := lam_ne hsc
  have hΛ0 : 0 < lamW r k sc := Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (hlam0 a)) _
  have hN0 : 0 < nrm r sc := Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hlam0 a)
  have hpos : 0 < 2 ^ (r + 1) * nrm r sc * lamW r k sc := mul_pos (mul_pos (by positivity) hN0) hΛ0

  have hDl : ∀ l, Continuous fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l := by
    intro l
    by_cases hl : l ≤ r + 1
    · have e : (fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l) = fun c => ∏ i : Fin l, c (Fin.castLE hl i) :=
        funext fun c => dl_diag c l hl
      rw [e]; fun_prop
    · have e : (fun c : Fin (r + 1) → ℂ => Dl (Matrix.diagonal c) l) = fun _ => 0 :=
        funext fun c => by simp [Dl, hl]
      rw [e]; exact continuous_const
  have hGv : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv]
    exact ((hDl (r + 1)).norm.pow 2).sub (continuous_const.mul ((hDl r).norm.pow 2))
  have hGood : MeasurableSet (GoodLoc (r := r) T T') := by
    have e : GoodLoc (r := r) T T' =
        (⋂ l, {c : Fin (r + 1) → ℂ | c l ≠ 0}) ∩ {c | 0 < Gv T T' (Matrix.diagonal c)} := by
      ext c; simp [GoodLoc]
    rw [e]
    exact ((isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const).inter
      (isOpen_lt continuous_const hGv)).measurableSet

  have hptq : ∀ q : (Fin r → ℂ) × ℂ, Complex.normSq q.2 ≠ T * T' →
      Gi r k T T' F (coordSc r sc q) =
        ENNReal.ofReal (lamW r k sc) * (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q)) := by
    intro q hq
    have hw := wt_cs hk T T' sc q
    have hg := gv_cs T T' sc q
    by_cases hq0 : ∀ a, q.1 a ≠ 0
    · by_cases hz : T * T' < Complex.normSq q.2
      · have hmem : coordSc r sc q ∈ GoodLoc (r := r) T T' := by
          refine ⟨fun l => ?_, ?_⟩
          · refine Fin.lastCases ?_ (fun a => ?_) l
            · rw [coordSc_last]
              intro h0
              rw [h0, map_zero] at hz
              exact absurd hz (not_lt.2 (mul_pos hT hT').le)
            · rw [coordSc_cs]; exact mul_ne_zero (hlam0 a) (hq0 a)
          · rw [hg]
            exact mul_pos (Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (mul_ne_zero (hlam0 a) (hq0 a))) 2)
              (by linarith)
        rw [Gi, Set.indicator_of_mem hmem, hw, Formalism.QuantumDeterminants.bcWeight, if_pos hz.le, ENNReal.ofReal_mul hΛ0.le, mul_assoc]
      · have hlt : Complex.normSq q.2 < T * T' := lt_of_le_of_ne (not_lt.1 hz) hq
        have hnot : coordSc r sc q ∉ GoodLoc (r := r) T T' := by
          rintro ⟨-, hp⟩
          rw [hg] at hp
          exact absurd hp (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos
            (Finset.prod_nonneg fun a _ => by positivity) (sub_neg.2 hlt).le))
        rw [Gi, Set.indicator_apply_eq_zero.2 (fun h => absurd h hnot), Formalism.QuantumDeterminants.bcWeight,
          if_neg (not_le.2 hlt), ENNReal.ofReal_zero, zero_mul, mul_zero]
    · push_neg at hq0
      obtain ⟨a, ha⟩ := hq0
      have hnot : coordSc r sc q ∉ GoodLoc (r := r) T T' := by
        rintro ⟨hne, -⟩
        exact hne a.castSucc (by rw [coordSc_cs, ha, mul_zero])
      have hp : ∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by
          rw [ha, norm_zero]
          exact zero_pow (by have := a.isLt; unfold Formalism.QuantumDeterminants.Mdim; omega))
      have hb : Formalism.QuantumDeterminants.bcWeight k r T T' q = 0 := by
        unfold Formalism.QuantumDeterminants.bcWeight; split_ifs <;> simp [hp]
      rw [Gi, Set.indicator_apply_eq_zero.2 (fun h => absurd h hnot), hb, ENNReal.ofReal_zero, zero_mul, mul_zero]

  have hnull : ∀ᵐ c : Fin (r + 1) → ℂ, Complex.normSq (c (Fin.last r)) ≠ T * T' := by
    have hS : (volume : Measure ℂ) {ζ | Complex.normSq ζ = T * T'} = 0 := by
      refine measure_mono_null (fun ζ hζ => ?_) (Measure.addHaar_sphere volume (0 : ℂ) (Real.sqrt (T * T')))
      simp only [Set.mem_setOf_eq] at hζ
      rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    have h0 : (volume : Measure (Fin (r + 1) → ℂ)) {c | Complex.normSq (c (Fin.last r)) = T * T'} = 0 := by
      exact Measure.pi_eval_preimage_null (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (i := Fin.last r) hS
    exact ae_iff.2 (by simpa using h0)
  have hpt : ∀ᵐ c : Fin (r + 1) → ℂ, Gi r k T T' F c = ENNReal.ofReal (lamW r k sc) *
      (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' ((Phe r sc hsc).symm c)) * F c) := by
    filter_upwards [hnull] with c hc
    have hc' : coordSc r sc ((Phe r sc hsc).symm c) = c := by
      rw [← phe_apply hsc, MeasurableEquiv.apply_symm_apply]
    have h2 : ((Phe r sc hsc).symm c).2 = c (Fin.last r) := by
      conv_rhs => rw [← hc']
      rw [coordSc_last]
    have key := hptq ((Phe r sc hsc).symm c) (by rw [h2]; exact hc)
    rw [hc'] at key
    exact key

  have hL : ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) =
      ENNReal.ofReal (nrm r sc)⁻¹ * ∫⁻ c : Fin (r + 1) → ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' ((Phe r sc hsc).symm c)) * F c := by
    rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_Phe hsc, lintegral_map_equiv]
    refine lintegral_congr fun q => ?_
    rw [MeasurableEquiv.symm_apply_apply, phe_apply]
  rw [hL, show (∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r))) =
      ∫⁻ c, Gi r k T T' F c ∂(dcLoc (r := r)) from (lintegral_indicator hGood _).symm,
    dcLoc_eq, lintegral_smul_measure, smul_eq_mul, lintegral_congr_ae hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (inv_pos.2 hpos).le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

theorem lam_one (r : ℕ) (a : Fin r) : lam r 1 a = 1 := by simp [lam]

theorem nrm_one (r : ℕ) : nrm r 1 = 1 := by simp [nrm, lam_one]

theorem lamW_one (r k : ℕ) : lamW r k 1 = 1 := by simp [lamW, lam_one]

theorem coordinate_weight_lintegral (r k : ℕ) (T T' : ℝ) (hk : 1 ≤ k) (hT : 0 < T) (hT' : 0 < T')
    (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) :
    ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r 1 q) =
      ENNReal.ofReal ((2 ^ (r + 1))⁻¹) *
        ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) := by
  rw [coordW_exact r k T T' 1 hk hT hT' one_pos F, nrm_one, lamW_one, mul_one, mul_one]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXMeas
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem embQ (hF : IsFrameJ ε e f wf z0) :
    MeasurableEmbedding (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) :=
  cM_measEmb (ε := ε) (A := Qi ε e f wf z0) (B := Qm e f wf z0) (A' := Qm e f wf z0) (B' := Qi ε e f wf z0)
    (Qm_mul_Qi hF) (Qm_mul_Qi hF)

theorem Qm_e (a : Fin r) : Qm e f wf z0 *ᵥ bvec (eI k r a) = e a := by rw [Qm_mulVec_bvec, colQ_eI]

theorem Qm_f (a : Fin r) : Qm e f wf z0 *ᵥ bvec (esI k r a) = f a := by rw [Qm_mulVec_bvec, colQ_esI]

theorem conj_fix (hF : IsFrameJ ε e f wf z0) {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {v : Fin (2 * r + k + 1) → ℂ} (hv : s *ᵥ v = v) :
    (Qm e f wf z0 * s * Qi ε e f wf z0) *ᵥ (Qm e f wf z0 *ᵥ v) = Qm e f wf z0 *ᵥ v := by
  rw [Matrix.mulVec_mulVec]
  have e1 : Qm e f wf z0 * s * Qi ε e f wf z0 * Qm e f wf z0 = Qm e f wf z0 * s := by
    rw [Matrix.mul_assoc (Qm e f wf z0 * s), Qi_mul_Qm hF, Matrix.mul_one]
  rw [e1, ← Matrix.mulVec_mulVec, hv]

theorem measW_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} {μH : Measure (Formalism.REAL.UJ ε)}
    (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH) :
    Formalism.MainNotions.S.IsHaarOn (UWset k r zB) (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := embQ hF
  obtain ⟨hsf, hne, hcon, hinv⟩ := hH
  haveI := hsf
  refine ⟨emb.sigmaFinite_map, (Measure.map_ne_zero_iff emb.measurable.aemeasurable).mpr hne, ?_, ?_⟩
  · rw [emb.map_apply]
    refine measure_mono_null (fun g hg => ?_) hcon
    intro hgH
    apply hg
    exact conj_mem_UWset hF rfl (uMat_mem g) (fun a => (hgH.1 a).1) (fun a => (hgH.1 a).2) hgH.2
  · intro s hs
    have ht := conjQ_UJ hF hs.1
    set t := toUJ (Qm e f wf z0 * s * Qi ε e f wf z0) ht
    have htH : t ∈ Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB) := by
      show (∀ a, uMat t *ᵥ e a = e a ∧ uMat t *ᵥ f a = f a) ∧ uMat t *ᵥ (Qm e f wf z0 *ᵥ zB) = Qm e f wf z0 *ᵥ zB
      rw [uMat_toUJ]
      refine ⟨fun a => ⟨?_, ?_⟩, conj_fix hF hs.2.2⟩
      · rw [← Qm_e (e := e) (f := f) (wf := wf) (z0 := z0) a]; exact conj_fix hF (hs.2.1 a).1
      · rw [← Qm_f (e := e) (f := f) (wf := wf) (z0 := z0) a]; exact conj_fix hF (hs.2.1 a).2
    rw [Measure.map_map (measurable_lmulM s) emb.measurable]
    have hfun : lmulM s ∘ cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) =
        cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) ∘ (fun g : Formalism.REAL.UJ ε => t * g) := by
      funext g
      simp only [Function.comp, lmulM_cM]
      unfold cM
      rw [uMat_mul, uMat_toUJ]
      simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
      try rfl
    rw [hfun, ← Measure.map_map emb.measurable (measurable_const_mul t), hinv t htH]

theorem measN_of (hF : IsFrameJ ε e f wf z0) (κ : ℝ) :
    (ENNReal.ofReal κ • refN ε e f wf z0).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ) := by
  have emb := embQ hF
  rw [Measure.map_smul _ emb.measurable.aemeasurable, refN, emb.map_comap, Jac.haarLie_eq_smul (Nset k r) (ENNReal.ofReal κ)]
  congr 1
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hc : (Formalism.MainNotions.S.haarLie (Nset k r) 1) {x | Matrix.of x ∉ Nset k r} = 0 := Jac.nilradical_measure_is_haar.2.2.1
  refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hc)
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hxN
  apply hx
  have hU := conjQ_UJ hF hxN.1
  refine ⟨toUJ _ hU, ?_⟩
  show Qi ε e f wf z0 * uMat (toUJ _ hU) * Qm e f wf z0 = x
  rw [uMat_toUJ, Qi_Qm_conj hF]
  rfl

theorem haarN_of (κ : ℝ) (hκ : 0 < κ) : Formalism.MainNotions.S.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) :=
  Formalism.MainNotions.BridgeCSB.haarLieN k r _ (ENNReal.ofReal_pos.2 hκ).ne' ENNReal.ofReal_ne_top

theorem psi_mul (hF : IsFrameJ ε e f wf z0) (n h : Formalism.REAL.UJ ε) :
    cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) (n * h) =
      Jac.mm (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) n) (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) h) :=
  (cM_comp_mul hF (Qm e f wf z0) n h).symm

theorem measS_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hT : 0 < Tz k r zB) {μH : Measure (Formalism.REAL.UJ ε)} (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH)
    (κ : ℝ) (hκ : 0 < κ) :
    (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      Formalism.MainNotions.S.muS (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)))
        (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) := by
  have emb := embQ hF
  have hW := measW_of hF hH
  have hN := haarN_of (k := k) (r := r) κ hκ
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  set μW := μH.map Ψ with hμW
  set μN := Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ) with hμN
  set μN' := ENNReal.ofReal κ • refN ε e f wf z0 with hμN'
  haveI : SigmaFinite μH := hH.1
  haveI : SigmaFinite μW := hW.1
  haveI : SigmaFinite μN := hN.1
  have hNmap : μN'.map Ψ = μN := measN_of hF κ
  have hWB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ hN
  apply Measure.ext_of_lintegral
  intro g hg
  have hgm : Measurable fun p : Mt k r × Mt k r => g (Jac.mm p.1 p.2) := hg.comp Jac.measurable_mt_mul
  rw [Jac.lintegral_muS μW μN hg, lintegral_map hg emb.measurable]
  have hmul : Measurable fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => p.1 * p.2 := measurable_mul
  have hgΨ : Measurable fun a : Formalism.REAL.UJ ε => g (Ψ a) := hg.comp emb.measurable
  rw [show muSL μH μN' = (μN'.prod μH).map (fun p => p.1 * p.2) from rfl,
    lintegral_map hgΨ hmul,
    lintegral_prod (fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => g (Ψ (p.1 * p.2))) (hgΨ.comp hmul).aemeasurable]
  have hpm : ∀ n h : Formalism.REAL.UJ ε, Ψ (n * h) = Jac.mm (Ψ n) (Ψ h) := psi_mul hF
  simp only [hpm]
  have step1 : ∀ n : Formalism.REAL.UJ ε, ∫⁻ h, g (Jac.mm (Ψ n) (Ψ h)) ∂μH = ∫⁻ y, g (Jac.mm (Ψ n) y) ∂μW := by
    intro n
    rw [hμW, emb.lintegral_map]
  simp_rw [step1]
  rw [← emb.lintegral_map (μ := μN') (f := fun x => ∫⁻ y, g (Jac.mm x y) ∂μW), hNmap]
  rw [lintegral_lintegral_swap (f := fun x y => g (Jac.mm x y)) hgm.aemeasurable]

  have hconc : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r zB := by
    have h0 : μW {x | Matrix.of x ∉ UWset k r zB} = 0 := hW.2.2.1
    exact ae_iff.2 h0
  refine lintegral_congr_ae ?_
  filter_upwards [hconc] with h hh
  have hd : IsUnit (Matrix.of h).det := JL.RI.det_unit_of_UH hh.1
  have hhi : (Matrix.of h)⁻¹ ∈ UWset k r zB := JL.RI.inv_mem_UW hh
  have hc : μN.map (conjM (k := k) (r := r) (Matrix.of h)⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r zB μN hz hT hWB _ hhi
  conv_rhs => rw [← hc]
  have hmh : Measurable fun n : Mt k r => g (Jac.mm h n) := hgm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hmh (Jac.meas_conjM _)]
  refine lintegral_congr fun x => ?_
  congr 1
  show Jac.mm x h = Jac.mm h (conjM (Matrix.of h)⁻¹ x)
  funext i j
  show (Matrix.of x * Matrix.of h) i j = (Matrix.of h * ((Matrix.of h)⁻¹ * Matrix.of x * ((Matrix.of h)⁻¹)⁻¹)) i j
  rw [Matrix.nonsing_inv_nonsing_inv _ hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mul]

theorem haarW_B (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB) (hT : 0 < Tz k r zB)
    {μH : Measure (Formalism.REAL.UJ ε)} (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH)
    (hfin : μH Set.univ ≠ ⊤) :
    Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r zB) (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := embQ hF
  have hW := measW_of hF hH
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r zB hz hT
  have hνfin : ∀ K, (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) K < ⊤ := fun K =>
    lt_of_le_of_lt (measure_mono (Set.subset_univ K)) (by rw [emb.map_apply, Set.preimage_univ]; exact hfin.lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (UWset k r zB) μ0 _ (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r zB) h0
    hW.2.2.1 hW.2.2.2 (fun K _ => hνfin K)
  exact ⟨hW.2.2.1, hW.2.2.2, fun a ha => by rw [hc, Measure.map_smul _ (JL.RI.meas_rmul a).aemeasurable, h0.right a ha], fun K _ => hνfin K, hW.2.1⟩

theorem rightX_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hT : 0 < Tz k r zB) {μH : Measure (Formalism.REAL.UJ ε)}
    (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH) (hfin : μH Set.univ ≠ ⊤)
    (κ : ℝ) (hκ : 0 < κ) (s : Formalism.REAL.UJ ε) (hs : s ∈ SLoc ε e (Qm e f wf z0 *ᵥ zB)) :
    (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map (fun x => x * s) =
      muSL μH (ENNReal.ofReal κ • refN ε e f wf z0) := by
  have emb := embQ hF
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  set μS := muSL μH (ENNReal.ofReal κ • refN ε e f wf z0) with hμS
  have hN := haarN_of (k := k) (r := r) κ hκ
  have hWB := haarW_B hF hz hT hH hfin
  have hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) :=
    Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ hN
  have hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0 := Matrix.inv_eq_left_inv (Qi_mul_Qm hF)
  have hdet : IsUnit (Qm e f wf z0).det := Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)
  set sM : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Qi ε e f wf z0 * uMat s * Qm e f wf z0 with hsM
  have hSs : sM ∈ Sset k r zB := by
    have := (JL.setCorr_holds r k ε e (Qm e f wf z0 *ᵥ zB) zB (Qm e f wf z0) (gramQ hF) hdet
      (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz rfl hT s).1 hs
    rw [hQinv] at this
    exact this
  have hmeas : Measurable fun x : Formalism.REAL.UJ ε => x * s := measurable_mul_const s
  have hfun : Ψ ∘ (fun x => x * s) = Formalism.FourierDecayAlt.B.rmulF sM ∘ Ψ := by
    funext x
    show (Qi ε e f wf z0 * uMat (x * s) * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      (Qi ε e f wf z0 * uMat x * Qm e f wf z0) * (Qi ε e f wf z0 * uMat s * Qm e f wf z0)
    rw [uMat_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (Qi ε e f wf z0 * uMat x) (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.mul_one]
  have key : (μS.map (fun x => x * s)).map Ψ = μS.map Ψ := by
    rw [Measure.map_map emb.measurable hmeas, hfun,
      ← Measure.map_map (JL.RI.meas_rmul (k := k) (r := r) _) emb.measurable, hμS, measS_of hF hz hT hH κ hκ]
    exact JL.RI.muS_right hz hT hWB hNB _ hSs
  rw [← emb.comap_map (μS.map (fun x => x * s)), key, emb.comap_map]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXUni
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic

def sq2 : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

theorem sq2_mul_sq2_eq_half : sq2 * sq2 = 1 / 2 := by
  unfold sq2
  rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
  push_cast; ring

theorem star_sq2_eq_self : star sq2 = sq2 := by
  unfold sq2; rw [Complex.star_def, Complex.conj_ofReal]

def u1 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then -sq2 else 1

def u2 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val < r then sq2 else if r + k < i.val then sq2 else 0

def Pu (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if j = i then u1 k r i else 0) + (if i = sig k r j then u2 k r i else 0)

theorem Pu_star (k r : ℕ) (i j : Fin (2 * r + k + 1)) : star (Pu k r i j) = Pu k r i j := by
  unfold Pu u1 u2
  split_ifs <;> simp [star_sq2_eq_self]

theorem PuJPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r) i j = Hpk k r i j := by
  have hJ : Formalism.REAL.Jm (epsK k r) = diagonal (dK k r) := rfl
  rw [hJ, Matrix.mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2, dK, epsK, sgn, decide_eq_true_eq]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      rw [if_neg h1, if_neg hjs, if_neg h2', if_neg h3, if_neg hjs]
      norm_num

theorem PuPu_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    ((Pu k r)ᴴ * Pu k r) i j = (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j := by
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [conjTranspose_apply, Pu_star]
  unfold Pu
  simp only [add_mul, mul_add, Finset.sum_add_distrib, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hi := i.isLt
  have hs := sig_val k r i
  have h2 := sq2_mul_sq2_eq_half
  by_cases hji : j = i
  · subst hji
    simp only [Fin.ext_iff]
    simp only [u1, u2]
    split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
    all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
      linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
  · by_cases hjs : j = sig k r i
    · subst hjs
      simp only [sig_sig]
      have hji' : ¬ (sig k r i).val = i.val := fun h => hji (Fin.ext h)
      simp only [Fin.ext_iff]
      simp only [u1, u2]
      split_ifs at * <;> first | (exfalso; omega) | ring_nf | skip
      all_goals first | ring | linear_combination h2 | linear_combination (-1 : ℂ) * h2 |
        linear_combination (2 : ℂ) * h2 | linear_combination (-2 : ℂ) * h2
    · have h1 : ¬ i = j := fun h => hji h.symm
      have h2' : ¬ i = sig k r j := fun h => hjs ((eq_sig_iff k r i j).1 h)
      have h3 : ¬ sig k r j = sig k r i := fun h => hji ((sig_inj k r j i).1 h)
      simp [h1, hjs, h2', h3]

theorem PuJPu (k r : ℕ) : (Pu k r)ᴴ * Formalism.REAL.Jm (epsK k r) * Pu k r = Hpk k r := by
  ext i j; exact PuJPu_apply k r i j

theorem PuPu (k r : ℕ) : (Pu k r)ᴴ * Pu k r = 1 := by
  ext i j; exact PuPu_apply k r i j

theorem exists_unitary {r k : ℕ} (ε : Fin (2 * r + k + 1) → Bool)
    (hs : (Finset.univ.filter (fun i => ε i = false)).card = r + 1) :
    ∃ P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r ∧ Pᴴ * P = 1 := by
  obtain ⟨σ, hσ⟩ := Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.PF.exists_perm ε hs
  refine ⟨Matrix.of fun i j => Pu k r (σ.symm i) j, ?_, ?_⟩
  · rw [← PuJPu k r]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Formalism.REAL.Jm, mul_diagonal, conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply, hσ m]
  · rw [← PuPu k r]
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [conjTranspose_apply, of_apply]
    refine (Fintype.sum_equiv σ _ _ (fun m => ?_)).symm
    simp only [Equiv.symm_apply_apply]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

