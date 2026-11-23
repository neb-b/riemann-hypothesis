module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXGauge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0006
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0007

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealX
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem disint_switch {n r k : ℕ} {ε : Fin n → Bool} {e : Fin r → Fin n → ℂ} {z z' : Fin n → ℂ} {T T' sc C : ℝ}
    (hF : FrameLoc ε k e z z' T T') {μS μS' : Measure (Formalism.REAL.UJ ε)}
    (hR : ∀ s ∈ SLoc ε e z, μS.map (fun x => x * s) = μS) (hR' : ∀ s ∈ SLoc ε e z', μS'.map (fun x => x * s) = μS')
    {h0 h : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε} (hh0 : IsSecLoc ε sc e z z' T T' h0)
    (hh : IsSecLoc ε sc e z z' T T' h) (hD : DisintLoc ε k T T' μS μS' h0 C) : DisintLoc ε k T T' μS μS' h C := by
  intro φ hφ
  rw [hD φ hφ]
  refine setLIntegral_congr_fun (JL.measurableSet_goodLoc r T T') (fun c hc => ?_)
  obtain ⟨s₁, hs₁, s₁', hs₁', hg⟩ :=
    Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds n r k ε e z z' T T' sc hF c hc (h0 c) (h c) (hh0 c hc) (hh c hc)
  rw [hg, JL.inner_dc μS μS' s₁ s₁' (h0 c) (hR s₁ hs₁) (hR' s₁' hs₁') φ]

theorem jacLocX_of (hJ : JacGauge) : JacLocX := by
  intro k r ε e f wf z0 zB zB' hF hk hz hz' hT hT' hG μH μH' hH hH' a a' ha ha' hma hma' κ hκ h hh
  have emb := embQ hF
  have hFL : FrameLoc ε k e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') := by
    exact ⟨by omega, hk, sig_of_frame hF, e_li hF, hF.ee, hJ_e_Qm hF hz,
      hJ_e_Qm hF hz', hJ_Qm_self hF zB, hJ_Qm_self hF zB', hT, hT'⟩
  have hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0 := Matrix.inv_eq_left_inv (Qi_mul_Qm hF)
  have hdet : IsUnit (Qm e f wf z0).det := Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)
  have hpsi : JL.psiP (ε := ε) (Qm e f wf z0) = cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) := by
    funext u
    show (fun i j => ((Qm e f wf z0)⁻¹ * uMat u * Qm e f wf z0) i j) =
      (Qi ε e f wf z0 * uMat u * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    rw [hQinv]

  obtain ⟨μsec, hμ⟩ := JL.secWb_holds k r zB zB' hk hz hz' hT hT'
  let μs : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun ζ =>
    if Tz k r zB * Tz k r zB' < Complex.normSq ζ then μsec ζ else 1
  have hμs : IsSection k r zB zB' μs := by
    refine ⟨fun i j => (hμ.1 i j).congr fun ζ hζ => ?_, fun ζ hζ => ?_⟩
    · have hζ' : Tz k r zB * Tz k r zB' < Complex.normSq ζ := hζ
      simp only [μs, if_pos hζ']
    · simp only [μs, if_pos hζ]
      exact hμ.2 ζ hζ
  have hU : ∀ ζ, (μs ζ)ᴴ * Hb k * μs ζ = Hb k := by
    intro ζ
    by_cases hζ : Tz k r zB * Tz k r zB' < Complex.normSq ζ
    · simp only [μs, if_pos hζ]; exact (hμ.2 ζ hζ).1
    · simp only [μs, if_neg hζ, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hMuj : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      Formalism.REAL.inUJ ε (Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹) := fun q hq =>
    JL.inUJ_conj (gramQ hF) hdet (JL.bigMem_holds k r q.1 (μs q.2) hq (hU q.2))

  let h0 : (Fin (r + 1) → ℂ) → Formalism.REAL.UJ ε := fun c =>
    if hc : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 then JL.ujOf _ (hMuj (JL.qOf r 1 c) hc) else 1
  have hh0q : ∀ q : (Fin r → ℂ) × ℂ, (∀ a, q.1 a ≠ 0) →
      uMat (h0 (JL.coordSc r 1 q)) = Qm e f wf z0 * bigCell k r q.1 (μs q.2) * (Qm e f wf z0)⁻¹ := by
    intro q hq
    have hq' : ∀ a, (JL.qOf r 1 (JL.coordSc r 1 q)).1 a ≠ 0 := by rw [JL.qOf_coordSc r one_pos]; exact hq
    simp only [h0, dif_pos hq', JL.uMat_ujOf, JL.qOf_coordSc r one_pos]
  have hh0 : IsSecLoc ε 1 e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') (Tz k r zB) (Tz k r zB') h0 := by
    intro c hc
    have hq1 : ∀ a, (JL.qOf r 1 c).1 a ≠ 0 := fun a =>
      mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ one_ne_zero)) (hc.1 _)
    have hζ : Tz k r zB * Tz k r zB' < Complex.normSq (JL.qOf r 1 c).2 := by
      have h2 := hc.2
      rw [JL.gv_diag_eq] at h2
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · show Tz k r zB * Tz k r zB' < Complex.normSq (c (Fin.last r)); linarith
      · exact absurd h3 (not_lt.2 (sq_nonneg _))
    have he0 := hh0q (JL.qOf r 1 c) hq1
    rw [JL.coordSc_qOf r one_pos] at he0
    show Zhat ε (famSc 1 e (Qm e f wf z0 *ᵥ zB)) (famSc 1 e (Qm e f wf z0 *ᵥ zB')) (uMat (h0 c)) = Matrix.diagonal c
    rw [he0, (JL.zBig r k ε e (Qm e f wf z0 *ᵥ zB) (Qm e f wf z0 *ᵥ zB') zB zB' (Qm e f wf z0) 1 (gramQ hF) hdet
      (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz hz' rfl rfl one_pos μs hμs (JL.qOf r 1 c) hq1 hζ).2,
      JL.coordSc_qOf r one_pos]

  have hfin : μH Set.univ ≠ ⊤ := by rw [hma]; exact ENNReal.ofReal_ne_top
  have hfin' : μH' Set.univ ≠ ⊤ := by rw [hma']; exact ENNReal.ofReal_ne_top
  refine disint_switch hFL (fun s hs => rightX_of hF hz hT hH hfin κ hκ s hs)
    (fun s hs => rightX_of hF hz' hT' hH' hfin' κ hκ s hs) hh0 hh ?_
  have hW := measW_of hF hH
  have hW' := measW_of hF hH'
  have hWa : (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a := by
    rw [emb.map_apply, Set.preimage_univ, hma]
  have hWa' : (μH'.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) Set.univ = ENNReal.ofReal a' := by
    rw [emb.map_apply, Set.preimage_univ, hma']
  open Filter Topology in
  have hGauge : IsGaugeOn (UH (Hpk k r))
        (((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map
          (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
    obtain ⟨P, hPJ, h1⟩ := exists_unitary ε (sig_of_frame hF)
    have h2 : P * Pᴴ = 1 := mul_eq_one_comm.mp h1
    set c : ℝ≥0∞ := (ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ with hc
    have hgpos := hG.2
    have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top
    have hct : c ≠ ⊤ := ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hgpos).ne'
  
    have hQ := gramQ hF
    have hQiQm := Qi_mul_Qm hF
    have hQmQi := Qm_mul_Qi hF
    have ht : (Qm e f wf z0 * Pᴴ)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ) = Formalism.REAL.Jm ε := by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose]
      calc P * (Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * (Qm e f wf z0 * Pᴴ)
          = P * ((Qm e f wf z0)ᴴ * Formalism.REAL.Jm ε * Qm e f wf z0) * Pᴴ := by simp only [Matrix.mul_assoc]
        _ = Formalism.REAL.Jm ε := by rw [hQ, PHP hPJ h2]
    set t : Formalism.REAL.UJ ε := toUJ (Qm e f wf z0 * Pᴴ) ht
    have hut : uMat t = Qm e f wf z0 * Pᴴ := uMat_toUJ _ _
    have hut' : uMat t⁻¹ = P * Qi ε e f wf z0 := by
      have hinv : uMat t⁻¹ * uMat t = 1 := by rw [← uMat_mul, inv_mul_cancel, uMat_one]
      have hr : uMat t * (P * Qi ε e f wf z0) = 1 := by
        rw [hut, Matrix.mul_assoc, ← Matrix.mul_assoc Pᴴ, h1, Matrix.one_mul, hQmQi]
      calc uMat t⁻¹ = uMat t⁻¹ * (uMat t * (P * Qi ε e f wf z0)) := by rw [hr, Matrix.mul_one]
        _ = P * Qi ε e f wf z0 := by rw [← Matrix.mul_assoc, hinv, Matrix.one_mul]
    have hfun : cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) = cM (ε := ε) Pᴴ P ∘ (fun g => t⁻¹ * g * t) := by
      funext g
      show (Qi ε e f wf z0 * uMat g * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
        Pᴴ * uMat (t⁻¹ * g * t) * P
      rw [uMat_mul, uMat_mul, hut, hut']
      simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
      rw [Matrix.mul_assoc _ Pᴴ P, h1, Matrix.mul_one]
    have emb := cM_measEmb (ε := ε) (A := Pᴴ) (B := P) (A' := P) (B' := Pᴴ) h2 h2
    have hmapeq : (c • Formalism.REAL.muG ε).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
        (c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P) := by
      have hm : Measurable (fun g : Formalism.REAL.UJ ε => t⁻¹ * g * t) := (measurable_const_mul t⁻¹).mul_const t
      rw [hfun, ← Measure.map_map emb.measurable hm, Measure.map_smul, muG_conj]
      exact hm.aemeasurable
    rw [hmapeq]
    refine ⟨?_, ?_⟩
    · rw [Measure.map_smul]
      exact isHaarOn_smul (isHaarOn_G (P0 := P) (B0 := Pᴴ) ⟨hPJ, by
        rw [← hPJ]; simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc P Pᴴ, h2, Matrix.one_mul,
          Formalism.REAL.Jm_mul_self, Matrix.mul_one]⟩) hc0 hct
      exact emb.measurable.aemeasurable
    · have hratio : ∀ ρ : ℝ,
          (((c • Formalism.REAL.muG ε).map (cM (ε := ε) Pᴴ P)) (expBall (UH (Hpk k r)) ρ)).toReal /
            (volume (Metric.ball (0 : lieE (UH (Hpk k r))) ρ)).toReal =
          (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ := by
        intro ρ
        rw [emb.map_apply, preimage_expBall hPJ h1 h2, volume_ball_lie hPJ h1 h2, Measure.smul_apply, smul_eq_mul,
          ENNReal.toReal_mul, hc, ENNReal.toReal_inv, ENNReal.toReal_ofReal hgpos.le, Formalism.MainNotions.S.Gauge.ratioAt,
          mul_div_assoc]
      have hlim : Tendsto (fun ρ => (Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.ratioAt ε ρ) (𝓝[>] 0)
          (𝓝 ((Formalism.MainNotions.S.Gauge.gaugeU ε)⁻¹ * Formalism.MainNotions.S.Gauge.gaugeU ε)) := hG.1.const_mul _
      rw [inv_mul_cancel₀ hgpos.ne'] at hlim
      exact hlim.congr fun ρ => (hratio ρ).symm
  have hJG := hJ k r zB zB' hk hz hz' hT hT' _ _ _ hGauge hW hW' a a' ha ha' hWa hWa' κ hκ μs hμs
  have hS1 := measS_of hF hz hT hH κ hκ
  have hS2 := measS_of hF hz' hT' hH' κ hκ
  intro φ hφ
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  let φh : Mt k r → ℝ≥0∞ := Function.extend Ψ φ 0
  have hφh : Measurable φh := emb.measurable_extend hφ measurable_const
  have hext : ∀ u, φh (Ψ u) = φ u := fun u => emb.injective.extend_apply φ 0 u
  have hgU : 0 < Formalism.MainNotions.S.Gauge.gaugeU ε := hG.2
  have hL : ∫⁻ x, φ x ∂(Formalism.REAL.muG ε) = ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε) *
      ∫⁻ x, φh x ∂(((ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε))⁻¹ • Formalism.REAL.muG ε).map Ψ) := by
    rw [emb.lintegral_map, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hgU).ne' ENNReal.ofReal_ne_top, one_mul]
    simp only [hext]
  rw [hL, hJG φh hφh, ← hS1, ← hS2]
  set F : (Fin (r + 1) → ℂ) → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * h0 c * s'⁻¹)
    ∂(muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)) ∂(muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)) with hF0
  have hpt : ∀ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) *
      ∫⁻ s, ∫⁻ s', φh (fun i j => (Matrix.of s * bigCell k r q.1 (μs q.2) * (Matrix.of s')⁻¹) i j)
        ∂((muSL μH' (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ)
        ∂((muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map Ψ) =
      ENNReal.ofReal (bcWeight k r (Tz k r zB) (Tz k r zB') q) * F (JL.coordSc r 1 q) := by
    intro q
    by_cases hq : ∀ a, q.1 a ≠ 0
    · congr 1
      rw [emb.lintegral_map]
      refine lintegral_congr fun u => ?_
      rw [emb.lintegral_map]
      refine lintegral_congr fun u' => ?_
      have hw := JL.psiP_mul_B hdet u u' (bigCell k r q.1 (μs q.2)) (h0 (JL.coordSc r 1 q)) (hh0q q hq)
      rw [hpsi] at hw
      rw [hw, hext]
    · push_neg at hq
      obtain ⟨a, ha0⟩ := hq
      rw [JL.bcWeight_zero _ _ q a ha0, ENNReal.ofReal_zero, zero_mul, zero_mul]
  rw [lintegral_congr hpt, JL.coordinate_weight_lintegral r k (Tz k r zB) (Tz k r zB') hk hT hT' F]
  have hK0 := Jac.jacConst_nonneg (k := k) (r := r) hT hT' ha ha' hκ
  have hV1 := Jac.volU_pos (k - 1)
  have hCX : Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) =
      Formalism.MainNotions.S.Gauge.gaugeU ε * (jacConst k r (Tz k r zB) (Tz k r zB') a a' κ * (2 ^ (r + 1))⁻¹) := by
    unfold jacConst
    field_simp
  have hC0 : 0 ≤ Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) := by
    rw [hCX]; positivity
  have hpt2 : ∀ c, ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2) * wtLoc k (Tz k r zB) (Tz k r zB') c) *
        F c =
      ENNReal.ofReal (Formalism.MainNotions.S.Gauge.gaugeU ε * Formalism.MainNotions.S.UnitaryVolumeMass.volU k ^ 2 /
      ((Tz k r zB * Tz k r zB') ^ k * Formalism.MainNotions.S.UnitaryVolumeMass.volU (k - 1) * a * a' * κ ^ 2)) *
        (ENNReal.ofReal (wtLoc k (Tz k r zB) (Tz k r zB') c) * F c) := fun c => by
    rw [ENNReal.ofReal_mul hC0, mul_assoc]
  rw [lintegral_congr hpt2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hCX,
    ENNReal.ofReal_mul hgU.le, ENNReal.ofReal_mul hK0]
  ring

end Formalism.L2.SG.Pf.NcReal.JX
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSBoxVolPf
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.BoxVolPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.Volumes Formalism.L2.SG.LocVol
  NumberField IsDedekindDomain MeasureTheory
open Formalism.L2.SG.Pf.NcS.BoxVolSk Formalism.L2.SG.Pf.NcS.BoxSteps Formalism.L2.SG.Pf.NcS.FinVolSk
open scoped TensorProduct

theorem finprod_box {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n a d : ℕ} (b : Module.Basis (Fin d) F E)
    (C : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin a → Fin n → Fv F v ⊗[F] E))
    (hCa : ∀ᶠ v in Filter.cofinite, C v = latV b v) (x : Fin a → Fin n → Af F ⊗[F] E) :
    (∏ᶠ v, (C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v x)) =
      ({x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v}.indicator 1 x : ℂ) := by
  classical
  have hev : ∀ᶠ v in Filter.cofinite, projV v x ∈ C v := by
    filter_upwards [finite_integral_holds F E n a d b x, hCa] with v h1 h2
    rw [h2]; exact h1
  have hfin : (Function.mulSupport fun v =>
      (C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ) (projV v x)).Finite := by
    refine (Filter.eventually_cofinite.1 hev).subset fun v hv => ?_
    intro hm
    apply hv
    simp [Set.indicator_of_mem hm]
  by_cases hx : ∀ v, projV v x ∈ C v
  · rw [Set.indicator_of_mem (show x ∈ {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} from hx)]
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    simp [Set.indicator_of_mem (hx v)]
  · rw [Set.indicator_of_notMem (show x ∉ {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} from hx)]
    push Not at hx
    obtain ⟨v0, hv0⟩ := hx
    exact finprod_eq_zero _ v0 (Set.indicator_of_notMem hv0 _) hfin

theorem box_volume_holds : BoxVol := by
  intro F E _ _ _ _ _ σ n J ψ a X0 hT νX hStd hdet ha hn hSWa hSWc hOm μinf νinf fibInf hμ hν hfib hne
    ωf hdec
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set TI := hermOf (Ainf F) σ (gramE σ J X0) hT with hTI
  obtain ⟨Φi, hΦc, hΦs, hΦ0, hΦint, hΦpos⟩ := positivity_test_holds F E σ n J a μinf νinf fibInf TI hfib hne
  set c : ENNReal := ∫⁻ z, ENNReal.ofReal (Φi z) ∂(fibInf TI) with hcdef
  have hc : c = ENNReal.ofReal (∫ z, Φi z ∂(fibInf TI)) :=
    (ofReal_integral_eq_lintegral_ofReal hΦint (Filter.Eventually.of_forall hΦ0)).symm
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 hΦpos).ne'
  have hcT : c ≠ ⊤ := by rw [hc]; exact ENNReal.ofReal_ne_top
  obtain ⟨hGm, hGf, hGv⟩ := gram_measurable_holds F E σ n J a (gramE σ J X0)
  have hae : ∀ᵐ y ∂νX, gramR (AF F) σ J y = (gramE σ J X0).map (inclR (AF F)) := by
    rw [Filter.Eventually, mem_ae_iff]
    simpa [Set.compl_ofPred] using hOm.1
  refine ⟨?_, ?_⟩
  · set S := {x : Fin a → Fin n → Af F ⊗[F] E | gramR (Af F) σ J x ≠ (gramE σ J X0).map (inclR (Af F))}
      with hSdef
    have h1 := hdec (fun z => ENNReal.ofReal (Φi z)) S hGm
    have hL : ∫⁻ y, ENNReal.ofReal (Φi (projInf y)) * S.indicator 1 (projFin y) ∂νX = 0 := by
      rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
      filter_upwards [hae] with y hy
      have : projFin y ∉ S := fun h => h (hGf y hy)
      simp [Set.indicator_of_notMem this]
    rw [hL] at h1
    have hS0 : ωf S = 0 := by
      rcases (mul_eq_zero.1 h1.symm) with h | h
      · exact h
      · exact absurd h hc0
    refine measure_mono_null (fun x hx => ?_) hS0
    intro hxT
    exact hx (hGv x hxT)
  · intro d b C hSB hCm hCa
    set B := {x : Fin a → Fin n → Af F ⊗[F] E | ∀ v, projV v x ∈ C v} with hBdef
    have hBm : MeasurableSet B := box_measurable_holds F E n a C hCm
    have h2 := hdec (fun z => ENNReal.ofReal (Φi z)) B hBm

    have hA1 := hOm.2.2 μinf hμ
    have hA2 := hA1.2 νinf hν
    have hdX : ∀ v, SdW F E σ n J (Fv F v) (psiV F ψ v) a (dX σ J ψ v a) := by
      intro v
      obtain ⟨μv, hμv⟩ := hA2.1
      have hex : ∃ μ, SdW F E σ n J (Fv F v) (psiV F ψ v) a μ := ⟨μv v, hμv v⟩
      simp only [dX, dif_pos hex]
      exact hex.choose_spec
    have hA3 := hA2.2 (fun v => dX σ J ψ v a) hdX
    have hdT : ∀ v, SdHerm F E σ (Fv F v) (psiV F ψ v) a (dT σ ψ v a) := by
      intro v
      obtain ⟨νv, hνv⟩ := hA3.1
      have hex : ∃ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν := ⟨νv v, hνv v⟩
      simp only [dT, dif_pos hex]
      exact hex.choose_spec
    have hA4 := hA3.2 (fun v => dT σ ψ v a) hdT
    have hA5 := hA4.2 fibInf hfib
    have hOmF : ∀ v, IsOm σ J ψ v a (omFam σ J ψ v a) := by
      intro v
      obtain ⟨fibV, hfibV⟩ := hA5.1
      have hex : ∃ fib, IsOm σ J ψ v a fib := ⟨fibV v, hfibV v⟩
      simp only [omFam, dif_pos hex]
      exact hex.choose_spec
    have hQ := hA5.2 (fun v => omFam σ J ψ v a) hOmF

    let Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin a → Fin n → Fv F v ⊗[F] E) → ℂ :=
      fun v => (C v).indicator 1
    let Φf : (Fin a → Fin n → Af F ⊗[F] E) → ℂ := fun x => ∏ᶠ v, Φv v (projV v x)
    let Φinf : (Fin a → Fin n → Ainf F ⊗[F] E) → ℂ := fun z => (Φi z : ℂ)
    let Φ : (Fin a → Fin n → AF F ⊗[F] E) → ℂ := fun y => Φinf (projInf y) * Φf (projFin y)
    have hpure : IsPureFin b Φf Φv :=
      ⟨hSB, hCa.mono fun v h => by simp only [Φv, h], fun X => rfl⟩
    obtain ⟨hInt, hMult, hEq⟩ := hQ d b Φ Φinf Φf Φv (Complex.continuous_ofReal.comp hΦc)
      (hΦs.comp_left Complex.ofReal_zero) hpure (fun X => rfl)

    let g : (Fin a → Fin n → AF F ⊗[F] E) → ℝ := fun y => Φi (projInf y) * B.indicator 1 (projFin y)
    have hΦg : ∀ y, Φ y = (g y : ℂ) := by
      intro y
      simp only [Φ, Φinf, Φf, Φv, g]
      rw [finprod_box b C hCa (projFin y), ← hBdef]
      by_cases hy : projFin y ∈ B
      · simp [Set.indicator_of_mem hy]
      · simp [Set.indicator_of_notMem hy]
    have hg0 : ∀ y, 0 ≤ g y := fun y => mul_nonneg (hΦ0 _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    have hgInt : Integrable g νX := by
      have : Integrable (fun y => (g y : ℂ)) νX := hInt.congr (Filter.Eventually.of_forall hΦg)
      exact this.re
    have hlin : ∫⁻ y, ENNReal.ofReal (g y) ∂νX =
        ∫⁻ y, ENNReal.ofReal (Φi (projInf y)) * B.indicator 1 (projFin y) ∂νX := by
      refine lintegral_congr fun y => ?_
      by_cases hy : projFin y ∈ B
      · simp [g, Set.indicator_of_mem hy]
      · simp [g, Set.indicator_of_notMem hy]
    have hLHS : ∫ y, Φ y ∂νX = ((ωf B * c).toReal : ℂ) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hΦg), integral_complex_ofReal,
        integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg0) hgInt.aestronglyMeasurable,
        hlin, h2]
    have hfinB : ωf B * c ≠ ⊤ := by
      rw [← h2, ← hlin]; exact (hgInt.lintegral_lt_top).ne
    have hωT : ωf B ≠ ⊤ := by
      intro h; apply hfinB; rw [h]; exact ENNReal.top_mul hc0

    have hloc : ∀ v, (∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
        (((omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))))
          (C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))})).toReal : ℂ) := by
      intro v
      have hom : omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))) =
          omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT) := by
        simp only [omAt, dif_pos (map_mem_HermR (Fv F v) σ (gramE σ J X0) hT)]
        rfl
      have hnull : omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT)
          {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))}ᶜ = 0 :=
        measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_left) ((hOmF v).1 _)
      rw [hom, measure_inter_conull hnull]
      have e : Φv v = fun X => (((C v).indicator (1 : (Fin a → Fin n → Fv F v ⊗[F] E) → ℝ) X : ℝ) : ℂ) := by
        funext X
        by_cases hX : X ∈ C v
        · simp [Φv, Set.indicator_of_mem hX]
        · simp [Φv, Set.indicator_of_notMem hX]
      rw [e, integral_complex_ofReal, integral_indicator_one (hCm v), Measure.real]
    let r : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
      ((omAt σ J ψ v ((gramE σ J X0).map (inclR (Fv F v))))
        (C v ∩ {X | gramR (Fv F v) σ J X = (gramE σ J X0).map (inclR (Fv F v))})).toReal
    have hMult' : Multipliable (fun v => (r v : ℂ)) := by
      have : (fun v => ∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT))) =
        fun v => (r v : ℂ) := funext hloc
      rw [← this]; exact hMult
    have hRHS : (∫ X, Φinf X ∂(fibInf (hermOf (Ainf F) σ (gramE σ J X0) hT))) *
        ∏' v, ∫ X, Φv v X ∂(omFam σ J ψ v a (hermOf (Fv F v) σ (gramE σ J X0) hT)) =
        (((∫ z, Φi z ∂(fibInf TI)) * ∏' v, r v : ℝ) : ℂ) := by
      rw [tprod_congr hloc, BoxVolSk_tprod_ofReal r hMult']
      simp only [Φinf]
      rw [integral_complex_ofReal, Complex.ofReal_mul]
    rw [hLHS, hRHS, Complex.ofReal_inj, ENNReal.toReal_mul] at hEq
    have hcR : c.toReal = ∫ z, Φi z ∂(fibInf TI) := by
      rw [hc, ENNReal.toReal_ofReal (integral_nonneg hΦ0)]
    rw [hcR, mul_comm] at hEq
    have hB : (ωf B).toReal = ∏' v, r v := mul_left_cancel₀ hΦpos.ne' hEq
    rw [← hB, ENNReal.ofReal_toReal hωT]

end Formalism.L2.SG.Pf.NcS.BoxVolPf
end
end

