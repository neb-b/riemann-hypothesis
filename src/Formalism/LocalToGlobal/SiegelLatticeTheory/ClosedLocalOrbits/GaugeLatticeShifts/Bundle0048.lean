module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0047
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecMeasLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeRA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationRealHolds
section
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

theorem haar_disintegration_real_holds : HaarDisintegrationReal := by
  have hR : JacobianCoordinates.JL.RightInvS :=
    JacobianCoordinates.JL.rightInvS_of JacobianCoordinates.JL.setCorr_holds (JacobianCoordinates.JL.haarCorr_of JacobianCoordinates.JL.setCorr_holds)
  have hU : JacobianCoordinates.UnimodLoc := hR
  exact UnitaryIsometries.haar_disintegration_of_local ProductExactness.product_formula_holds JacobianCoordinates.JL.jacLoc_holds ProductExactness.SecMeasLoc_holds hU
    NilradicalHermitianFrames.NH.NHLoc_holds ProductExactness.StepReal_holds

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IotaDictOut
section
noncomputable section

namespace Formalism.L2.SG.Pf

theorem iotaDictAllC_holds : IotaDictAllC := iotaDictAllC_of iotaBridgeRAC_holds

theorem iotaDictC_holds : IotaDictC := iotaDictC_holds_of iotaBridgeRAC_holds

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdExactHolds
section
noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sf_smul {β : Type*} [MeasurableSpace β] (μ : Measure β) [SigmaFinite μ] (c : ℝ≥0∞) (hc : c ≠ ∞) :
    SigmaFinite (c • μ) := by
  rw [← ENNReal.coe_toNNReal hc, ← ENNReal.smul_def]
  infer_instance

theorem ProdExact_holds : Formalism.L2.SG.Pf.NcReal.ProdExact := by
  classical
  intro D X u u' μN μN' μH μH' C hσN hσN' hσH hσH' hC hN hN' hH hH' hDis
  haveI : ∀ v, SigmaFinite (μN v) := hσN
  haveI : ∀ v, SigmaFinite (μN' v) := hσN'
  haveI : ∀ v, SigmaFinite (μH v) := hσH
  haveI : ∀ v, SigmaFinite (μH' v) := hσH'
  have hU : UnimodLoc := JL.rightInvS_of JL.setCorr_holds (JL.haarCorr_of JL.setCorr_holds)
  have hep : ∀ v a b, hJ (X.B.I.ε v) (eV X v a) (pV X v b) = if a = b then 1 else 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ef]; simp)
  have hpp : ∀ v a b, hJ (X.B.I.ε v) (pV X v a) (pV X v b) = 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ff]; simp)
  have hzp : ∀ w v b, hJ (X.B.I.ε v) (zV X w v) (pV X v b) = 0 := fun w v b => by
    have h0 : hJ (X.B.I.ε v) (pV X v b) (zV X w v) = 0 :=
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w b).2]; simp)
    rw [hJ_cj, h0, map_zero]
  have hSH : ∀ w v, IsHaarS (SLoc (X.B.I.ε v) (eV X v) (zV X w v)) (muSv X w v) := fun w v =>
    NilradicalHermitianFrames.NH.NHLoc_holds _ _ _ _ _ _ _ _ _ _ (frameLoc_X X w u v) (hep v) (hpp v) (hzp w v) _ _
      (muNv_haar X w v) (muHv_haar X w v)

  have fN : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)],
      X.muN w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muNv X w v := by
    intro w μ _ hw v
    obtain ⟨_, h0, hc, hi⟩ := X.muN_haar w
    rw [← NinfG_coe, hw] at hc hi
    rw [hw] at h0
    rw [NinfG, Subgroup.coe_pi] at hc
    exact PiM.factor_uniq μ (NGv X w) (fun v => NilradicalHermitianFrames.NH.NG_closed _ _ _) (muNv X w)
      (fun v => (muNv_haar X w v).1.2.2.1) (fun v => (muNv_haar X w v).1.2.2.2) (fun v => (muNv_haar X w v).1.2.1)
      h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v
  have fH : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)],
      X.muH w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muHv X w v := by
    intro w μ _ hw v
    obtain ⟨_, h0, hc, hi⟩ := X.muH_haar w
    rw [← HinfG_coe, hw] at hc hi
    rw [hw] at h0
    rw [HinfG, Subgroup.coe_pi] at hc
    exact PiM.factor_uniq μ (HGv X w) (fun v => NilradicalHermitianFrames.NH.HG_closed _ _ _ _) (muHv X w)
      (fun v => (muHv_haar X w v).1.2.2.1) (fun v => (muHv_haar X w v).1.2.2.2) (fun v => (muHv_haar X w v).1.2.1)
      h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v
  choose κN hκN0 hκNT hκN using fN u μN hN
  choose κN' hκN'0 hκN'T hκN' using fN u' μN' hN'
  choose κH hκH0 hκHT hκH using fH u μH hH
  choose κH' hκH'0 hκH'T hκH' using fH u' μH' hH'
  have hSL : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) = (κN v * κH v) • muSv X u v := fun v => by
    haveI : SigmaFinite (muHv X u v) := inferInstance
    unfold Formalism.L2.SG.Pf.NcReal.muSL muSv
    rw [hκN v, hκH v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
    all_goals exact measurable_mul.aemeasurable
  have hSL' : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) = (κN' v * κH' v) • muSv X u' v := fun v => by
    unfold Formalism.L2.SG.Pf.NcReal.muSL muSv
    rw [hκN' v, hκH' v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
    all_goals exact measurable_mul.aemeasurable
  haveI : ∀ w v, SigmaFinite (muSv X w v) := fun w v => (hSH w v).1.1
  haveI hσS : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) := fun v => by
    rw [hSL v]; exact sf_smul _ _ (ENNReal.mul_ne_top (hκNT v) (hκHT v))
  haveI hσS' : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) := fun v => by
    rw [hSL' v]; exact sf_smul _ _ (ENNReal.mul_ne_top (hκN'T v) (hκH'T v))

  have hmS : ∀ (w : D.what₂.Word) (ρN ρH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (ρN v)]
      [∀ v, SigmaFinite (ρH v)] [∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v))],
      X.muN w = Measure.pi ρN → X.muH w = Measure.pi ρH →
      muS X w = Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v) := by
    intro w ρN ρH _ _ hσ h1 h2
    unfold muS
    rw [h1, h2]
    have mp := measurePreserving_piProd ρN ρH
    rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
      mp.measurable]
    haveI : ∀ v, SigmaFinite (((ρN v).prod (ρH v)).map
        (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hσ
    exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
      (fun v => measurable_mul.aemeasurable)
  have hmu := hmS u μN μH hN hH
  have hmu' := hmS u' μN' μH' hN' hH'

  have hsec := fun v => SecMeasLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) one_pos
  choose hs hsm hss using hsec
  have hloc : ∀ v, Formalism.REAL.muG (X.B.I.ε v) =
      ((nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)).prod ((Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)).prod
        (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)))).map (phiLoc (X.B.I.ε v) (hs v)) := fun v =>
    muG_eq_map _ _ _ _ _ _ _ (hsm v) _ (hDis v (hs v) (hss v))
  intro φ hφ
  have hpf := prod_formula (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v))
    (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) hs hsm hloc φ hφ
  change ∫⁻ x, φ x ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = _
  rw [hpf]
  have hwm : ∀ v, Measurable fun c : Fin (D.R.rS + 1) → ℂ => ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') c) :=
    fun v => ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont D.R.k (Tw u) (Tw u')).measurable)
  have hν : Measure.pi (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) =
      ((dcInf X).restrict (Good X u u')).withDensity
        (fun c => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v))) := by
    unfold nuLoc
    haveI : SigmaFinite (dcLoc (r := D.R.rS)) := by unfold dcLoc; infer_instance
    rw [PiM.pi_withDensity _ _ hwm (fun v x => ENNReal.ofReal_ne_top), ← Measure.restrict_pi_pi, good_eq]
    rfl
  set H : (Cinf X) → X.B.I.Ginf := fun c v => hs v (c v) with hHd
  have hHm : Measurable H := Measurable.of_eval fun v => (hsm v).comp (measurable_pi_apply v)
  set μP := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) with hμP
  set μP' := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) with hμP'
  set Fc : Cinf X → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * H c * s'⁻¹) ∂μP' ∂μP with hFc
  have hFm : Measurable Fc := by
    have h1 : Measurable fun q : (Cinf X × X.B.I.Ginf) × X.B.I.Ginf => φ (q.1.2 * H q.1.1 * q.2⁻¹) :=
      hφ.comp (((measurable_snd.comp measurable_fst).mul (hHm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h1.lintegral_prod_right'.lintegral_prod_right'
  rw [show (∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => hs v (c v)) * s'⁻¹) ∂μP' ∂μP
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) = ∫⁻ c, Fc c
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v) from rfl,
    hν, lintegral_withDensity_eq_lintegral_mul _
      (f := fun c : Cinf X => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)))
      (Finset.measurable_prod _ fun v _ => (hwm v).comp (measurable_pi_apply v)) hFm]
  have hGm : MeasurableSet (Good X u u') := by
    rw [good_eq]; exact MeasurableSet.univ_pi fun v => measurableSet_goodLoc _ _
  refine setLIntegral_congr_fun hGm fun c hc => ?_
  simp only [Pi.mul_apply]
  have hcv : ∀ v, c v ∈ GoodLoc (r := D.R.rS) (Tw u) (Tw u') := fun v => by
    rw [good_eq, Set.mem_univ_pi] at hc; exact hc v
  have hW : ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)) =
      ENNReal.ofReal ((∏ v, C v) * wt X u u' c) := by
    rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (hC v).le (wtLoc_nonneg _ _ _ (hcv v)),
      Finset.prod_mul_distrib]
    rfl
  have hex := StepReal_holds D X u u' 1 one_pos c hc
  have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf; rw [dite_eq_left hex]; exact hex.choose_spec
  have hdc := fun v => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) (c v)
    (hcv v) (hs v (c v)) (hOf X u u' 1 c v) (hss v (c v) (hcv v)) (hh v)
  choose t ht t' ht' htt using hdc
  have hofe : hOf X u u' 1 c = t * H c * t'⁻¹ := funext fun v => htt v
  have hrt : μP.map (fun x => x * t) = μP :=
    PiM.pi_map_mul_right _ t fun v => by
      rw [hSL v, Measure.map_smul,
        hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u u' v) _ (hSH u v) (t v) (ht v)]
      exact (measurable_id.mul measurable_const).aemeasurable
  have hrt' : μP'.map (fun x => x * t') = μP' :=
    PiM.pi_map_mul_right _ t' fun v => by
      rw [hSL' v, Measure.map_smul,
        hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u' u v) _ (hSH u' v) (t' v) (ht' v)]
      exact (measurable_id.mul measurable_const).aemeasurable
  have hsw : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' 1 c * s'⁻¹) ∂μP' ∂μP = Fc c := by
    rw [hofe]; exact dc_switch _ _ φ hφ (H c) t t' hrt hrt'
  rw [hW, hmu, hmu', hsw]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfApprox
section
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

def RatSolApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (G G' : Matrix (Kap X) (Kap X) X.B.I.E) (k N : ℕ), 1 ≤ N →
    ∃ C : ℝ, ∀ P : InfinitePlace X.B.I.F → Matrix (Kap X) (Kap X) ℂ,
      (∀ v, InPat (lvk X) k (P v) ∧ InPat (lvk X) 1 (G'.map (X.B.I.φ v) * P v * G.map (X.B.I.φ v))) →
      ∃ Y0 : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) k Y0 ∧ InPat (lvk X) 1 (G' * Y0 * G) ∧
        (∃ A : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E), Y0 = (N : X.B.I.E) • A.map (fun a => (a : X.B.I.E))) ∧
        ∀ v i j, ‖(Y0.map (X.B.I.φ v) - P v) i j‖ ≤ C

def JBDenom : Prop :=
  ∀ (D : D7) (X : HidaSetting D), ∃ c : ℕ, 1 ≤ c ∧ ∃ B B' : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E),
    (c : X.B.I.E) • JB X = B.map (fun a => (a : X.B.I.E)) ∧ (c : X.B.I.E) • JB' X = B'.map (fun a => (a : X.B.I.E))

section SlopeTestRemainingChoices

variable {D : D7} (X : HidaSetting D)

theorem star_integral (a : 𝓞 X.B.I.E) : ∃ b : 𝓞 X.B.I.E, (b : X.B.I.E) = star (a : X.B.I.E) :=
  ⟨⟨star (a : X.B.I.E), (NumberField.RingOfIntegers.isIntegral_coe a).map
    (starRingEnd X.B.I.E).toIntAlgHom⟩, rfl⟩

theorem gr_mul (M : GL (Fin X.B.I.n) X.B.I.E) :
    Gr X (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *
      Gr X ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = 1 := by
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E := (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) with hMm
  set Mi : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
    ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) with hMi
  have hMMi : Mm * Mi = 1 := by rw [hMm, hMi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  unfold Gr
  have e : Bm' X * Mm * Bm X * (Bm' X * Mi * Bm X) = Bm' X * (Mm * (Bm X * Bm' X) * Mi) * Bm X := by
    simp only [Matrix.mul_assoc]
  rw [e, Bm_mul_Bm', Matrix.mul_one, hMMi, Matrix.mul_one, Bm'_mul_Bm]

theorem gr_unitary (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    (Gr X (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E))ᴴ * JB X *
      Gr X (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = JB X := by
  set Mm : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E := (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) with hMm
  have hU : Mmᴴ * X.B.I.J * Mm = X.B.I.J := by
    have h : Formalism.UG.cT (starRingEnd X.B.I.E) Mm * X.B.I.J * Mm = X.B.I.J := hM
    have hc : Formalism.UG.cT (starRingEnd X.B.I.E) Mm = Mmᴴ := by
      ext i j; simp [Formalism.UG.cT, conjTranspose_apply, starRingEnd_apply]
    rwa [hc] at h
  have hB : (Bm' X)ᴴ * (Bm X)ᴴ = 1 := by
    rw [← conjTranspose_mul, Bm_mul_Bm', conjTranspose_one]
  unfold Gr
  rw [JB_eq, conjTranspose_mul, conjTranspose_mul]
  calc (Bm X)ᴴ * (Mmᴴ * (Bm' X)ᴴ) * ((Bm X)ᴴ * X.B.I.J * Bm X) * (Bm' X * Mm * Bm X)
      = (Bm X)ᴴ * Mmᴴ * ((Bm' X)ᴴ * (Bm X)ᴴ) * X.B.I.J * (Bm X * Bm' X) * Mm * Bm X := by
          simp only [Matrix.mul_assoc]
    _ = (Bm X)ᴴ * (Mmᴴ * X.B.I.J * Mm) * Bm X := by
          rw [hB, Bm_mul_Bm']; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = (Bm X)ᴴ * X.B.I.J * Bm X := by rw [hU]

end SlopeTestRemainingChoices

section Bounds

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_mul_entry_le (A B : Matrix ι ι ℂ) (a b : ℝ) (ha0 : 0 ≤ a)
    (ha : ∀ i j, ‖A i j‖ ≤ a) (hb : ∀ i j, ‖B i j‖ ≤ b) (i j : ι) :
    ‖(A * B) i j‖ ≤ Fintype.card ι * (a * b) := by
  rw [Matrix.mul_apply]
  calc ‖∑ x, A i x * B x j‖ ≤ ∑ x, ‖A i x * B x j‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ι, a * b := Finset.sum_le_sum fun x _ => by
        rw [norm_mul]; exact mul_le_mul (ha i x) (hb x j) (norm_nonneg _) ha0
    _ = Fintype.card ι * (a * b) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem norm_proj_entry_le [Invertible (2 : ℂ)] (J J' E' : Matrix ι ι ℂ) (a bJ bJ' : ℝ) (ha0 : 0 ≤ a)
    (hJ0 : 0 ≤ bJ) (hJ'0 : 0 ≤ bJ') (ha : ∀ i j, ‖E' i j‖ ≤ a) (hJ : ∀ i j, ‖J i j‖ ≤ bJ)
    (hJ' : ∀ i j, ‖J' i j‖ ≤ bJ') (i j : ι) :
    ‖proj J J' E' i j‖ ≤ a + Fintype.card ι * (Fintype.card ι * (bJ' * a) * bJ) := by
  have hs : ∀ i j, ‖E'ᴴ i j‖ ≤ a := fun i j => by rw [conjTranspose_apply, norm_star]; exact ha j i
  have h1 := norm_mul_entry_le J' E'ᴴ bJ' a hJ'0 hJ' hs
  have hn : 0 ≤ Fintype.card ι * (bJ' * a) := by positivity
  have h2 := norm_mul_entry_le (J' * E'ᴴ) J _ bJ hn h1 hJ i j
  have h2' : ‖(⅟2 : ℂ)‖ = 1 / 2 := by rw [invOf_eq_inv]; simp
  unfold proj Formalism.L2.SG.Pf.Unip.sharp
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, h2', Matrix.sub_apply]
  have h3 := norm_sub_le (E' i j) ((J' * E'ᴴ * J) i j)
  have h4 := ha i j
  have h5 : 0 ≤ Fintype.card ι * (Fintype.card ι * (bJ' * a) * bJ) := by positivity
  nlinarith [norm_nonneg (E' i j - (J' * E'ᴴ * J) i j)]

end Bounds

section Proj

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [StarRing K] [Invertible (2 : K)]

theorem proj_sub' (J J' A B : Matrix ι ι K) : proj J J' A - proj J J' B = proj J J' (A - B) := by
  unfold proj Formalism.L2.SG.Pf.Unip.sharp
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul, ← smul_sub]
  congr 1
  abel

end Proj

theorem map_proj {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) [Invertible (2 : X.B.I.E)]
    [Invertible (2 : ℂ)] (J J' A : Matrix (Kap X) (Kap X) X.B.I.E) :
    (proj J J' A).map (X.B.I.φ v) = proj (J.map (X.B.I.φ v)) (J'.map (X.B.I.φ v)) (A.map (X.B.I.φ v)) := by
  have h2 : X.B.I.φ v (⅟2 : X.B.I.E) = (⅟2 : ℂ) := by
    rw [invOf_eq_inv, invOf_eq_inv, map_inv₀, map_ofNat]
  unfold proj Formalism.L2.SG.Pf.Unip.sharp
  rw [Matrix.map_smul' _ _ _ (fun a b => map_mul _ a b), h2, Matrix.map_sub _ (fun a b => map_sub _ a b), Matrix.map_mul, Matrix.map_mul,
    map_conjTranspose X v]

theorem ratApprox_of (hS : RatSolApprox) (hD : JBDenom) : RatApprox := by
  intro D X M hM k hk d hd
  let _ : Invertible (2 : X.B.I.E) := invertibleOfNonzero two_ne_zero
  let _ : Invertible (2 : ℂ) := invertibleOfNonzero two_ne_zero
  obtain ⟨c, hc, B, B', hB, hB'⟩ := hD D X
  have hN : 1 ≤ 2 * d * (c * c) := by
    have := Nat.mul_pos (Nat.mul_pos two_pos hd) (Nat.mul_pos hc hc); omega
  obtain ⟨C1, hC1⟩ := hS D X (Gr X (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E))
    (Gr X ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)) k (2 * d * (c * c)) hN
  have hJ0 : 0 ≤ ∑ v, ∑ i, ∑ j, ‖JBv X v i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hJ'0 : 0 ≤ ∑ v, ∑ i, ∑ j, ‖JBv' X v i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hJb : ∀ v i j, ‖JBv X v i j‖ ≤ ∑ v, ∑ i, ∑ j, ‖JBv X v i j‖ := fun v i j => by
    calc ‖JBv X v i j‖ ≤ ∑ j', ‖JBv X v i j'‖ :=
          Finset.single_le_sum (f := fun j' => ‖JBv X v i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖JBv X v i' j'‖ :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖JBv X v i' j'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ i)
      _ ≤ ∑ v, ∑ i, ∑ j, ‖JBv X v i j‖ := Finset.single_le_sum (f := fun v' => ∑ i', ∑ j', ‖JBv X v' i' j'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ v)
  have hJ'b : ∀ v i j, ‖JBv' X v i j‖ ≤ ∑ v, ∑ i, ∑ j, ‖JBv' X v i j‖ := fun v i j => by
    calc ‖JBv' X v i j‖ ≤ ∑ j', ‖JBv' X v i j'‖ :=
          Finset.single_le_sum (f := fun j' => ‖JBv' X v i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖JBv' X v i' j'‖ :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖JBv' X v i' j'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ i)
      _ ≤ ∑ v, ∑ i, ∑ j, ‖JBv' X v i j‖ := Finset.single_le_sum (f := fun v' => ∑ i', ∑ j', ‖JBv' X v' i' j'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
            (Finset.mem_univ v)
  generalize hbJ : (∑ v, ∑ i, ∑ j, ‖JBv X v i j‖) = bJ at hJ0 hJb
  generalize hbJ' : (∑ v, ∑ i, ∑ j, ‖JBv' X v i j‖) = bJ' at hJ'0 hJ'b
  generalize ha : max C1 0 = a
  have ha0 : 0 ≤ a := ha ▸ le_max_right _ _
  have haC : C1 ≤ a := ha ▸ le_max_left _ _
  refine ⟨a + Fintype.card (Kap X) * (Fintype.card (Kap X) * (bJ' * a) * bJ), fun P hP => ?_⟩
  obtain ⟨Y0, hk0, h10, ⟨A, hA⟩, hC⟩ := hC1 P (fun v => ⟨(hP v).1, (hP v).2.1⟩)
  refine ⟨proj (JB X) (JB' X) Y0, inPat_proj (JB_graded X) (JB'_graded X) hk0, ?_,
    proj_skew (JB_herm X) (JB'_herm X) (JB'_mul_JB X) (JB_mul_JB' X) Y0, ?_, ?_⟩
  · rw [conj_proj (JB_herm X) (JB'_herm X) (JB'_mul_JB X) (JB_mul_JB' X) (gr_unitary X M hM) (gr_mul X M)]
    exact inPat_proj (JB_graded X) (JB'_graded X) h10
  · choose s hs using fun i j => star_integral X (A j i)
    set As : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => s i j with hAsd
    set Am := A.map (fun a => (a : X.B.I.E)) with hAm
    set Asm := As.map (fun a => (a : X.B.I.E)) with hAsm
    set Bm_ := B.map (fun a => (a : X.B.I.E)) with hBm
    set B'm := B'.map (fun a => (a : X.B.I.E)) with hB'm
    have hAs : Amᴴ = Asm := by
      ext i j; simp [Am, Asm, As, hs, conjTranspose_apply]
    have e1 : JB' X * Y0ᴴ * JB X = ((2 * d : ℕ) : X.B.I.E) • (B'm * Asm * Bm_) := by
      rw [hA, conjTranspose_smul, star_natCast, Matrix.mul_smul, Matrix.smul_mul, hAs, ← hB, ← hB',
        Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
      congr 1
      push_cast; ring
    refine ⟨(c * c) • A - B' * As * B, ?_⟩
    have e2 : ((c * c) • A - B' * As * B).map (fun a => (a : X.B.I.E)) =
        ((c * c : ℕ) : X.B.I.E) • Am - B'm * Asm * Bm_ := by
      have h := (algebraMap (𝓞 X.B.I.E) X.B.I.E).mapMatrix.map_sub ((c * c) • A) (B' * As * B)
      rw [map_nsmul, map_mul, map_mul] at h
      simp only [RingHom.mapMatrix_apply] at h
      rw [Nat.cast_smul_eq_nsmul]
      exact h
    rw [e2]
    unfold proj Formalism.L2.SG.Pf.Unip.sharp
    rw [e1, hA]
    have e3 : ((2 * d * (c * c) : ℕ) : X.B.I.E) • Am - ((2 * d : ℕ) : X.B.I.E) • (B'm * Asm * Bm_) =
        (2 : X.B.I.E) • ((d : X.B.I.E) • (((c * c : ℕ) : X.B.I.E) • Am - B'm * Asm * Bm_)) := by
      push_cast
      module
    rw [e3, smul_smul, invOf_mul_self, one_smul]
  · intro v i j
    have hskew := proj_of_skew (JBv'_mul X v) (hP v).2.2
    rw [map_proj X v, show (JB X).map (X.B.I.φ v) = JBv X v from rfl,
      show (JB' X).map (X.B.I.φ v) = JBv' X v from rfl, ← hskew, proj_sub']
    exact norm_proj_entry_le (JBv X v) (JBv' X v) _ a bJ bJ' ha0 hJ0 hJ'0
      (fun i j => (hC v i j).trans haC) (hJb v) (hJ'b v) i j

theorem exists_common_den {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] (f : ι → E) :
    ∃ c : ℕ, 1 ≤ c ∧ ∀ i, IsIntegral ℤ ((c : E) * f i) := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  have hpos : 0 < y * y := mul_self_pos.2 hy0
  refine ⟨(y * y).toNat, by omega, fun i => ?_⟩
  have hc : (((y * y).toNat : ℕ) : E) = ((y : ℤ) : E) * ((y : ℤ) : E) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hpos.le, Int.cast_mul]
  have hi : IsIntegral ℤ (y • f i) := hy _ (Finset.mem_image_of_mem f (Finset.mem_univ i))
  rw [hc]
  have hi' : IsIntegral ℤ (((y : ℤ) : E) * f i) := by simpa [zsmul_eq_mul] using hi
  have h2 : IsIntegral ℤ (algebraMap ℤ E y * (((y : ℤ) : E) * f i)) := isIntegral_algebraMap.mul hi'
  simpa [mul_assoc] using h2

theorem jbDenom_holds : JBDenom := by
  intro D X
  obtain ⟨c, hc, h⟩ := exists_common_den (E := X.B.I.E)
    (fun p : (Kap X × Kap X) ⊕ (Kap X × Kap X) => Sum.elim (fun q => JB X q.1 q.2) (fun q => JB' X q.1 q.2) p)
  refine ⟨c, hc, Matrix.of fun i j => ⟨(c : X.B.I.E) * JB X i j, h (Sum.inl (i, j))⟩,
    Matrix.of fun i j => ⟨(c : X.B.I.E) * JB' X i j, h (Sum.inr (i, j))⟩, ?_, ?_⟩
  · ext i j; simp [smul_eq_mul]; rfl
  · ext i j; simp [smul_eq_mul]; rfl

theorem ratApprox_of_sol (hS : RatSolApprox) : RatApprox := ratApprox_of hS jbDenom_holds

end Formalism.L2.SG.TermOp.Vanish
end
end

