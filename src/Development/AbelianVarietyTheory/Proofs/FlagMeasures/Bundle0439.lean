module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowDoubleCosetSumNormSqBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalCoordinatesRationalFlagPair
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubleCosetEqIffIsometryUnipotentTranslate
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0437
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsAtPointOfRelevantTermRelevantFinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0061
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0361
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTwoSidedMomentsLargeGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0259
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedMeasureEqProdBesselRootMeasures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsQuotientMeasureUnipotentStabilisers
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBruhatFunctionLocalBesselIntegralEqL2Mass
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc

noncomputable section

namespace GlobalTheory.SlocTie

def rmulE {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hab : a * b = 1) (hba : b * a = 1) :
    Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun x := Matrix.of.symm (Matrix.of x * a)
  invFun x := Matrix.of.symm (Matrix.of x * b)
  left_inv x := by
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of x * a)) * b) = x
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, hab, Matrix.mul_one]; rfl
  right_inv x := by
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (Matrix.of x * b)) * a) = x
    rw [Equiv.apply_symm_apply, Matrix.mul_assoc, hba, Matrix.mul_one]; rfl
  measurable_toFun := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun x : Formalism.QuantumDeterminants.Mt k r => ∑ l, x i l * _
    fun_prop
  measurable_invFun := by
    apply Continuous.measurable
    refine continuous_pi fun i => continuous_pi fun j => ?_
    show Continuous fun x : Formalism.QuantumDeterminants.Mt k r => ∑ l, x i l * _
    fun_prop

theorem quot_rmul {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hab : a * b = 1)
    (hba : b * a = 1) {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : μG.map (rmulE a b hab hba) = μG)
    (hq : IsQuotMeas μG μS ν) : IsQuotMeas μG μS (ν.map (rmulE a b hab hba)) := by
  intro f hf
  set R := rmulE a b hab hba
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, f x ∂(μG.map R) := by rw [hG]
    _ = ∫⁻ x, f (R x) ∂μG := MeasureTheory.lintegral_map_equiv _ R
    _ = ∫⁻ x, (∫⁻ s, f (R (fun i j => (Matrix.of s * Matrix.of x) i j)) ∂μS) ∂ν := hq _ (hf.comp R.measurable)
    _ = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (R x)) i j) ∂μS) ∂ν := by
        refine lintegral_congr fun x => lintegral_congr fun s => ?_
        congr 1
        show Matrix.of.symm (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j) * a) =
          fun i j => (Matrix.of s * Matrix.of (Matrix.of.symm (Matrix.of x * a))) i j
        rw [Equiv.apply_symm_apply]
        funext i j
        show (Matrix.of s * Matrix.of x * a) i j = (Matrix.of s * (Matrix.of x * a)) i j
        rw [Matrix.mul_assoc]
    _ = ∫⁻ x, (∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂(ν.map R) :=
        (MeasureTheory.lintegral_map_equiv (fun x => ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) R).symm

end GlobalTheory.SlocTie

namespace GlobalTheory.SlocTie

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def yInv (C : Choice X θ) (τ : D.what₂.Tau) : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
  Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS

theorem y_inv (C : Choice X θ) (τ : D.what₂.Tau) : C.y τ * yInv C τ = 1 ∧ yInv C τ * C.y τ = 1 := by
  obtain ⟨-, hi⟩ := Formalism.MainNotions.S.Inh.unitary_group_inv_mem (C.y τ) (C.y_mem τ)
  exact ⟨(Matrix.mul_eq_one_comm_of_card_eq (Fin _) (Fin _) ℂ rfl).mp hi, hi⟩

def Ry (C : Choice X θ) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS ≃ᵐ Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  rmulE (C.y τ) (yInv C τ) (y_inv C τ).1 (y_inv C τ).2

theorem muGB_rinv (C : Choice X θ) (τ : D.what₂.Tau) :
    (muGB X (C.Q τ) (C.Qi τ) τ).map (Ry C τ) = muGB X (C.Q τ) (C.Qi τ) τ := by
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy' : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hJ : (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by
    calc (C.Q τ * C.y τ * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.y τ * C.Qi τ)
        = (C.Qi τ)ᴴ * ((C.y τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.y τ) * C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by rw [hg, hy', Formalism.L2.SG.Pf.Choice.qiHqi _ h2 hg]
  set γy := Formalism.L2.SG.Pf.GoodS.toUJn (C.Q τ * C.y τ * C.Qi τ) hJ
  haveI : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular _ _ g⟩
  have he := eT_emb C τ (vOf X τ)
  have hcomm : (Ry C τ) ∘ eT C τ (vOf X τ) = eT C τ (vOf X τ) ∘ (fun γ => γ * γy) := by
    funext γ
    show Matrix.of.symm (Matrix.of (Matrix.of.symm (C.Qi τ * uMat γ * C.Q τ)) * C.y τ) =
      Matrix.of.symm (C.Qi τ * uMat (γ * γy) * C.Q τ)
    rw [Equiv.apply_symm_apply, show uMat (γ * γy) = uMat γ * uMat γy from rfl,
      show uMat γy = C.Q τ * C.y τ * C.Qi τ from rfl]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_one]
  show ((Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (eT C τ (vOf X τ))).map (Ry C τ) =
    (Formalism.REAL.muG (X.B.I.ε (vOf X τ))).map (eT C τ (vOf X τ))
  rw [Measure.map_map (Ry C τ).measurable he.measurable, hcomm,
    ← Measure.map_map he.measurable (measurable_mul_const γy), map_mul_right_eq_self]

def shiftC (C : Choice X θ) : Choice X θ :=
  { C with
    nuS := fun u τ => (C.nuS u τ).map (Ry C τ)
    nuS_q := fun u τ => quot_rmul _ _ _ _ (muGB_rinv C τ) (C.nuS_q u τ) }

theorem loc_main (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u : D.what₂.Word)
    (τ : D.what₂.Tau) :
    ∃ β : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ (vOf X τ)) (muHl C u τ (vOf X τ))) = 1) ∧
      ∫⁻ y, β y * ‖X.Wloc u (vOf X τ) y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε (vOf X τ))) =
        l2SG (C.nuS u τ) (phiOf hB u τ) := by
  obtain ⟨β, hβm, hβ1⟩ := bruhat_mulMap C u τ
  refine ⟨β, hβm, hβ1, ?_⟩
  have hid := loc_id (shiftC C) u τ hβm hβ1
  rw [hid]
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  have hconc := Formalism.L2.SG.Pf.GoodS.nu_conc hz hT (Formalism.L2.SG.Pf.haarTr C τ) (Formalism.L2.SG.Pf.LocF.muS_haar C u τ)
    (C.nuS_q u τ)
  have hae : ∀ᵐ x ∂(C.nuS u τ), Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact hconc
  show ∫⁻ x, (‖wT C u τ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂((C.nuS u τ).map (Ry C τ)) =
    ∫⁻ x, (‖phiOf hB u τ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂(C.nuS u τ)
  rw [MeasureTheory.lintegral_map_equiv]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [Formalism.L2.SG.Pf.GoodS.phi_eq C hB u τ _ hx]
  rfl

end GlobalTheory.SlocTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGroupSumFactorsRowWeightAmplitudeProof
section
noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG GlobalTheory.HL GlobalTheory.LocOver GlobalTheory.SnFam

namespace GlobalTheory.FamilyNormRational

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toPts_inj' {K : Type} [Zero K] {i : ℕ} (p q : Point K (i + 1)) (h : toPts p = toPts q) : p = q := by
  have hb : p.1.map Prod.snd = q.1.map Prod.snd := congrArg (fun x => x.1.blocks) h
  have hl : p.1.length = q.1.length := by simpa using congrArg List.length hb
  have hv : ∀ k (hk : k < p.1.length) (hk' : k < q.1.length), (p.1[k]).1 = (q.1[k]).1 := by
    intro k hk hk'
    have key := congrArg (fun x : (Σ c : Composition (i + 1), (Fin c.length → K)) =>
      if hk : k < x.1.length then x.2 ⟨k, hk⟩ else 0) h
    have e1 : k < (toPts p).1.length := by simpa [toPts, Composition.length] using hk
    have e2 : k < (toPts q).1.length := by simpa [toPts, Composition.length] using hk'
    simp only [dif_pos e1, dif_pos e2] at key
    simpa [toPts] using key
  apply Subtype.ext
  apply List.ext_getElem hl
  intro k hk hk'
  have hs := congrArg (fun l => l[k]?) hb
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Option.map_some,
    Option.some.injEq] at hs
  exact Prod.ext (hv k hk hk') hs

theorem one_mem_nRat {D : D7} {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ NRat F :=
  ⟨one_mem _, fun j x _ => by simp, fun x _ => by simp⟩

theorem squaredGroupSum_classDoubleCoset_eq_rowWeight : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k →
    ConcTie X Y → ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ s : X.B.I.Ginf → NNReal, (∀ γ, 0 < s γ) →
    (∀ w : Point D.host.E (D.R.rS + 1), (∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w g) →
      (s (Formalism.L2.SG.RealObj.gamW X u u' w) : ℝ) = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹)) →
    ∀ (K : Type) (S : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → K), FamQ Y u u' S TS cls →
    ∀ γ : PN.Pts D.host.E D.R.rS, HasPt Y u u' TS γ →
    ∀ Fm : LocFam (zOf Y) K (NuC D), FamTie TS cls (nmlOf Y u u') γ Fm →
    ∀ (c : K) (n : NuC D), a2F Y u u' TS cls (sc s ν) c γ n = a2W Fm.toL (ampQ S Fm.toL) c n := by
  intro D X Y u u' hSt hk hCT ν hνP s hs0 hsw K S TS cls hFQ γ hγ Fm hFT c n
  obtain ⟨w, F00, F'0, F'1, hw, -, -, -, hZ, hbase, hOm, hgood, -, -, -, -, hdat, -, -⟩ := hFT
  have hdc := hdat c n
  have hL : Fm.toL.dat c n = Fm.dat c n := rfl
  show ‖grpF Y u u' TS cls c γ n‖ ^ 2 / J2of Y u u' (sc s ν) γ = a2W Fm.toL (ampQ S Fm.toL) c n
  unfold a2W
  rw [hL]
  rcases hd : Fm.dat c n with _ | d
  · rw [hd] at hdc
    have h0 : grpF Y u u' TS cls c γ n = 0 := by
      unfold grpF
      have h0 : ∀ t, (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = n}).indicator (Y.tO u u').vec t = 0 := by
        intro t; apply Set.indicator_of_notMem; rintro ⟨h1, h2, h3, h4⟩; exact hdc ⟨t, h1, h2, h3, h4⟩
      simp [h0]
    simp [h0]
  · rw [hd] at hdc
    obtain ⟨⟨t0, ht0, hc0, hp0, hn0⟩, hall⟩ := hdc
    obtain ⟨hOv, hrw⟩ := hall t0 ht0 hc0 hp0 hn0
    obtain ⟨hTS, hCR, hRow⟩ := hFQ
    obtain ⟨t1, ht1, hv1, hp1⟩ := hγ
    have hGTS : ∀ t ∈ TS, t.G ≠ 0 := by
      intro t ht h0
      rw [hTS] at ht
      apply ht.1
      show Formalism.L2.SG.TermOp.Gt t = 0
      unfold Formalism.L2.SG.TermOp.Gt
      rw [if_pos h0]
    have hG1 := hGTS t1 ht1
    have hG0 := hGTS t0 ht0
    have hrel1 : t1.relevant := (_root_.GlobalTheory.NGClass.ngClass_rows D X Y u u' hCT).2.2 t1 hv1
    obtain ⟨w1, hw1, hat1, -⟩ := _root_.GlobalTheory.LocOver.terms_at_point_of_relevant D X Y u u' t1 hG1 hrel1
    have hw1w : w1 = w := toPts_inj' _ _ (hw1.trans (hp1.trans hw.symm))
    subst hw1w
    have hatOf : ∀ t : TauC Y u u', ptPN t = γ → t.relevant ∧ t.toTerm.atPt w1 ∧ Formalism.L2.SG.PairVal.ptOf t.toTerm = w1 := by
      intro t ht
      obtain ⟨hr, hg, hcell⟩ := hat1 t (ht.trans hp1.symm)
      refine ⟨hr, ⟨(Quot.out t.toTerm.cls).1, ⟨(Quot.out t.toTerm.cls).2, Quot.out_eq _⟩, hg, hcell⟩, ?_⟩
      exact toPts_inj' _ _ (ht.trans hw.symm)
    obtain ⟨hrel0, hat0, hpt0⟩ := hatOf t0 hp0
    obtain ⟨-, hat1', hpt1⟩ := hatOf t1 hp1
    have hAtB : ∀ p, AtBase (zOf Y) p F00 F'0 (Tu D u) (Tu D u') (Fm.FP p) := fun p =>
      ⟨(hbase p).1, (hbase p).2.1, (hbase p).2.2.1, (hbase p).2.2.2⟩
    have hGv : Gval F00 F'0 ≠ 0 := by
      obtain ⟨-, hg0, hcell0⟩ := hat1 t0 (hp0.trans hp1.symm)
      have hcell00 : IsInCell (ZhatOM (ZhatL F00 F'0)) w1 :=
        ⟨1, 1, fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_lt h), fun h => h ▸ Matrix.one_apply_eq i⟩,
          fun i j => ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => h ▸ Matrix.one_apply_eq i⟩,
          by rw [hZ, Matrix.one_mul, Matrix.mul_one]⟩
      have e1 := Formalism.L2.SG.WConst.gPoint_eq_gval F00 F'0 w1 hcell00
      have e2 := Formalism.L2.SG.WConst.gPoint_eq_gval (T := Tu D u) (T' := Tu D u') (lf D (X.Fu u)) (Quot.out t0.toTerm.cls).1
        w1 hcell0
      change Gpt (D.mem u).A.T (D.mem u').A.T w1 = _ at e2
      rw [← e1, e2]
      exact hg0
    have hBase : ∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (Fm.FP p) ∧
        (Fm.FP p).RelG (LocNG.theta (Y.M p)) := fun p =>
      ⟨hAtB p, (_root_.GlobalTheory.LocBaseRel.atBase_relG D (zOf Y) u u' w1 F00 F'0 hZ hGv p).2 _ (hAtB p)⟩
    obtain ⟨G, ⟨cc⟩⟩ := _root_.GlobalTheory.HL.GCoordEx.exists_global_coords D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase
    obtain ⟨ρ, U, U', hmv⟩ := _root_.GlobalTheory.HL.MoveTerm.term_moves_to_base D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase t0 hat0
    have hcore := _root_.GlobalTheory.HL.RowCoset.row_coset_sum_norm_sq D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc ν hνP t0 ρ U U' hmv hrel0 hpt0 S
    have hamp := GlobalTheory.T.globalAmplitude_eq_localAmplitudes D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc t0 ρ U U' hmv Fm.R Fm.P Fm.Om
      (fun p => (d p).1) hgood hOm (fun p => hOv p.1 p.2) S
    have hset : (TS ∩ {t | cls t = c ∧ ptPN t = γ ∧ nmlOf Y u u' t = n}) =
        {t : TauC Y u u' | (Y.tO u u').rowOf t = (Y.tO u u').rowOf t0 ∧ nmlOf Y u u' t = nmlOf Y u u' t0 ∧
          S (¬ t.generic)} := by
      ext t
      constructor
      · rintro ⟨htS, hct, -, hnt⟩
        refine ⟨hRow t htS t0 ht0 (hct.trans hc0.symm), hnt.trans hn0.symm, ?_⟩
        have h2 := htS
        rw [hTS] at h2
        exact h2.2
      · rintro ⟨hr, hnm, hS⟩
        obtain ⟨nn, mm, hnn, hmm, hlin⟩ := (_root_.GlobalTheory.HL.nmlOf_eq_iff_lin D X Y u u' hSt t0 t).1 hnm
        obtain ⟨-, hGeq, hpteq, -, -⟩ := _root_.GlobalTheory.HL.CosetConst.coset_const D X Y u u' hSt t0 t nn mm hrel0 hG0 ⟨hnn, hmm, hlin⟩
        have htS : t ∈ TS := by
          rw [hTS]
          refine ⟨?_, hS⟩
          show Formalism.L2.SG.TermOp.Gt t ≠ 0
          unfold Formalism.L2.SG.TermOp.Gt
          rw [if_neg (hGeq ▸ hG0)]
          exact one_ne_zero
        refine ⟨htS, ((hCR t htS t0 ht0 hnm).2 hr).trans hc0, ?_, hnm.trans hn0⟩
        show toPts (Formalism.L2.SG.PairVal.ptOf t.toTerm) = γ
        rw [hpteq]
        exact hp0
    have hrep : ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w1 g :=
      (GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hSt ν hνP t0 hrel0 hG0 w1 hpt0.symm).1
    have hJ : J2of Y u u' (sc s ν) γ = (s (Formalism.L2.SG.RealObj.gamW X u u' w1) : ℝ) ^ 2 *
        ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ ^ 2 := by
      unfold J2of
      have hex : ∃ w' : Point D.host.E (D.R.rS + 1), toPts w' = γ ∧ ∃ g, Formalism.L2.SG.RealObj.IsPtRep X u u' w' g :=
        ⟨w1, hw, hrep⟩
      rw [dif_pos hex]
      have hcw : hex.choose = w1 := toPts_inj' _ _ (hex.choose_spec.1.trans hw.symm)
      rw [hcw, Jw_sc, map_smul, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hJne : ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ ≠ 0 := by
      intro h0
      obtain ⟨ρ1, U1, U1', hmv1⟩ := _root_.GlobalTheory.HL.MoveTerm.term_moves_to_base D X Y u u' hSt w1 F00 F'0 Fm.FP hZ hGv hBase t1 hat1'
      obtain ⟨T, hT, hamp1⟩ := _root_.GlobalTheory.AmpTerm.amp_eq_mass_phase D X Y u u' hSt hk w1 F00 F'0 Fm.FP hZ hGv hBase G cc ν hνP t1 ρ1 U1 U1'
        hmv1 hrel1 hpt1
      have he := hamp1 t1 1 1 rfl ⟨one_mem_nRat _, one_mem_nRat _, by simp⟩
      have hT0 : Formalism.L2.SG.PackageTie.hsEmb T = 0 := norm_eq_zero.1 (hT.trans h0)
      apply hv1
      show Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t1 = 0
      unfold Formalism.L2.SG.TermOp.vec
      rw [he, map_smul, hT0, smul_zero, smul_zero]
      ext q
      simp
    have hgi := hsw w1 hrep
    have hspos : (0 : ℝ) < s (Formalism.L2.SG.RealObj.gamW X u u' w1) := by exact_mod_cast hs0 _
    have hampeq : ‖G.amp (G.datOf (cc.lat ρ t0.lam)) (fun Γ => S (¬ G.Gen (G.datOf (cc.lat ρ t0.lam)) Γ))‖ =
        ‖ampQ S Fm.toL d‖ := by
      rw [hamp]; unfold ampQ
      congr 1
      refine Finset.sum_congr rfl (fun A _ => Finset.prod_congr rfl (fun p _ => ?_))
      split_ifs <;> first | rfl | (exfalso; tauto)
    have hgrp : grpF Y u u' TS cls c γ n = ∑' t : TauC Y u u', {t : TauC Y u u' | (Y.tO u u').rowOf t =
        (Y.tO u u').rowOf t0 ∧ nmlOf Y u u' t = nmlOf Y u u' t0 ∧ S (¬ t.generic)}.indicator (Y.tO u u').vec t := by
      unfold grpF; rw [hset]
    rw [hgrp, hcore, hJ, hampeq]
    show _ = Fm.rw c * ‖ampQ S Fm.toL d‖ ^ 2
    rw [hrw, ← hgi]
    have hJp : 0 < ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w1)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hJne)
    field_simp

theorem familyGroupSumFactorsRowWeightAmplitude : GlobalTheory.SnFam.FamilyGroupSumFactorsWeightAmplitude := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, le_rfl, 0, 0, fun C' Cl _ _ D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  have hk := four_rank_add_seven_le_k hc
  obtain ⟨-, hSt, hCT⟩ := hc
  obtain ⟨s, hs1, hs0, hsle, hsw⟩ := _root_.GlobalTheory.PinScale.scale_pin D X u u'
  refine ⟨s, hs1, hs0, fun γ => ?_, fun K S TS cls hFQ γ hγ Fm hFT c n =>
    squaredGroupSum_classDoubleCoset_eq_rowWeight D X Y u u' hSt hk hCT ν hν.2 s hs0 hsw K S TS cls hFQ γ hγ Fm hFT c n⟩
  have h1 : (s γ : ℝ) ≤ 1 := by exact_mod_cast hsle γ
  have h0 : (0 : ℝ) ≤ s γ := (s γ).2
  simp only [zero_mul, Real.rpow_zero]
  nlinarith

end GlobalTheory.FamilyNormRational
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDatCOfBesselOfW
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm

theorem locDatC_of_besselOfW (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) : LocDatC := by
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨GlobalTheory.DecTransport.decLow_main⟩
  intro D X hne hG hT
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hB : WuBessel C := Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG hBW
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ)
    (fun τ => Formalism.L2.SG.Pf.haarTr C τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)
  refine ⟨C, hB, Formalism.L2.SG.Pf.LocF.locFactor_holds hG C, fun u τ => ⟨?_, ?_⟩⟩
  · exact goodW_of C u u τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u τ)
      (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.haarTr C τ)
  · exact goodS_of _ u u τ (Formalism.L2.SG.Pf.goodSRest_all hG hT _ u u τ)

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataTailBoundClosedFormLargeGaps
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TypeAsm.TailTopGap

theorem tailP_of_gap : GlobalTheory.GapIn.Hyp → TailP := by
  intro hH Cg cb Cw cT CT C0 _ _
  obtain ⟨CH, hCH, hmom⟩ := _root_.GlobalTheory.TwoSidedMomentsGap.two_sided_moments_gap hH Cg cb Cw cT CT C0
  refine ⟨CH, hCH, fun C₁ => ⟨0, max 1000 (C₁ : ℝ), fun C' Cl _ hCl D large₂ _ hK hTr => ?_⟩⟩
  have hZ : HypZ D large₂ C' Cl Cg cb Cw cT CT C0 := hK.1
  have h1000 : (1000 : ℝ) ≤ Cl := le_trans (le_max_left _ _) hCl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -, -, hClm, -⟩ := hK.1.1

  have hC₁m : C₁ ≤ D.R.m := by
    have h : (C₁ : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) (le_trans hCl hClm)
    exact_mod_cast h
  have hrS : D.R.rS ≤ D.R.m := by
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  have hm1 : 1 ≤ D.R.m := le_trans (by norm_num) D.R.two_le_m
  have hq : C₁ * D.R.k * D.R.rS ≤ D.R.k * D.R.m ^ 3 := by
    have h2 : C₁ * D.R.rS ≤ D.R.m ^ 3 :=
      calc C₁ * D.R.rS ≤ D.R.m * D.R.m := Nat.mul_le_mul hC₁m hrS
        _ ≤ D.R.m * D.R.m * D.R.m := Nat.le_mul_of_pos_right _ (by omega)
        _ = D.R.m ^ 3 := by ring
    calc C₁ * D.R.k * D.R.rS = D.R.k * (C₁ * D.R.rS) := by ring
      _ ≤ D.R.k * D.R.m ^ 3 := Nat.mul_le_mul_left _ h2
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hH1 : 0 < large₂.sc.b ^ (CH * (D.R.m : ℝ)) := Real.rpow_pos_of_pos hb _

  have hTrpos : ∀ w, 0 < Tr D w := by
    intro w
    have hk : 0 ≤ Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) := (even_two_mul _).pow_nonneg _
    by_contra hneg
    push_neg at hneg
    have h0 : Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg hk
    linarith [hTr w]
  have hv0 : 0 < D.host.v := by linarith
  intro τ u W hW A hA

  have side : ∀ W' : LocW D.R.k D.R.rS, GoodW D τ u u 1 W' → ∀ A' : LocS W', GoodS D (lamD D τ) A' →
      TailBd W'.z W'.νS A'.Φ (C₁ * D.R.k * D.R.rS) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) := by
    intro W' hW' A' hA'
    obtain ⟨hM, hI⟩ := hmom D large₂ C' Cl h1000 hZ τ u W' hW' A' hA' _ hq
    obtain ⟨hzW, -, -, -, -, hG, hWH, -, hN, hQ, -, -, hcont, -, -⟩ :=
      (_root_.GlobalTheory.AmpSides.oneSide_of_good D τ u u 1 W' (lamD D τ) A' hv0 one_pos (hTrpos u) (hTrpos u) hW' hA').1
    have hnull : W'.νS {x | Matrix.of x ∉ GG D.R.k D.R.rS} = 0 := by
      have hf := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hWH hN
      exact ae_iff.mp (Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 hf.1 hf.2 hQ)
    exact _root_.GlobalTheory.Amp.TailTwo.tailBd_of_moments D.R.k D.R.rS W'.z W'.νS A'.Φ _ _ hzW hH1 hnull hcont hM hI

  exact ⟨side W hW A hA, _root_.GlobalTheory.TypeAsm.tailBd_primed_of_unprimed D τ u 1 (lamD D τ) _ _ side W hW A hA⟩

end GlobalTheory.TypeAsm.TailTopGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedLiftAmplitudeEqCovolumeMulLocal
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AmpLift.amp_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  intro D X Y θ C u u' s x hrel _hG _hat hpin hfund hinv
  obtain ⟨μl, hμeq, hHaar, hHR, hroot⟩ := _root_.GlobalTheory.Amp.PinRoot.pinned_root D X Y θ C u u' s x.1 x.2.1 hpin
  obtain ⟨hq, ν, hν⟩ := _root_.GlobalTheory.QuotExist.quot_exists D X u u' s.pt.1 μl hHaar
  choose νl hνl using hq
  refine ⟨μl, νl, hHaar, hνl, hroot, ?_⟩
  have hν' : IsQuotMeasS X.B.I x.2.1 ν := hμeq ▸ hν
  have hOO := Formalism.L2.SG.Pf.formAllC_holds D X Y u u' s x.2.1 ν x.2.2
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' s hrel) hHR hν' hfund.1 hfund.2
  have hprod := GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local D X u u' s.pt.1 μl νl ν hHaar hνl hν hinv
  unfold Formalism.L2.SG.TermOp.ampN
  rw [Formalism.L2.SG.LoopTerm.hsNormSq_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hOO,
    ← Complex.coe_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hprod]
  have hc : Complex.normSq (Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_pow]
  rw [hc, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring
end

