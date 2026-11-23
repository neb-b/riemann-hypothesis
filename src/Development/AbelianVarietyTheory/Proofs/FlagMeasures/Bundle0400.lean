module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0277
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0367
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0388

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticConstantGenericBoundOfNormalisedSteps
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

noncomputable section

open scoped Classical

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticCGP_of_steps : StepPinExists → StepTermVanishG → StepLocGenPinnedG → StepThmBGP →
    StepAnalyticCGP := by
  intro hE hV hL hB Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨e₀, f₀, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨v₀, w₀, hV2⟩ := hV Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, p₀, q₀, hB2⟩ := hB Cg cb Cw cT CT C0 hcb hcT A
  refine ⟨CB, CSt, hCB, hCSt, max a₀ (max e₀ (max v₀ p₀)), max b₀ (max f₀ (max w₀ q₀)),
    fun C' Cl h1 h2 D large₂ X Y u hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk => ?_⟩
  have ha1 : a₀ ≤ C' := le_trans (by simp) h1
  have ha2 : b₀ ≤ Cl := le_trans (by simp) h2
  have he1 : e₀ ≤ C' := le_trans (by simp) h1
  have he2 : f₀ ≤ Cl := le_trans (by simp) h2
  have hv1 : v₀ ≤ C' := le_trans (by simp) h1
  have hv2 : w₀ ≤ Cl := le_trans (by simp) h2
  have hp1 : p₀ ≤ C' := le_trans (by simp) h1
  have hp2 : q₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨ν, hν⟩ := hE2 C' Cl he1 he2 D large₂ X Y u u hc
  obtain ⟨s, ng, e1, hs1, hs0, hsb, he0, he3, hLoc, hGen⟩ :=
    hL2 C' Cl ha1 ha2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  exact ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    Formalism.L2.SG.NGAnalytic.nuQOK_sc u u s hs1 hs0 ν hν.1, hν.1, hb0, le_rfl, he0, he3,
    ampVanishG_sc Y u s hs0 ν (ampVanishG_of_term Y u ν (hV2 C' Cl hv1 hv2 D large₂ X Y u hc ν hν)), hLoc, hGen,
    measureInputG_sc Y u s ν _ hsb ng,
    hB2 C' Cl hp1 hp2 D large₂ X Y u hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν (sc s ν) ng⟩

end GlobalTheory.SnPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AnalyticGenericBoundOfChoiceStepPositive
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticGP_of (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hA : StepAnalyticCGP) : StepAnalyticGP := by
  intro Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨k₀, l₀, hB2⟩ := hB Cg cb Cw cT CT C0
  obtain ⟨m₀, n₀, hT2⟩ := hTi Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, CSt, h1, h2, a₀, b₀, hA2⟩ := hA1 A
  refine ⟨CB, CSt, h1, h2, max a₀ (max k₀ m₀), max b₀ (max l₀ n₀), fun C' Cl e1 e2 D large₂ X Y u hD hc => ?_⟩
  obtain ⟨hb, X0, ψ, hT⟩ := hT2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc
  obtain ⟨sd, C, Th, F0, what₂, vR, Q, i0, i0', νq, Irat, Ire, hBk⟩ :=
    hB2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u u hc hb X0 ψ hT
  have hBk' := massDataValid_unscale (kapU_pos D) hBk
  obtain ⟨νL, νB, ng, cSt, e, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ :=
    hA2 C' Cl (le_trans (by simp) e1) (le_trans (by simp) e2) D large₂ X Y u hD hc hb X0 ψ hT sd C Th
      F0 what₂ vR Q i0 i0' νq (Irat * kapU D) (Ire * kapU D) hBk'
  exact ⟨_, inferInstance, _, Irat * kapU D, Ire * kapU D, νL, νB, ng, cSt, e, hBk', a1, a2, a3, a4, a5, a6, a7,
    a8, a9, a10, a11⟩

end GlobalTheory.SnPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelTransportConjPlaceMatrices
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp.Transp

theorem besselModelTransportMatrix_mul_right {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    A0 X C w * (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)).submatrix (ci X) id = 1 := by
  have hu : IsUnit (X.B.I.P (vOf X (tauOf D w))).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _)
  have h1 : (X.B.I.P (vOf X (tauOf D w)))⁻¹ * X.B.I.P (vOf X (tauOf D w)) = 1 := Matrix.nonsing_inv_mul _ hu
  obtain ⟨hQ, -, -, -⟩ := C.isT (tauOf D w)
  rw [A0, ← submatrix_mul _ _ id (ci X) id (ci X).bijective]
  have : C.Qi (tauOf D w) * (X.B.I.P (vOf X (tauOf D w)))⁻¹ * (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (X.B.I.P _), h1, Matrix.one_mul, hQ]
  rw [this, submatrix_id_id]

theorem besselModelTransportMatrix_inv_eq_frame {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (w : InfinitePlace D.host.E) :
    (A0 X C w)⁻¹ = (X.B.I.P (vOf X (tauOf D w)) * C.Q (tauOf D w)).submatrix (ci X) id :=
  Matrix.inv_eq_right_inv (besselModelTransportMatrix_mul_right X C w)

theorem besselModelTransportMatrix_conj_realPoint {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (w : InfinitePlace D.host.E) :
    A0 X C w * ((X.B.I.P (vOf X (tauOf D w)) * uMat (s (vOf X (tauOf D w))) * (X.B.I.P (vOf X (tauOf D w)))⁻¹).submatrix (ci X) (ci X))
      * (A0 X C w)⁻¹ = Formalism.L2.SG.RealObj.trG (C.Q (tauOf D w)) (C.Qi (tauOf D w)) (s (vOf X (tauOf D w))) := by
  have hu : IsUnit (X.B.I.P (vOf X (tauOf D w))).det := (Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _)
  have h1 : (X.B.I.P (vOf X (tauOf D w)))⁻¹ * X.B.I.P (vOf X (tauOf D w)) = 1 := Matrix.nonsing_inv_mul _ hu
  rw [besselModelTransportMatrix_inv_eq_frame, A0, ← submatrix_mul _ _ id (ci X) (ci X) (ci X).bijective,
    ← submatrix_mul _ _ id (ci X) id (ci X).bijective, submatrix_id_id, Formalism.L2.SG.RealObj.trG]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ (X.B.I.P _) (uMat _ * _), h1, Matrix.one_mul,
    ← Matrix.mul_assoc (X.B.I.P _)⁻¹ (X.B.I.P _) (C.Q _), h1, Matrix.one_mul]

theorem transp : ∀ {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s : X.B.I.Ginf) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ τ, γ.map (embS D τ) = (X.B.I.P (vOf X τ) * uMat (s (vOf X τ)) * (X.B.I.P (vOf X τ))⁻¹).submatrix (ci X) (ci X)) → ∀ w : InfinitePlace D.host.E, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w) := by
  intro D X θ C s γ hγ w
  have key := besselModelTransportMatrix_conj_realPoint X C s w
  rw [← hγ] at key
  unfold Ac Gm cjw trX
  split_ifs with hd
  · rw [show w.embedding = embS D (tauOf D w) from hd, key]
    rfl
  · rw [ModelIso.embedding_of_not_direct w hd]
    have hg : γ.map (ComplexEmbedding.conjugate (embS D (tauOf D w))) = (γ.map (embS D (tauOf D w))).map (starRingEnd ℂ) := by
      ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
    have hinv : ((A0 X C w).map star)⁻¹ = ((A0 X C w)⁻¹).map (starRingEnd ℂ) := by
      apply Matrix.inv_eq_right_inv
      rw [show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← Matrix.map_mul, besselModelTransportMatrix_inv_eq_frame, besselModelTransportMatrix_mul_right,
        Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hg, hinv, show (A0 X C w).map star = (A0 X C w).map (starRingEnd ℂ) from rfl, ← Matrix.map_mul, ← Matrix.map_mul, key]
    ext i j
    simp

end GlobalTheory.CovDomGrp.Transp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolFormalDegreeEq
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory

theorem covol_formalDegree_eq : ∀ (D : D7) (X : HidaSetting D), X.B.I = Formalism.L2.SG.InstExistsPf.instOf D →
    Formalism.MainNotions.StandardLattice.VolTie D → cdScaleTie D → dsigTie D →
    (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
      Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ :=
  fun _D X h hVol hcd hT => Formalism.L2.SG.Pf.DstarVolPf.dstarVol_holds X h hVol hcd hT

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfCutBoundPositive
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem rowMainEqP_of_cut (hCh : PN.NGChain) (hMG : MeanAmpGen) (hc : GenCutP) : RowMainEqP := by
  intro Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨C1, C0n, Aexp, CB, CSt, Cgs, CTs, h1, h2, h3, h4, hA, C'₀, Cl₀, h⟩ := hc Cg cb Cw cT CT C0 A hcb hcT
  obtain ⟨Cn, hCn, hK⟩ := rowGenJoint_of hCh hMG C1 C0n Aexp CB CSt Cgs CTs h1 h2 h3 h4 hA
  refine ⟨Cn, hCn, C'₀, Cl₀, fun C' Cl a b D large₂ X Y u hTies hH hT ha => ?_⟩
  obtain ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, _, _, hG, hdd, hN, hF, hS, hIn⟩ :=
    h C' Cl a b D large₂ X Y u hTies hH hT
  have hcard := Formalism.MainNotions.LatticeGluingRadicals.d_card D
  have key := hK D.host.E (TauC Y u u) _ _ _ _ (Y.tO u u) D.R.rS D.R.k (Set (TauC Y u u)) (NuC D)
    (NOfG Y u νL νB ng) P B large₂.sc.b (2 * D.host.v) (X.B.g : ℝ) (((Tu D u : ℕ) : ℝ) * ((Tu D u : ℕ) : ℝ))
    cSt e1 Irat Ire
  rw [hcard] at key
  have r := key ha hG hN hF hS hIn
  rw [hdd] at r
  exact r

end GlobalTheory.SnPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FullExistsOfLocTied
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory

theorem fullExists_of_locTied : ∀ (D : D7) (X : HidaSetting D), Formalism.L2.SG.Pf.LocCP.LocTied D → Nonempty (Formalism.L2.SG.Full.Full X) := by

  intro D X hT
  exact Formalism.L2.SG.Pf.fullExists_tied Formalism.L2.SG.Pf.trExistsC_holds Formalism.L2.SG.Pf.lattice_steps_hold
    Formalism.L2.SG.Closed.LocCTied_holds D X (Formalism.L2.SG.Closed.level_subgroup_is_group X) hT

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericHeightBoundOfLocalEstimates
section
noncomputable section

open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genCutP_of_steps (hS : StepSizes) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hH : StepHeightG) (hA : StepAnalyticGP) : GenCutP := by
  intro Cg cb Cw cT CT C0 A0 hcb hcT
  obtain ⟨C1, C0n, hA1⟩ := hA Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CB, CSt, hCB, hCSt, a₀, b₀, hA2⟩ := hA1 (C1 + C0n + 38)
  obtain ⟨Cgs, CTs, hCg, hCT, s₀, t₀, hS2⟩ := hS Cg cb Cw cT CT C0
  obtain ⟨n₀, m₀, hN2⟩ := hN Cg cb Cw cT CT C0
  obtain ⟨p₀, q₀, hP2⟩ := hP Cg cb Cw cT CT C0
  obtain ⟨h₀, j₀, hH2⟩ := hH Cg cb Cw cT CT C0
  refine ⟨C1, C0n, C1 + C0n + 38, CB, CSt, Cgs, CTs, hCB, hCSt, hCg, hCT, le_refl _,
    max a₀ (max s₀ (max n₀ (max p₀ h₀))), max b₀ (max t₀ (max m₀ (max q₀ j₀))),
    fun C' Cl h1 h2 D large₂ X Y u hTies hHy hT => ?_⟩
  have hc : Formalism.L2.SG.NGCut.Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u := ⟨hHy.1, hHy.2.1, hT⟩
  have e1' : a₀ ≤ C' := le_trans (le_max_left _ _) h1
  have e2' : b₀ ≤ Cl := le_trans (le_max_left _ _) h2
  have f1 : s₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h1
  have f2 : t₀ ≤ Cl := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h2
  have i1 : n₀ ≤ C' :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h1
  have i2 : m₀ ≤ Cl :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) h2
  have j1 : p₀ ≤ C' := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have j2 : q₀ ≤ Cl := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  have k1 : h₀ ≤ C' := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h1
  have k2 : j₀ ≤ Cl := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) h2
  obtain ⟨P, iP, B, Irat, Ire, νL, νB, ng, cSt, e1, hBk, hL, hBq, c1, c2, c3, c4, hV, hLoc, hGen, hMeas, hSum⟩ :=
    hA2 C' Cl e1' e2' D large₂ X Y u hTies hc
  obtain ⟨hG, hdd, hNI, hFI⟩ := hBk
  refine ⟨P, iP, B, cSt, e1, Irat, Ire, νL, νB, ng, hL, hBq, hG, hdd, hNI, hFI,
    Formalism.L2.SG.NGCut.ngSizes_of (hS2 C' Cl f1 f2 D large₂ X Y u u hc) c1 c2 c3 c4, ?_⟩
  exact ⟨classInputG_of Y u (hC D X Y u (g_ge_three hc) hT) νL νB ng, ampInputG_of_vanish Y u νL νB ng hV,
    hN2 C' Cl i1 i2 D large₂ X Y u hc νL νB ng, hP2 C' Cl j1 j2 D large₂ X Y u hc νL νB ng, hLoc, hMeas, hGen,
    hH2 C' Cl k1 k2 D large₂ X Y u hc νL νB ng, hSum⟩

end GlobalTheory.SnPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesLocalDataUnimodular
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueDat

variable {D : D7}

private theorem infinite_finPlaces (K : Type) [Field K] [NumberField K] :
    Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      la.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)


private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg (Z : LocDat D) (Λ : LV D) (h : Submodule.IsLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG := by
  obtain ⟨S, hS, hspan⟩ := Submodule.fg_def.mp (LatLoc.isLattice_map (LatLoc.cE D) Λ h).fg
  change Submodule.span (𝓞 D.host.E) S = LatLoc.cL Λ at hspan
  have hfg : ((GlobalTheory.HL.placesOf Z).lat p (LatLoc.cL Λ)).FG := by
    rw [← hspan, GlobalTheory.HL.PlacesRec.lat_span]
    exact Submodule.fg_span (hS.image _)
  rw [LatLoc.localLattice_eq]
  exact hfg

theorem orbit (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) {Tn T'n : ℕ}
    (F G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p)))
    (hG : Tri D.host.E (frame F) (frame G)) (hG' : Tri D.host.E (frame F') (frame G')) (p : PlF D) :
    (∃ n ∈ (FP p).A.N, scaled Z p (frame G) = fun b => n ((FP p).A.f b)) ∧
    (∃ n ∈ (FP p).B.N, scaled Z p (frame G') = fun b => n ((FP p).B.f b)) := by
  obtain ⟨A, hA, hAc⟩ := hG
  obtain ⟨A', hA', hAc'⟩ := hG'
  obtain ⟨Ap, hAp, -⟩ := _root_.GlobalTheory.LocOver.tri_scaled D Z _ _ A hA hAc
  obtain ⟨Ap', hAp', -⟩ := _root_.GlobalTheory.LocOver.tri_scaled D Z _ _ A' hA' hAc'
  have hN := (hR p).2.2.2.2.2.2
  have hfA : (FP p).A.f = scaled Z p (frame F) := (hB p).1
  have hfB : (FP p).B.f = scaled Z p (frame F') := (hB p).2.1
  refine ⟨?_, ?_⟩
  · exact (_root_.GlobalTheory.LocOver.UnipOnto.unipotent_onto (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p).A hN.2.1).2.2 (scaled Z p (frame G))
      (by rw [hfA]; exact ⟨Ap p, (hAp p).1, (hAp p).2⟩)
  · exact (_root_.GlobalTheory.LocOver.UnipOnto.unipotent_onto (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p).B hN.2.2.2.1).2.2 (scaled Z p (frame G'))
      (by rw [hfB]; exact ⟨Ap' p, (hAp' p).1, (hAp' p).2⟩)

theorem mem_iff_of_img {α : Type*} {S S' : Set α} {f : α → α} (hf : Function.Injective f) (hS : f '' S = S')
    {a b : α} (hb : b = f a) : a ∈ S ↔ b ∈ S' := by
  subst hb; rw [← hS]; exact (hf.mem_set_image).symm

end GlobalTheory.GlueDat


open GlobalTheory.GlueDat in
theorem GlobalTheory.GlueDat.glued_data : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ Λ : LV D, (Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ ∃ y : Dat Z FP, Λ ∈ globSet G G' y) ∧ (∀ y y' : Dat Z FP, Λ ∈ globSet G G' y → Λ ∈ globSet G G' y' → y = y') ∧ (∀ y : Dat Z FP, Λ ∈ globSet G G' y → (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite) ∧ ∀ (y y' : Dat Z FP), ∀ h ∈ H0 F F', RMoves h y y' → (Λ ∈ globSet G G' y ↔ Formalism.HermitianLatticesTheory.gmap h Λ ∈ globSet G G' y') := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS Λ
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hR := hB.2.1
  have hO := fun p => orbit Z FP F G F' G' hB.1 hR hS.1 hS.2.1 p
  have hLM := fun p (L : Submodule (Z.M p).L.O (Vp D p)) =>
    GlobalTheory.T.generic_local_terms_selfDual_lattices (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)
      (scaled Z p (frame G)) (scaled Z p (frame G')) (hO p).1 (hO p).2 L
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.glued_unimodular_lattice_iff_local_completions D Z FP u u' G G' (_root_.GlobalTheory.GenMass.changed_frames_linInd D Z FP _ _ F G F' G' hB.1 hR hS.1 hS.2.1) Λ]
    constructor
    · rintro ⟨hL, hp⟩
      have : ∀ p, ∃ d, lattice₂ D Z.M p Λ ∈ locSet G G' p d := fun p =>
        (hLM p _).1.1 ⟨(hp p).1, localLattice_fg Z Λ hL p, (hp p).2.1, (hp p).2.2⟩
      choose y hy using this
      exact ⟨y, hL, hy⟩
    · rintro ⟨y, hL, hy⟩
      refine ⟨hL, fun p => ?_⟩
      obtain ⟨h1, -, h3, h4⟩ := (hLM p _).1.2 ⟨y p, hy p⟩
      exact ⟨h1, h3, h4⟩
  · intro y y' h h'
    funext p
    exact (hLM p _).2 (y p) (y' p) (h.2 p).1 (h'.2 p).1
  · intro y hy
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hS.2.2.2.2 p hp
      have := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_loc p) (hR p)
        (hB.2.2.1 p hp) A A' (fun a b hab => ⟨hA.1 a b hab, hA'.1 a b hab⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
        (scaled Z p (frame G)) (scaled Z p (frame G'))
        (fun j => by rw [(hB.1 p).1]; exact hc j) (fun j => by rw [(hB.1 p).2.1]; exact hc' j)
        (d0 p) (hB.2.2.2.1 p) (y p)
      exact this.2 ⟨_, (hy.2 p).1⟩
    · obtain ⟨Λ₀, hΛ₀, hΛ₀p⟩ := hB.2.2.2.2
      haveI : Infinite (PlF D) := infinite_finPlaces D.host.F
      obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset P
      have hfull : Submodule.IsFullLattice D.host.E Λ :=
        isFullLattice_of_local_span Z q Λ hy.1
          (_root_.GlobalTheory.GenMass.Fibre.termLat D Z FP q (y q) _ (hy.2 q).1).2
      have hfull₀ : Submodule.IsFullLattice D.host.E Λ₀ :=
        isFullLattice_of_local_span Z q Λ₀ hΛ₀
          (_root_.GlobalTheory.GenMass.Fibre.termLat D Z FP q (d0 q) _ (hΛ₀p q hq)).2
      refine (((LatLoc.lattices_local_global D Z).1 Λ Λ₀ hfull hfull₀).1.union P.finite_toSet).subset ?_
      intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
      apply hp
      exact (_root_.GlobalTheory.LocOver.TermLat.datum_of_lattice (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)).2
        (y p) (d0 p) _ _ (hy.2 p).1 (hΛ₀p p hc.2) (by dsimp only [tm]; rw [hc.1]) (by dsimp only [tm]; rw [hc.1])
        (fun g _ => by dsimp only [tm]; rw [hc.1])
  · intro y y' h hh hmv
    have hloc : ∀ p, ∃ g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p, g ∈ (FP p).UW0 ∧
        LocNG.Datum.Moves g (y p) (y' p) ∧
        lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap h Λ) = LocNG.img g (lattice₂ D Z.M p Λ) := by
      intro p
      obtain ⟨g, hext, hU, huniq, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p h hh.1
      obtain ⟨g', hext', hm⟩ := hmv p
      obtain rfl : g' = g := huniq g' hext'
      refine ⟨g', Subgroup.subset_closure ⟨hU, fun b => ⟨?_, ?_⟩⟩, hm, (himg Λ).symm⟩
      · rw [(hB.1 p).1]
        show g' (frFac Z.δ p b • baseChange₂ D p (frame F b)) = _
        rw [map_smul, hext', hh.2.1 b]
        rfl
      · rw [(hB.1 p).2.1]
        show g' (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = _
        rw [map_smul, hext', hh.2.2 b]
        rfl
    choose g hgU hgm hgimg using hloc
    have hset := fun p => (GlobalTheory.T.unitaryComplement_moves_hermitianTerms (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)
      (scaled Z p (frame G)) (scaled Z p (frame G')) (hO p).1 (hO p).2 (g p) (hgU p) (y p) (y' p) (hgm p)).2
    have hlat : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap h Λ) ↔ Submodule.IsLattice D.host.E Λ := by
      constructor
      · intro hl
        have e : Λ = Formalism.HermitianLatticesTheory.gmap h.symm (Formalism.HermitianLatticesTheory.gmap h Λ) := by
          ext x; simp [Formalism.HermitianLatticesTheory.gmap]
        rw [e]; exact LatLoc.isLattice_map _ _ hl
      · exact LatLoc.isLattice_map _ _
    show (Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ ∈ locSet G G' p (y p)) ↔
      (Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap h Λ) ∧ ∀ p, lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap h Λ) ∈ locSet G G' p (y' p))
    rw [hlat]
    refine and_congr_right fun _ => forall_congr' fun p => ?_
    have e := hgimg p
    have key : ∀ L, L ∈ LocNG.img (g p) '' locSet G G' p (y p) ↔ L ∈ locSet G G' p (y' p) :=
      fun L => Set.ext_iff.mp (hset p) L
    have hinj : Function.Injective (LocNG.img (M := Z.M p) (g p)) := fun L₁ L₂ e =>
      Submodule.map_injective_of_injective (f := ((g p : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p).restrictScalars (Z.M p).L.O))
        (g p).injective e
    exact mem_iff_of_img hinj (Set.ext key) e
end

