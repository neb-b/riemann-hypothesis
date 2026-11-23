module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0403
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.StepLocGenPinnedGP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0232
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothMapsClosure
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountConstantsOfSiegelWeil
section
open Formalism.MainNotions Formalism.MainNotions.S MeasureTheory

namespace GlobalTheory.CountConstants

theorem count_constants_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∃ (c30 : List ℝ → Formalism.MainNotions.S.CountingConstants) (cIc : ℝ),
      (∀ {eps : ℝ} (Fm : FamP eps), 0 ≤ (c30 Fm.cOut).C ∧ 2 * (Fm.CYL + 1) ≤ (c30 Fm.cOut).A) ∧ 0 < cIc ∧
      (∀ {eps : ℝ} (Fm : FamP eps), cIc ≤ (c30 Fm.cOut).c) ∧
      ∀ (P : ∀ I : AutInst, Measure I.Gf → ℕ → (I.Gf → ℂ) → Prop) {eps : ℝ} (Fm : FamP eps),
        CountE.CountAllPointsClass P Fm (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C (c30 Fm.cOut).c (c30 Fm.cOut).cb := by
  intro hSW
  have H := GlobalTheory.CountBridge.count_typed_of_volumeStep (GlobalTheory.GaussMean.volumeStep_of_siegelWeil hSW)
  choose n₀ C₀ hC₀ HC using H
  let Af : List ℝ → ℝ := fun l => 2 * (l.getD 6 0 + 1)
  refine ⟨fun l => ⟨0, n₀ (Af l), Af l, 0, C₀ (Af l), 1 / 16, 1 / 16⟩, 1 / 16,
    fun Fm => ⟨hC₀ _, le_refl _⟩, by norm_num, fun Fm => le_refl _, fun P {_} Fm => ⟨by norm_num, by norm_num, ?_⟩⟩
  intro x i
  exact CountE.count_class_of_count P (HC _ _ le_rfl _ le_rfl _)

end GlobalTheory.CountConstants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumDegreeEqMulFormalDegreeGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.GapDegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem deg_eq_mul_fdegH : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → (∃ h : ℝ, GapAtLeast (epsSH D.R) lam h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW
  have hμ : PI.BesselPeriodGGP.IsHaarOn (GG D.R.k D.R.rS) W.μG := hW.2.2.2.2.2.2.1
  by_cases hQ : ∃ Q, IsCayley D.R.k D.R.rS (epsSH D.R) Q
  swap
  · refine ⟨1, one_pos, fun lam A hA _ => absurd ?_ hQ⟩
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact ⟨P, hP⟩
  obtain ⟨Q, hQ⟩ := hQ
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  obtain ⟨a, ha0, hat, ha⟩ := GlobalTheory.BesselDegree.haar_eq_smul hQd hQ.2 W.μG hμ
  set s : ℝ≥0∞ := ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ≥0∞) with hs
  have hs0 : s ≠ 0 := ENNReal.coe_ne_zero.2 (D.s.cdScale_pos _ _).ne'
  have hst : s ≠ ∞ := ENNReal.coe_ne_top
  have hb0 : a / s ≠ 0 := (ENNReal.div_pos ha0 hst).ne'
  have hbt : a / s ≠ ∞ := (ENNReal.div_lt_top hat hs0).ne
  have hκ : 0 < (a / s).toReal := ENNReal.toReal_pos hb0 hbt
  refine ⟨(a / s).toReal, hκ, fun lam A hA _ v hv => ?_⟩
  obtain ⟨P, hP, hd, hS⟩ := hA.2.2.2.2.2.2.2.2.2.2
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hme : MeasurableEmbedding (phi (epsSH D.R) P) :=
    (phi_closedEmbedding (ε := epsSH D.R) Formalism.REAL.isClosedEmbeddingMatrix hPd).measurableEmbedding
  have hb : W.μG = (a / s) • (s • Formalism.REAL.muG (epsSH D.R)).map (phi (epsSH D.R) P) := by
    rw [Measure.map_smul, smul_smul, ENNReal.div_mul_cancel hs0 hst, GlobalTheory.DegreeTie.map_phi_eq hP hQ]
    · exact ha
    · exact hme.measurable.aemeasurable
  have hf : PI.BesselPeriodGGP.fdegH W.μG A.σ v = A.deg / (a / s).toReal := by
    refine Formalism.FourierDecayAlt.P.DDSmoothness.fdeg_eq (div_pos hd hκ) (fun v w v' w' => ?_) hv
    obtain ⟨h1, h2⟩ := hS v w v' w'
    rw [hb]
    constructor
    · refine Integrable.smul_measure ?_ hbt
      rw [hme.integrable_map_iff]
      exact h1
    · rw [integral_smul_measure, hme.integral_map]
      have h3 : ∫ g, ⟪w, A.σ (Matrix.of (phi (epsSH D.R) P g)) v⟫_ℂ *
          star ⟪w', A.σ (Matrix.of (phi (epsSH D.R) P g)) v'⟫_ℂ
          ∂(s • Formalism.REAL.muG (epsSH D.R)) = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / ((A.deg : ℝ) : ℂ) := h2
      rw [h3, Complex.ofReal_div, div_div_eq_mul_div, Complex.real_smul]
      ring
  refine ⟨?_, hd⟩
  rw [hf]
  field_simp

end GlobalTheory.GapDegreeTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqualWordGenericBoundOfNormalisedSteps
section
open Formalism.FourierDecayAlt Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna GlobalTheory.SnPos

namespace GlobalTheory.SnPos

theorem rowMainEqP_of_pinned (hCh : PN.NGChain) (hC : StepClassG) (hN : StepNormalsG) (hP : StepPointsG)
    (hO : StepNormOneG) (hTi : TieOfCtx) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hV : StepTermVanishG)
    (hL : StepLocGenPinnedG) (hT : StepThmBGP) : GlobalTheory.SnPos.RowMainEqP :=
  GlobalTheory.T.equalWordGenericBound_of_cutBound_positive hCh Formalism.L2.SG.Pf.MainEqCut.meanAmplitudeGeneric_holds
    (GlobalTheory.T.generic_height_bound_of_local_estimates Formalism.L2.SG.NGCut.sizes_of_hypotheses hC hN hP (stepHeightG_of_normOne hO)
      (GlobalTheory.T.analyticGenericBound_of_choiceStep_positive hTi hB (_root_.GlobalTheory.SnPos.stepAnalyticCGP_of_steps hE hV hL hT)))

end GlobalTheory.SnPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGoodLocalDatumOfNonzeroPeriodsGap
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DatumOfPeriodsGap

theorem exists_goodS : GlobalTheory.GapIn.Hyp → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDG (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  intro hH D τ w w' θ W lam R _ l l' dd _ _ hRG hl hl' hdd hn hn'
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hR : R.IsDS (epsSH D.R) lam := GlobalTheory.isDS_of_isDG hRG
  obtain ⟨P, hP, hD⟩ := hR.2
  have hD' : Formalism.MainNotions.S.IsDS (epsSH D.R) lam (fun g => R.σ (P⁻¹ * g * P)) := hD
  obtain ⟨d, hd⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS _ _ _ _ _ hD' _ (D.s.cdScale_pos _ (epsSH D.R))
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hD'
  obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
  have hvs : v ∈ R.sm :=
    ((GlobalTheory.CompactStable.kStable_smooth_and_stable hK _ _ _ lam R hR P hP S hS.1 hS.2.1).1 v hvS).2
  refine ⟨{ H := R.H, σ := R.σ, B := fun x => ((Real.sqrt (Module.finrank ℂ W.Wp : ℕ) : ℝ) : ℂ) • l x,
            B' := fun x => ((Real.sqrt (Module.finrank ℂ W.Wq : ℕ) : ℝ) : ℂ) • l' x,
            v0 := v, cN := ‖v‖ ^ 2 / dd, deg := d },
    hR.1, hR.2, GlobalTheory.DatumOfPeriods.isBesselMapSm_smul hl _, GlobalTheory.DatumOfPeriods.isBesselMapSm_smul hl' _, hvs, hv0,
    ⟨P, hP, ?_⟩, div_pos (pow_pos (norm_pos_iff.2 hv0) 2) hdd,
    GlobalTheory.DatumOfPeriods.l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn v hvs), GlobalTheory.DatumOfPeriods.l2SG_sqrt_smul_eq_ofReal_mul _ _ _ _ (hn' v hvs),
    P, hP.1, hd⟩
  exact (le_sSup (s := {S | IsKTypeOf (epsSH D.R) (fun g => R.σ (P⁻¹ * g * P)) (Formalism.QuantumDeterminants.lowK (epsSH D.R) lam) S}) hS) hvS

end GlobalTheory.DatumOfPeriodsGap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsKFinCoefTorusNe
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.GapAmpTK

open GlobalTheory.AmpTK

theorem exists_kFinCoef_torus_ne : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → GlobalTheory.AmpTK.SmCW L l → GlobalTheory.AmpTK.SmCW L l' → (∃ x ∈ (GlobalTheory.AmpTK.rep L).TK, l x ≠ 0) → (∃ y ∈ (GlobalTheory.AmpTK.rep L).TK, l' y ≠ 0) → ∃ (f₁ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp)) (s₁ : ℂ), Formalism.MainNotions.S.IsKFinCoefH L.σ f₁ ∧ BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f₁ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s₁ ∧ s₁ ≠ 0 := by
  intro H k r L l l' κ τ hκ hτ hl hl' hxe hye
  have hK : PI.KFinSmooth := H.1.1.2.2.1
  have hDS : (rep L).IsDS L.ε L.lam := ⟨L.hlam, L.hσ⟩
  obtain ⟨hmul0, hone0, hinn0, hsm0, hTKsm0, hTKg0, hKT0, -, -⟩ :=
    GlobalTheory.rep_basic_of_isDS hK k r L.ε L.lam (rep L) hDS
  have hmul : ∀ g ∈ BranchingSupport.GG k r, ∀ h ∈ BranchingSupport.GG k r, ∀ v : L.Hs, L.σ (g * h) v = L.σ g (L.σ h v) := hmul0
  have hone : ∀ v : L.Hs, L.σ 1 v = v := hone0
  have hinn : ∀ g ∈ BranchingSupport.GG k r, ∀ v w : L.Hs, ⟪L.σ g v, L.σ g w⟫_ℂ = ⟪v, w⟫_ℂ := hinn0
  have hR : Formalism.MainNotions.S.IsURepOn (BranchingSupport.GG k r) (rep L).σ := GlobalTheory.Amp.LocalInputs.urep_of_ds L.hσ
  have hd : Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH hκ hτ
  have hdi : Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ ∈ BranchingSupport.GG k r := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH hκ hτ
  have hddi : ∀ v : L.Hs, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) v) = v := by
    intro v
    rw [← hmul _ hd _ hdi, Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ, hone]
  have side : ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (m : L.Hs → V),
      SmCW L m → (∃ x ∈ (rep L).TK, m x ≠ 0) →
      ∃ x₀ : L.Hs, (rep L).KFin x₀ ∧ m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) ≠ 0 := by
    intro V _ _ _ m hm ⟨x, hxT, hx⟩
    haveI := FiniteDimensional.complete ℂ V
    refine GlobalTheory.exists_kFin_ne_zero_of_cwCont hK k r L.ε L.lam (rep L) hDS V
      (fun v => m (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v)) ?_ ?_ ?_ ?_
    · intro v hv w hw
      exact (congrArg m (map_add (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) v w)).trans
        (hm.1 _ (hsm0 _ hd _ hv) _ (hsm0 _ hd _ hw))
    · intro a v hv
      exact (congrArg m (map_smul (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ)) a v)).trans (hm.2.1 _ _ (hsm0 _ hd _ hv))
    · exact GlobalTheory.SmMapAct.cw_comp (GlobalTheory.BesselMove.smMap_sigma hR hd) hm.2.2
    · refine ⟨L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) x, hsm0 _ hdi _ (hTKsm0 _ hxT), ?_⟩
      exact fun h0 => hx ((congrArg m (hddi x)).symm.trans h0)
  obtain ⟨x₀, hx₀, hx₀'⟩ := side l hl hxe
  obtain ⟨y₀, hy₀, hy₀'⟩ := side l' hl' hye
  set ξ := l (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀) with hξ
  set ξ' := l' (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀) with hξ'
  let P : L.Hs →L[ℂ] L.Wp := (innerSL ℂ x₀).smulRight ξ
  let Q : L.Wq →L[ℂ] L.Hs := (innerSL ℂ ξ').smulRight y₀
  let X : L.Wq →L[ℂ] L.Wp := (innerSL ℂ ξ').smulRight ξ
  have hP : ∀ v, P v = ⟪x₀, v⟫_ℂ • ξ := fun v => rfl
  have hQ : ∀ w, Q w = ⟪ξ', w⟫_ℂ • y₀ := fun w => rfl
  have hX : ∀ w, X w = ⟪ξ', w⟫_ℂ • ξ := fun w => rfl
  refine ⟨fun g => P.comp ((L.σ g).comp Q), ⟪ξ, X ξ'⟫_ℂ, ⟨P, Q, ?_, ?_, fun g => rfl⟩, ?_, ?_⟩
  · intro w
    obtain ⟨S, hS, hyS, hSK⟩ := hy₀
    refine ⟨S, hS, ?_, hSK⟩
    rw [hQ]
    exact S.smul_mem _ hyS
  · intro v
    have hadj : ContinuousLinearMap.adjoint P v = ⟪ξ, v⟫_ℂ • x₀ := by
      apply ext_inner_right ℂ
      intro u
      rw [ContinuousLinearMap.adjoint_inner_left, hP, inner_smul_left, inner_smul_right, inner_conj_symm, mul_comm]
    rw [hadj]
    obtain ⟨S, hS, hxS, hSK⟩ := hx₀
    exact ⟨S, hS, S.smul_mem _ hxS, hSK⟩
  · refine ⟨1, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, fun _ => L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) y₀,
      fun _ => X, fun _ => ⟨hTKg0 _ hd _ (hKT0 _ hx₀), hTKg0 _ hd _ (hKT0 _ hy₀)⟩, ?_, ?_⟩
    · intro g hg
      have key : L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ g) =
          (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ)).comp ((L.σ g).comp (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ))) := by
        ext v
        show L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ * g * Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) v = _
        rw [hmul _ (GlobalTheory.BesselMove.mul_mem' hdi hg) _ hd, hmul _ hdi _ hg]
        rfl
      have key2 : ∀ u, ⟪x₀, L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u⟫_ℂ =
          ⟪L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dM k r κ τ) x₀, u⟫_ℂ := by
        intro u
        rw [← hinn _ hd x₀ (L.σ (Formalism.MainNotions.FrameBoundFromBesselTorus.dMi k r κ τ) u), hddi]
      ext w
      simp only [Fin.sum_univ_one, ContinuousLinearMap.comp_apply, key, ContinuousLinearMap.smul_apply, hP, hQ, hX,
        map_smul, key2, inner_smul_right, smul_smul, mul_comm]
      exact congrArg (fun c : ℂ => c • ξ) (mul_comm _ _)
    · simp only [Fin.sum_univ_one]
      rfl
  · rw [hX, inner_smul_right]
    exact mul_ne_zero (inner_self_ne_zero.2 hy₀') (inner_self_ne_zero.2 hx₀')

end GlobalTheory.GapAmpTK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypotheses
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapSetup

theorem isFamG_of_num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ)
    (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (hN : Num k r lam u b bv ga h q0) (hF : IsFam lam q0 R) :
    IsFamG lam q0 R := by
  have H := GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hN
  intro ν hν
  have hd := hF ν hν
  exact ⟨hd.1, hd.2, ⟨h / 2, (H.2 ν hν).2.2.1, H.1.2.2.2.2⟩⟩

theorem families_gap : (∀ (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r), Num k r lam u b bv ga h q0 → IsFam lam q0 R → IsFamG lam q0 R) ∧ ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg ↔ SetupG lam u b bv ga h q0 z π μW μN μG νq R lb dg := by
  refine ⟨isFamG_of_num, ?_⟩
  intro k r Wp _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg
  constructor
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, isFamG_of_num k r lam u b bv ga h q0 R hN hF, hS, hSF⟩
  · rintro ⟨hN, hF, hS, hSF⟩
    exact ⟨hN, fun ν hν => GlobalTheory.isDS_of_isDG (hF ν hν), hS, hSF⟩

end GlobalTheory.GapSetup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteRationalIsometriesFixingFramesConjStabiliz
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.FixFin

section Img

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem img_mul (g g' : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * g') Λ = LocNG.img g (LocNG.img g' Λ) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨g' x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩

theorem img_one (Λ : Submodule M.L.O V) : LocNG.img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hv; exact ⟨v, hv, rfl⟩

theorem img_inv {g : V ≃ₗ[E] V} {Λ Λ' : Submodule M.L.O V} (h : LocNG.img g Λ = Λ') :
    LocNG.img g⁻¹ Λ' = Λ := by
  rw [← h, ← img_mul, inv_mul_cancel, img_one]

theorem mem_Aut {g : V ≃ₗ[E] V} {Λ : Submodule M.L.O V} : g ∈ LocNG.Aut Λ ↔ LocNG.img g Λ = Λ := by
  constructor
  · intro hg
    unfold LocNG.Aut at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact img_one Λ
    | mul x y _ _ hx hy => rw [img_mul, hy, hx]
    | inv x _ hx => exact img_inv hx
  · intro h; exact Subgroup.subset_closure h

theorem img_fg_span (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  have e : (LocNG.img g L : Set V) = (g : V →ₗ[E] V) '' (L : Set V) := rfl
  rw [e, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

end Img

variable {D : D7}

theorem localLattice_fg_span (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hc : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E ((LatLoc.cE D).toLinearMap '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (LatLoc.cE D).surjective
  have := (_root_.GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hc).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

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


end GlobalTheory.Unfold.FixFin


set_option maxHeartbeats 1000000 in
open GlobalTheory.Unfold.FixFin in
theorem GlobalTheory.Unfold.FixFin.conj_aut_finite : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → ∀ Λ₀ : LV D, Submodule.IsFullLattice D.host.E Λ₀ → ∀ a : ∀ p, ↥(FP p).UW0, {p | ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∉ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite → {h : ↥(FlagPairStabilizer F F') | ∀ p, (((a p)⁻¹ * φ h p * a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) ∈ LocNG.Aut (lattice₂ D Z.M p Λ₀)}.Finite := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ Λ₀ hΛ₀ a ha
  have hLG := LatLoc.lattices_local_global D Z
  obtain ⟨Λa, hΛa, hΛap⟩ := hLG.2 Λ₀ hΛ₀
    (fun p => LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (lattice₂ D Z.M p Λ₀))
    (fun p => img_fg_span _ _ (localLattice_fg_span Z Λ₀ hΛ₀ p))
    (ha.subset fun p hp hA => hp (mem_Aut.1 hA))
  obtain ⟨p⟩ := GlobalTheory.PhiEmbed.exists_place D
  have hΛaFull : Submodule.IsFullLattice D.host.E Λa := by
    apply isFullLattice_of_local_span Z p Λa hΛa
    rw [hΛap p]
    exact (img_fg_span _ _ (localLattice_fg_span Z Λ₀ hΛ₀ p)).2
  have H128 := _root_.GlobalTheory.RatLocMove.rat_ext_moves D X Y u u' F F' w hw hG Z FP hB hR
  have H133 := (_root_.GlobalTheory.Unfold.ClFin.classes_finite D X Y u u' F F' w hw hG Z FP hB hR Λa hΛaFull).1
  refine (H133.preimage Subtype.val_injective.injOn).subset ?_
  intro h hh
  refine ⟨h.2, ?_⟩
  have hgl : Submodule.IsFullLattice D.host.E (Formalism.HermitianLatticesTheory.gmap (h : GV D) Λa) := by
    refine { toIsLattice := LatLoc.isLattice_map (h : GV D) Λa hΛa, span_eq_top := ?_ }
    change Submodule.span D.host.E (((h : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) '' (Λa : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, hΛaFull.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (h : GV D).surjective
  apply (hLG.1 _ _ hgl hΛaFull).2
  intro p
  rw [H128.2.2.1 (h : GV D) p _ Λa (hφ h p), hΛap p]
  have e := mem_Aut.1 (hh p)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, img_mul, img_mul] at e
  have e2 := congrArg (LocNG.img ((a p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) e
  rwa [← img_mul, mul_inv_cancel, img_one] at e2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassRowLatticeOrthogonalSplitPrimeStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_rowLattice_orthogonal_split_prime : ∀ (D : D7) (u : D.what₂.Word), letI := D.host.cmStar; ∀ F0 : FlagG (VS D) D.R.rS ((Lat.Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u → (Lat.Tu D u).Prime → Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) → ∀ Λ : Cnt.LatV D, IsRowLat D F0 Λ → mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) = Cnt.massS D D.R.k * ((((Lat.Tu D u : ℕ) : ℝ) ^ D.R.k - 1) / (((Lat.Tu D u : ℕ) : ℝ) - 1)) ^ D.R.f ∧ Cnt.massS D D.R.k * Cnt.NT D u ^ (D.R.k - 1) ≤ mass (D.sp.X 0).hT (Lat.L0X D Λ (lf D F0)) := by
  first | exact @GlobalTheory.Mass.RowPerpMass.main | exact GlobalTheory.Mass.RowPerpMass.main | (intros; apply GlobalTheory.Mass.RowPerpMass.main <;> assumption)
end

