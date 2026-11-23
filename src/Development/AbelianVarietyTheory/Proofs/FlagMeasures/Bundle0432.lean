module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0025
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0430
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0394
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0431
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair
public import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0221
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CorankOnePairsNonGenericRowBoundOfRemainingPremi
section
open Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic GlobalTheory.NGRow

theorem GlobalTheory.rowNGP_of_leaves (hCB : StepChoiceConstantsC) (hPin : StepPinExists) (hForm : Formalism.L2.SG.NGVanish.FormNGC)
    (hThmB : StepThmBPinnedP) (hG5 : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) (hW : Formalism.L2.SG.FamDefs.WeightsNG)
    (hG4 : Formalism.L2.SG.FamDefs.ProductStructureNonGeneric) (hEx : Formalism.L2.SG.FamDefs.ExistNG) : RowNGP := by
  obtain ⟨hS0, hNml, hPts, hN1, hX0⟩ := GlobalTheory.RowNGClosed.closedSteps
  have hFam : Formalism.L2.SG.NGLocModel.StepFamC := _root_.GlobalTheory.stepFamC_of_globalLeaves hG5 hW hG4 hEx
  have hconds : ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun D =>
    ((GlobalTheory.local_nongeneric_bound_record_family 39 le_rfl).2.1 D).1
  have hLoc : StepLocGenPinnedC :=
    stepLocGenPinnedC_of_loc (Formalism.L2.SG.NGLocModel.stepLocPinnedC_of_fam hconds hFam)
  have hVan : StepVanishPinned :=
    stepVanishPinned_of_term (Formalism.L2.SG.NGVanish.stepTermVanish_of_form hForm)
  have hAna : StepAnalyticP := _root_.GlobalTheory.NGRow.stepAnalyticP_of_steps hPin hVan hLoc hThmB
  have hMassData : StepAnalyticConstantsP := GlobalTheory.T.existsRowLevelWithAnalyticFacts_of_steps (tieOfCtx_of hX0) hCB hAna
  exact GlobalTheory.T.nonGenericCorankOnePairsBound_of_splitFiniteRealRow (GlobalTheory.T.rowSplitFiniteArchimedeanParts_of_steps hMassData sizes_of_hypotheses (stepClass_of_equiv hS0) hNml hPts
    (stepHeight_of_normOne hN1))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyLocalObjectsExistAtTermsProof
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  Formalism.L2.SG.FamDefs Formalism.MainNotions.S.LocNG

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem existFam : ExistFam := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hctx K S TS cls hF γ hP => ?_⟩
  have hTie : ConcTie X Y := hctx.2.2
  obtain ⟨hTS, _, hrow⟩ := hF
  obtain ⟨t₀, ht₀, hv, rfl⟩ := hP
  have hG : ∀ t ∈ TS, t.G ≠ 0 := by
    intro t ht h0
    rw [hTS] at ht
    apply ht.1
    show Gt t = 0
    simp [Gt, h0]
  have hrel : t₀.relevant := (_root_.GlobalTheory.NGClass.ngClass_rows D X Y u u' hTie).2.2 t₀ hv
  exact _root_.GlobalTheory.FamGen.exists_famTie D X Y u u' TS cls hG hrow t₀ ht₀ hrel

end GlobalTheory.SnFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabelsFixedByTupleOperatorOfTypeSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabPinTop

theorem kap_mem_GfC {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (k : X.B.I.Gf) : kap X h t k ∈ GfC (Yc D 0) := by
  have aux : ∀ (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (k : I.Gf),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)).symm ((1, k) : I.GA) ∈ GfC (D.sp.Y 0) := by
    intro I hI k
    subst hI
    have e : ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)).symm (1, k) =
        (Formalism.IndefR.RationalEmbedding.iota D).symm (1, k) := rfl
    rw [e]
    exact (Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (D := D) (1, k)).2 rfl
  have hy : (iotaX X h).symm ((1, k) : X.B.I.GA) ∈ GfC (D.sp.Y 0) := aux X.B.I h k
  show (t⁻¹ * (iotaX X h).symm (1, k) * t : GA D (D.sp.Y 0)) ∈ GfC (D.sp.Y 0)
  unfold GfC at hy ⊢
  rw [MonoidHom.mem_ker] at hy ⊢
  rw [map_mul, map_mul, hy, mul_one, map_inv, inv_mul_cancel]

theorem R_translate_ae {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0))
    (Φ : GA D (D.sp.Y 0) → ℂ) (hinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g) (f : L2X X)
    (hf : f =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t)) (k : X.B.I.Gf) :
    ((X.B.R (1, k) f : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x =>
      Φ ((iotaX X h).symm x * t * (show GA D (D.sp.Y 0) from kap X h t k)) := by
  have hU : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  have hFD := Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec
  have hφinv : ∀ γ ∈ X.B.I.GFset, ∀ y : X.B.I.GA,
      Φ ((iotaX X h).symm (γ * y) * t) = Φ ((iotaX X h).symm y * t) := by
    intro γ hγ y
    rw [map_mul, mul_assoc]
    exact hinv _ (iotaX_symm_rat X h γ hγ) _
  have hP : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) ((1, k) : X.B.I.GA) :=
    Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k
  have hPi : Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) (((1, k) : X.B.I.GA)⁻¹) := by
    have : ((1, k) : X.B.I.GA)⁻¹ = (1, k⁻¹) := Prod.ext inv_one rfl
    rw [this]; exact Formalism.L2.SG.Pf.RowDictPf.rp_fin X.B.I X.B.μf k⁻¹
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map hFD hP hPi
  have e1 := X.B.R_spec (1, k) f
  have e3 : ∀ᵐ x ∂(muX X), (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) =
      Φ ((iotaX X h).symm (X.B.I.rep X.B.fund (x * (1, k))) * t) := by
    refine ae_of_ae_map (p := fun y => (f : X.B.I.GA → ℂ) y = Φ ((iotaX X h).symm y * t)) h1 ?_
    rw [h2]
    exact hf
  filter_upwards [e1, e3] with x a1 a3
  rw [a1]
  show (f : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * (1, k))) = _
  rw [a3]
  obtain ⟨γ, hγ, hrep, -⟩ := Formalism.MainNotions.LeviCoordinates.rr_rep_spec hFD (x * (1, k))
  rw [Formalism.MainNotions.LeviCoordinates.rr_rep_eq_rep, show (Formalism.MainNotions.LeviCoordinates.rr_rep X.B.I.GFset X.B.fund (x * (1, k))) = γ * (x * (1, k)) from hrep,
    hφinv γ hγ]
  congr 1
  unfold kap
  rw [map_mul]
  group

end GlobalTheory.LabPinTop

namespace GlobalTheory.LabPinTop

theorem labTie_of_series : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (hF : D.host.F = maximalRealSubfield D.host.E) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (eE : D.what₂.EE →ₗ[ℂ] R.HE.H) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (C : Submodule ℂ (MMap (R.MY 0))), StdPsi hF PY → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ F, ι (D.sEE F) = conjHH X G (j F)) → RowJ R eE X h G t j → (∀ σ, R.HE.e (eE (D.what₂.onb σ)) ∈ isotIn (actM PY (R.MY 0)) C (FinTyp.conjT (rep (D.what₂.ft σ)))) → (∀ σ, ∀ k ∈ X.B.I.Kg X.B.g, ∀ v y, R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t k) = R.HE.e (eE (D.what₂.onb σ)) v y) → (∀ σ v, ∀ γ ∈ Formalism.L2.Theta.GQ (Yc D 0), ∀ y, R.HE.e (eE (D.what₂.onb σ)) v (γ * y) = R.HE.e (eE (D.what₂.onb σ)) v y) → TypeLab D rep → (∀ σ, D.ntypes.goodTuple (labOf σ)) → LabTie X ι := by
  intro D X h t PY hF G' _ _ Pl0 T A Ks _ _ _ R eE G j ι rep C hStd hHEq hι hJ hiso hK hQ hTL hgood
  let _ : Fintype (G0g D.nd) := Formalism.MainNotions.PrimeDegreeVariant.finiteLevelGroupFintype D
  have hlab : ∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v) := fun σ k v => ((hTL (D.what₂.ft σ)) k v).1
  refine ⟨hlab, hgood, fun σ => ?_⟩
  obtain ⟨c, red, hFR⟩ := _root_.GlobalTheory.LabPin.frameRed_exists D X h t PY hF hStd hHEq
  have hRH : IsRedHom X red := hFR.1
  choose sec hsec using hRH.2.2.1
  have hIS : IsSec X red sec := fun γ => hsec γ
  choose lf hlf using fun γ => PY.onto _ (kap_mem_GfC X h t (sec γ))
  have hser := _root_.GlobalTheory.LabFix.sum_serCoef_rt D X h t PY c red sec lf hFR hIS hlf (rep (D.what₂.ft σ)) (labOf σ) (hTL (D.what₂.ft σ))
  have hS := _root_.GlobalTheory.IsotConjFix.isotIn_conjT_fix_sum D D.R.r (MMap (R.MY 0)) (actM PY (R.MY 0)) C (rep (D.what₂.ft σ))
    {κ | ∃ k ∈ X.B.I.Kg X.B.g, PY.ψ κ = kap X h t k} (G0g D.nd) (serCoef (labOf σ)) lf
    (fun φ hφ hU => hser φ hφ (fun k hk κ hκ => hU κ ⟨k, hk, hκ⟩)) (R.HE.e (eE (D.what₂.onb σ))) (hiso σ)
    (by
      rintro κ ⟨k, hk, hκ⟩
      refine MultilinearMap.ext fun v => funext fun y => ?_
      rw [actM_apply, hκ]
      exact hK σ k hk v y)
  have hpt : ∀ v y, ∑ γ, star (serCoef (labOf σ) γ) * R.HE.e (eE (D.what₂.onb σ)) v (y * kap X h t (sec γ)) =
      R.HE.e (eE (D.what₂.onb σ)) v y := by
    intro v y
    have e := congrArg (fun T : MMap (R.MY 0) => T v y) hS
    simp only [finsum_eq_sum_of_fintype] at e
    rw [← e, sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [smul_apply, Pi.smul_apply, smul_eq_mul, actM_apply, hlf]
  obtain ⟨v₀, -, a, -, hj⟩ := hJ
  refine _root_.GlobalTheory.LabFix.mem_VT_of_sum_fixed D X red sec hRH hIS (labOf σ) (fun k v => hlab σ k v) (bRow X ι σ)
    (ι (D.sEE (D.what₂.onb σ))).2 ?_
  set Φ : GA D (D.sp.Y 0) → ℂ := fun y => star ((a : ℂ) * R.HE.e (eE (D.what₂.onb σ)) v₀ y) with hΦ
  have hΦinv : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, Φ (γ * g) = Φ g := fun γ hγ g =>
    congrArg (fun z => star ((a : ℂ) * z)) (hQ σ v₀ γ hγ g)
  have hb : bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := by
    show ((ι (D.sEE (D.what₂.onb σ)) : HHX X) : L2X X) = _
    rw [hι]
    rfl
  have hbr : (bRow X ι σ : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => Φ ((iotaX X h).symm x * t) := by
    rw [hb]
    filter_upwards [Lp.coeFn_star ((j (D.what₂.onb σ) : EEC X G) : L2X X), hj (D.what₂.onb σ)] with x b1 b2
    rw [b1, Pi.star_apply, b2]
    rfl
  have htr := fun γ => R_translate_ae X h t Φ hΦinv (bRow X ι σ) hbr (sec γ)
  rw [finsum_eq_sum_of_fintype]
  apply Lp.ext
  filter_upwards [coeFn_sum_smul (μ := muX X) (serCoef (labOf σ)) (fun γ => X.B.R ((1, sec γ) : X.B.I.GA) (bRow X ι σ)),
    ae_all_iff.2 htr, hbr] with x b1 b2 b3
  rw [b1, b3]
  simp only [b2, hΦ]
  rw [← hpt v₀ ((iotaX X h).symm x * t)]
  rw [Finset.mul_sum, star_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  have e : ∀ (c b s : ℂ), c * star (b * s) = star (b * (star c * s)) := fun c b s => by
    simp only [star_mul', star_star]; ring
  exact e _ _ _

end GlobalTheory.LabPinTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermDefectNeIffMoveLinearEquivStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTermDefect_ne_iff_move_linearEquiv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r), LocNG.BBne (H := H) (move g t) ↔ LocNG.BBne (H := H) t := by
  first | exact @GlobalTheory.LocOver.bbne_move | exact GlobalTheory.LocOver.bbne_move | (intros; apply GlobalTheory.LocOver.bbne_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatchedFamilyMassLawBaseSituation
section
noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinitePlaceMassFactors

theorem infinite_finPlaces (K : Type) [Field K] [NumberField K] :
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

theorem wt_self {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Loc.HermSp M V} {r : ℕ}
    {P : LocNG.FPair H r} (d : LocNG.Datum P) : LocNG.Datum.wt d d = 1 := by
  unfold LocNG.Datum.wt LocNG.volRel
  simp [Subgroup.relIndex_self]

end GlobalTheory.FinitePlaceMassFactors

namespace GlobalTheory.FinitePlaceMassFactors

theorem dl_loc_unsigned {D : D7} (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T)
    (F' : FlagG (VS D) D.R.rS T') (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    (locH Z p).Dl (fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a)) (fun a => frFac Z.δ p a • baseChange₂ D p (F'.fvec a)) l =
      (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i)) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F F' l) := by
  have hZ : (locH Z p).Zhat (fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a))
      (fun a => frFac Z.δ p a • baseChange₂ D p (F'.fvec a)) =
      Matrix.diagonal (fun a => (Z.M p).L.cj (frFac Z.δ p a)) * (Formalism.MainNotions.S.Zhat F F').map (D.s.atP p).ιE *
        Matrix.diagonal (fun b => frFac Z.δ p b) := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    show LocFacts₂ Z.M p (frFac Z.δ p b • baseChange₂ D p (F'.fvec b)) (frFac Z.δ p a • baseChange₂ D p (F.fvec a)) = _
    rw [Formalism.L2.SG.Pf.BBTie.formP_bc, Matrix.map_apply]
    simp only [Formalism.MainNotions.S.Zhat]
    ring
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl leadMinorE
  rw [dite_eq_left hl, dite_eq_left hl, hZ]
  have hsub : (Matrix.diagonal (fun a => (Z.M p).L.cj (frFac Z.δ p a)) *
        (Formalism.MainNotions.S.Zhat F F').map (D.s.atP p).ιE *
        Matrix.diagonal (fun b => frFac Z.δ p b)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i))) *
        ((Formalism.MainNotions.S.Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE *
        Matrix.diagonal (fun i => frFac Z.δ p (Fin.castLE hl i)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  have hdm : ∀ A : Matrix (Fin l) (Fin l) D.host.E, (A.map (D.s.atP p).ιE).det = (D.s.atP p).ιE A.det :=
    fun A => (RingHom.map_det _ A).symm
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hdm, Finset.prod_mul_distrib]
  ring

theorem gval_ne_of_primeTo : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)),
    Based Z FP Tn T'n F F' → ∀ p : PlF D, (FP p).PrimeTo → Gval F F' ≠ 0 := by
  intro D Z FP Tn T'n F F' hB p hP hG0
  obtain ⟨-, ⟨-, y, -, hy⟩, -⟩ := hP
  obtain ⟨hA, hB', hT, hT'⟩ := hB p
  set c := ∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p i.castSucc) * frFac Z.δ p i.castSucc with hc
  have h1 := dl_loc_unsigned Z p F.fl F'.fl (D.R.rS + 1) le_rfl
  rw [Fin.prod_univ_castSucc] at h1
  simp only [Fin.castLE_rfl, id, Formalism.L2.SG.Pf.BBTie.bt_frFac_last, mul_one, map_one] at h1
  have h2 : (locH Z p).Dl (fun a => frFac Z.δ p a • baseChange₂ D p (F.fl.fvec a))
      (fun a => frFac Z.δ p a • baseChange₂ D p (F'.fl.fvec a)) D.R.rS =
      c * (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl D.R.rS) := by
    rw [dl_loc_unsigned Z p F.fl F'.fl D.R.rS (Nat.le_succ _)]
    rfl
  have hcj : ∀ x : D.host.E, (Z.M p).L.cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x) :=
    fun x => cj_iota (Z.hcj p) x
  have hG' : (FP p).Gv = (c * (Z.M p).L.cj c) * (D.s.atP p).ιE (Gval F F') := by
    unfold Formalism.MainNotions.S.LocNG.FPair.Gv Loc.HermSp.Gdet Loc.HermSp.normE
    rw [hA, hB', hT, hT']
    erw [h1, h2]
    simp only [map_mul, hcj, Gval, Gflag, map_sub, map_natCast]
    ring
  rw [hG', hG0, map_zero, mul_zero, zero_mul] at hy
  exact zero_ne_one hy

end GlobalTheory.FinitePlaceMassFactors

namespace GlobalTheory.FinitePlaceMassFactors

theorem finprod_wt_eq {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    (P : Finset (PlF D)) (d0 d : Dat Z FP) (h : ∀ p, p ∉ P → d p = d0 p) :
    ∏ᶠ p, LocNG.Datum.wt (d0 p) (d p) = ∏ p ∈ P, LocNG.Datum.wt (d0 p) (d p) := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun p hp => ?_
  by_contra hP
  apply hp
  show LocNG.Datum.wt (d0 p) (d p) = 1
  rw [h p hP, wt_self]

theorem tied_mass_law : ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' → ∀ (K : Type) (S : Prop → Prop) (TS : Set (TauC Y u u')) (cls : TauC Y u u' → K), GlobalTheory.SnFam.FamQ Y u u' S TS cls → ∀ (γ : PN.Pts D.host.E D.R.rS) (Fm : LocFam (zOf Y) K (NuC D)), FamTie TS cls (nmlOf Y u u') γ Fm → OrbitFamilyIdentityAt Fm Fm.V0 → ∃ (w : Point D.host.E (D.R.rS + 1)) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Y0 : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep), toPts w = γ ∧ (∃ n ∈ NRat (lf D (X.Fu u)), ∀ a, frame F a = n (frame (lf D (X.Fu u)) a)) ∧ ZhatOM (ZhatL F F') = ptMat w ∧ TotPos (Gval F F') ∧ BaseOK (Tu D u) (Tu D u') F F' Fm.P Fm.d0 ∧ MassLaw F F' Fm.P Fm.d0 Fm.V0 ∧ ∀ p ∈ Fm.P, Fm.ngenL p = (ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p))).toReal ∧ ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t ∧ (locH (zOf Y) p).Zhat t.f t.f' ∈ clsLoc ((zOf Y).M p) (Y0 p) := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' _ K S TS cls hFQ γ Fm hFT hG5
  obtain ⟨w, F00, F'0, F'1, hw, hDs, -, hn0, hZ, hbase, -, hgood, hstd, ⟨t₀, ht₀, hpt₀, ht₀loc⟩, hd0P,
    ⟨Λ₀, hΛ₀, hΛ₀loc⟩, hdat, -, hngen⟩ := hFT
  subst hw
  set F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E) := ⟨F00.fl, F00.fl.z⟩ with hFdef
  set F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E) := ⟨F'0.fl, F'0.fl.z⟩ with hF'def
  have hBased : Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' := fun p => hbase p
  have hZF : ZhatOM (ZhatL F F') = ptMat w := hZ
  have hG : Gval F F' ≠ 0 := by
    haveI : Infinite (PlF D) := infinite_finPlaces D.host.F
    obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset Fm.P
    exact gval_ne_of_primeTo D (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' hBased p (hgood p hp)
  have hRel : ∀ p, (Fm.FP p).RelG (LocNG.theta ((zOf Y).M p)) := fun p =>
    (_root_.GlobalTheory.LocBaseRel.atBase_relG D (zOf Y) u u' w F00 F'0 hZ hG p).2 _ (hbase p)
  have hTot : TotPos (Gval F F') := fun τ =>
    (Formalism.MainNotions.LatticeGluingRadicals.b_G_pos (Formalism.MainNotions.LatticeGluingRadicals.p_starConj D) (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) F F' rfl rfl hG
      (Formalism.MainNotions.LatticeGluingRadicals.p_posX D _ (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) F) _).1
  have hd0 : ∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ := fun p =>
    if hp : p ∈ Fm.P then hd0P p hp else ⟨_, ht₀loc p hp⟩
  have hΛfin : {p | ¬ ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀}.Finite :=
    Fm.P.finite_toSet.subset fun p hp => by
      by_contra h
      exact hp ⟨_, hΛ₀loc p h, rfl⟩
  obtain ⟨V1, hV1, hmass⟩ := _root_.GlobalTheory.Unfold.mass_genus_local_weights D X Y u u' F F' w hZF hG (zOf Y) Fm.FP hBased hRel Fm.d0 hd0
    ⟨Λ₀, hΛ₀, hΛfin⟩
  obtain ⟨hcNG, hcGen, -, -⟩ := _root_.GlobalTheory.LocOrbit.closed_ng_gen D X Y u u' F F' w hZF hG (zOf Y) Fm.FP hBased hRel
  have hLC : LocClosed F F' (zOf Y) Fm.FP TS := by
    rw [hFQ.1]
    intro t t' Λ Λ' h1 h2 h3 ht
    obtain ⟨hGt, hSt⟩ := ht
    by_cases hg : (Y.tO u u').gener t
    · have h' : t' ∈ (Y.tO u u').genSet := hcGen t t' Λ Λ' h1 h2 h3 ⟨hGt, hg⟩
      refine ⟨h'.1, ?_⟩
      have e : (¬ (Y.tO u u').gener t') = (¬ (Y.tO u u').gener t) := propext (by simp [hg, h'.2])
      rw [e]; exact hSt
    · have h' : t' ∈ (Y.tO u u').ngSet := hcNG t t' Λ Λ' h1 h2 h3 ⟨hGt, hg⟩
      refine ⟨h'.1, ?_⟩
      have e : (¬ (Y.tO u u').gener t') = (¬ (Y.tO u u').gener t) := propext (by simp [hg, h'.2])
      rw [e]; exact hSt
  have hdat' : ∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧
      ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧
        ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν →
          (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (Formalism.L2.SG.TermOp.wt t) ^ 2 := by
    intro c ν
    have h := hdat c ν
    refine ⟨fun hn => ?_, fun d hd => ?_⟩
    · rw [hn] at h; exact h
    · rw [hd] at h; exact h
  have hΛrows : ∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P →
      ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀ :=
    ⟨Λ₀, hΛ₀, fun p hp => ⟨_, hΛ₀loc p hp, rfl⟩⟩

  have hV : Fm.V0 = V1 := by
    cases hd : Fm.dat (cls t₀) (nmlOf Y u u' t₀) with
    | none => exact absurd ⟨t₀, ht₀, rfl, hpt₀, rfl⟩ ((hdat' _ _).1 hd)
    | some d =>
      set dd : Dat (zOf Y) Fm.FP := fun p => if hp : p ∈ Fm.P then (d ⟨p, hp⟩).1 else Fm.d0 p with hdd
      have hdd1 : ∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1 := fun p hp => by simp [hdd, hp]
      have hdd2 : ∀ p, p ∉ Fm.P → dd p = Fm.d0 p := fun p hp => by simp [hdd, hp]
      obtain ⟨hddT, hsum⟩ := _root_.GlobalTheory.Unfold.GenusRows.rows_mass_genus D X Y u u' F F' w hZF hG TS cls Fm hBased hFQ.2.1 hLC hDs hstd
        hΛrows hdat' d ⟨(cls t₀, nmlOf Y u u' t₀), hd⟩ dd hdd1 hdd2
      have hfin : {p | dd p ≠ Fm.d0 p}.Finite :=
        Fm.P.finite_toSet.subset fun p hp => by
          by_contra h
          exact hp (hdd2 p h)
      have hm := hmass dd hddT hfin
      have h5 := hG5.2 d ⟨(cls t₀, nmlOf Y u u' t₀), hd⟩
      rw [hsum, hm, finprod_wt_eq Fm.P Fm.d0 dd hdd2] at h5
      have hprod : ∏ p, Fm.toL.wt p (d p) = ∏ p ∈ Fm.P, LocNG.Datum.wt (Fm.d0 p) (dd p) := by
        rw [← Finset.prod_coe_sort Fm.P]
        refine Finset.prod_congr rfl fun p _ => ?_
        show LocNG.Datum.wt (Fm.d0 p.1) (d p).1 = _
        rw [hdd1 p.1 p.2]
        rfl
      rw [hprod] at h5
      have hpos : 0 < ∏ p ∈ Fm.P, LocNG.Datum.wt (Fm.d0 p) (dd p) :=
        Finset.prod_pos fun p _ => _root_.GlobalTheory.WtPos.wt_pos D (zOf Y) p (Fm.FP p) (hRel p) _ _ (hd0 p) (hddT p)
      rw [ENNReal.ofReal_eq_ofReal_iff (mul_pos hV1 hpos).le (mul_pos hG5.1 hpos).le] at h5
      exact (mul_right_cancel₀ hpos.ne' h5).symm
  refine ⟨w, F, F', fun p => (locH (zOf Y) p).Zhat (locF Y p (lf D (X.Fu u))) (locF' Y p F'1), rfl, hn0, hZF, hTot,
    ⟨hBased, hRel, hgood, hd0, Λ₀, hΛ₀, fun p hp => ?_⟩, fun d hoff hterm => ?_, hngen⟩
  · have e1 := (hbase p).2.2.1
    have e2 := (hbase p).2.2.2
    simp only [tm, e1, e2]
    exact hΛ₀loc p hp
  · have hfin : {p | d p ≠ Fm.d0 p}.Finite :=
      Fm.P.finite_toSet.subset fun p hp => by
        by_contra h
        exact hp (hoff p h)
    rw [hmass d hterm hfin, finprod_wt_eq Fm.P Fm.d0 d hoff, hV]

end GlobalTheory.FinitePlaceMassFactors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedLocalTermDefectIffUnsignedLocalTermStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signedLocalTerm_defect_iff_unsignedLocalTerm : ∀ {D : D7} (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') (Tn T'n : ℕ), locBBne Z p Λ F F' Tn T'n ↔ LocNG.BBne (H := locH Z p) (locU Z p Λ F F' Tn T'n) := by
  first | exact @GlobalTheory.SignDefect.locBBne_iff_locU | exact GlobalTheory.SignDefect.locBBne_iff_locU | (intros; apply GlobalTheory.SignDefect.locBBne_iff_locU <;> assumption)
end

