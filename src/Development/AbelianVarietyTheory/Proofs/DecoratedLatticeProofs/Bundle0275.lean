module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0087
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0045
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockOperatorActsByNoncompactQuadraticOps
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWords
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem kExp_absConv_tied : Formalism.L2.SG.ThmSOwn.KExpTied ∧ AbsConvTied :=
  ⟨Formalism.L2.SG.ThmSOwn.kExpTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.InHHC_holds
            Formalism.L2.SG.Closed.FundExistsC_holds Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.OOFundIndepC_holds
            Formalism.L2.SG.Closed.AmpWellDefC_holds Formalism.L2.SG.Closed.AbsConvC_outright Formalism.L2.SG.Closed.KExpansionC_holds,
    Formalism.L2.SG.RowsConc.absConvTied_of_full Formalism.L2.SG.Closed.FoldOKC_outright Formalism.L2.SG.Closed.FundExistsC_holds
      Formalism.L2.SG.Closed.OOIntAllC_outright Formalism.L2.SG.Closed.AbsConvC_outright⟩

end GlobalTheory.Core.Diag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumHeckeIdentitySplitPlaceChartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVacuum_heckeIdentity_splitPlace_charts : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ eS eT, IsSplitChart D.sp.cm.sig S.gram (frameLat S) h eS → IsSplitChart D.sp.cm.sig T.gram (frameLat T) h eT → ∀ f, VacFin ψ S T v f → (∀ k ∈ Kv S v, ∀ k' ∈ Kv T v, om (embV S v k, embV T v k') f = f) ∧ ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ k ≤ T.rank, heckeVec (((om.comp (MonoidHom.inr _ _)).comp (embV T v)).comp eT.symm.toMonoidHom) (KGL w (n := T.rank)) (fun g => Tj ℂ T.rank (Ov D.host.E w) ϖ k g⁻¹) f = ∑ j ∈ Finset.range (S.rank + 1), (if j ≤ k then (qV D.host.E w : ℂ) ^ ((S.rank - j) * (k - j)) * (Formalism.L2.Col.gaussBin (qV D.host.E w) t (k - j) : ℂ) * (((val (F := D.host.F) χS w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ S.rank)⁻¹ ^ k * (((val (F := D.host.F) χT w : ℂˣ) : ℂ) * (Real.sqrt (qV D.host.E w) : ℂ) ^ T.rank) ^ j else 0) • heckeVec (((om.comp (MonoidHom.inl _ _)).comp (embV S v)).comp eS.symm.toMonoidHom) (KGL w (n := S.rank)) (Tj ℂ S.rank (Ov D.host.E w) ϖ j) f := by
  first | exact @GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart | exact GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart | (intros; apply GlobalTheory.ChainOnto.HSplitChart.hecke_vac_split_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupHaarEqConstMulProd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Mi.BesHaar

open scoped NNReal ENNReal

noncomputable def prodEquiv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A) :
    (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) ≃ₜ*
      besGrp B.d B.o where
  toFun p := ⟨(iotaX X h).symm ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)), by
    rw [((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _), ContinuousMulEquiv.apply_symm_apply]
    exact ⟨p.1.2, p.2.2⟩⟩
  invFun s := (⟨(iotaX X h s.1).1, (((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _).1 s.2).1⟩,
    ⟨(iotaX X h s.1).2, (((GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).1 _).1 s.2).2⟩)
  left_inv p := by
    ext <;> simp
  right_inv s := by
    ext
    simp
  map_mul' p q := by
    ext
    simp only [Subgroup.coe_mul, Prod.fst_mul, Prod.snd_mul]
    rw [← map_mul]
    rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ((iotaX X h).symm.continuous.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    have hc : Continuous (fun s : besGrp B.d B.o => iotaX X h s.1) :=
      (iotaX X h).continuous.comp continuous_subtype_val
    exact ((continuous_fst.comp hc).subtype_mk _).prodMk ((continuous_snd.comp hc).subtype_mk _)

theorem iota_prodEquiv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)
    (p : Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) :
    iotaX X h (prodEquiv X h B p).1 = ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)) := by
  show iotaX X h ((iotaX X h).symm _) = _
  simp

theorem lintegral_besGrp_eq : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μSf : Measure (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))), μSf.IsHaarMeasure → SigmaFinite μSf → IsHaarOnSet X.B.I (X.SinfU u) (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) → ∃ c : ℝ, 0 < c ∧ ∀ Φ : X.B.I.GA → ENNReal, Measurable Φ → ∫⁻ s, Φ (iotaX X h s.1) ∂B.lev.μR = ENNReal.ofReal c * ∫⁻ a, ∫⁻ t, Φ (a, t.1) ∂μSf ∂(((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)) := by
  intro D X h u ψ A B μSf hSf hσf hS
  haveI := hSf
  haveI := hσf
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : LocallyCompactSpace X.B.I.GA := hR.1
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : SecondCountableTopology (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.secondCountableTopology
  haveI : LocallyCompactSpace (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hcl : IsClosed (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ B.d B.o
  haveI : LocallyCompactSpace (besGrp B.d B.o) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : B.lev.μR.IsHaarMeasure := (GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  have hSi : IsClosed ((Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u) : Subgroup X.B.I.Ginf) : Set X.B.I.Ginf) := Formalism.L2.SG.WuDecayPf.isClosed_sinfU X u
  haveI : LocallyCompactSpace (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) := hSi.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨hHaar', -, -⟩ := Formalism.L2.SG.Pf.haarOnSet_isHaar_inst X.B.I (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) hSi _ hS
  haveI := hHaar'
  have hmap := Formalism.L2.SG.Pf.map_comap_subgroup (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) hSi _ hS.2.2.1
  set μS' := (((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2)).comap ((↑) : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) → X.B.I.Ginf) with hμS'
  haveI : SigmaFinite μS' := inferInstance
  let e := GlobalTheory.Core.Mi.BesHaar.prodEquiv X h B
  haveI : LocallyCompactSpace ((Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : (B.lev.μR.map e.symm).IsHaarMeasure := e.symm.isHaarMeasure_map B.lev.μR
  haveI : (μS'.prod μSf).IsHaarMeasure := Measure.prod.instIsHaarMeasure μS' μSf
  have hcpos := Measure.haarScalarFactor_pos_of_isHaarMeasure (B.lev.μR.map e.symm) (μS'.prod μSf)
  set c : ℝ≥0 := (B.lev.μR.map e.symm).haarScalarFactor (μS'.prod μSf) with hc
  have hme : Measurable (e : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) → besGrp B.d B.o) := e.continuous.measurable
  have hEq : B.lev.μR = (c • μS'.prod μSf).map e := by
    rw [hc, ← Measure.isMulLeftInvariant_eq_smul, Measure.map_map hme (show Measurable (e.symm : besGrp B.d B.o → (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u))) from e.symm.continuous.measurable)]
    simp
  refine ⟨(c : ℝ), hcpos, fun Φ hΦ => ?_⟩
  have hv : Measurable (fun p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (measurable_subtype_coe.comp measurable_snd)
  have hΦ' : Measurable (fun p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => Φ ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf))) := hΦ.comp hv
  have hin : Measurable (fun a : X.B.I.Ginf => ∫⁻ t, Φ (a, (t : X.B.I.Gf)) ∂μSf) := by
    have : Measurable (Function.uncurry fun (a : X.B.I.Ginf) (t : Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) => Φ (a, (t : X.B.I.Gf))) :=
      hΦ.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
    exact this.lintegral_prod_right'
  have hΦι : Measurable (fun s : besGrp B.d B.o => Φ (iotaX X h s.1)) :=
    hΦ.comp ((iotaX X h).continuous.measurable.comp measurable_subtype_coe)
  rw [hEq, lintegral_map hΦι hme]
  have hιe : ∀ p : (Formalism.L2.SG.Pf.SinfSub X.B.I X.eR (X.zR u)) × (Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)), iotaX X h (e p).1 = ((p.1 : X.B.I.Ginf), (p.2 : X.B.I.Gf)) :=
    GlobalTheory.Core.Mi.BesHaar.iota_prodEquiv X h B
  simp_rw [hιe]
  rw [lintegral_smul_measure, lintegral_prod _ hΦ'.aemeasurable, ← hmap,
    lintegral_map hin measurable_subtype_coe, ENNReal.ofReal_coe_nnreal, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.Core.Mi.BesHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupUnfoldFundamentalDomain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Unfold

theorem lintegral_unfold : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ f : X.B.I.GA → ENNReal, Measurable f → ∫⁻ s, f (iotaX X h s.1) ∂B.lev.μR = ∫⁻ s in 𝓢, ∑' σ : Srat X u, f ((σ : X.B.I.GA) * iotaX X h s.1) ∂B.lev.μR := by
  intro D X h u ψ A B 𝓢 h𝓢 f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (D.sp.Y 0).gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig (D.sp.Y 0).gram
  have hH : B.lev.μR.IsHaarMeasure := (GlobalTheory.BesselQuot.besGrp_quotient D D.R.rS B.lev).1
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  have : BorelSpace X.B.I.GA := hR.2.2.2.1
  have hgrp := (GlobalTheory.Core.Mi.besGrp_eq_sGroup D X h u ψ A B).2
  have : Countable (GQ (D.sp.Y 0)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (D.sp.Y 0).gram
  have : Countable ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) := Function.Injective.countable
    (f := fun x : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o) => (⟨x.1.1, x.2⟩ : GQ (D.sp.Y 0))) fun a b e =>
      Subtype.ext (Subtype.ext (congrArg (Subtype.val : GQ (D.sp.Y 0) → GA D (D.sp.Y 0)) e))
  have : SMulInvariantMeasure ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) (besGrp B.d B.o) B.lev.μR :=
    ⟨fun γ S _ => by
      show B.lev.μR ((fun y => (γ : besGrp B.d B.o) * y) ⁻¹' S) = B.lev.μR S
      exact measure_preimage_mul _ (γ : besGrp B.d B.o) S⟩
  have hιm : Measurable (fun s : besGrp B.d B.o => f (iotaX X h s.1)) :=
    hf.comp ((iotaX X h).continuous.measurable.comp measurable_subtype_coe)
  rw [h𝓢.lintegral_eq_tsum'' (fun s => f (iotaX X h s.1))]
  rw [← lintegral_tsum (f := fun (γ : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) (x : besGrp B.d B.o) => f (iotaX X h (γ • x).1))
    (fun γ => (hιm.comp (measurable_const_smul γ)).aemeasurable)]
  refine lintegral_congr fun s => ?_
  let e : (GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o) ≃ Srat X u := Equiv.ofBijective
    (fun γ => ⟨iotaX X h γ.1.1, (hgrp _).1 ⟨Subgroup.mem_subgroupOf.1 γ.2, γ.1.2⟩⟩)
    ⟨fun a b e => Subtype.ext (Subtype.ext ((iotaX X h).injective (congrArg Subtype.val e))), fun σ => by
      have hm := (hgrp ((iotaX X h).symm σ)).2 (by simpa using σ.2)
      exact ⟨⟨⟨_, hm.2⟩, Subgroup.mem_subgroupOf.2 hm.1⟩, Subtype.ext (by simp)⟩⟩
  rw [← e.tsum_eq]
  refine tsum_congr fun γ => ?_
  show f (iotaX X h ((γ : besGrp B.d B.o) * s).1) = f (iotaX X h γ.1.1 * iotaX X h s.1)
  rw [Subgroup.coe_mul, map_mul]

end GlobalTheory.Core.Mi.Unfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Doubling GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero)

noncomputable section

namespace GlobalTheory.TwBound

theorem hgt_io_eq_prod (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (ha : IsMaj V a) (g : GA D V) (hg : g ∈ GinfC V) :
    (hgt V a (io V (g, 1)) : ℝ) = ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g) := by
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
  have hI := _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D V (frameLat V) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat V) ha
  rw [hgt, hI.hgtAd_eq (isCMExt_host D)]
  have hf : ∀ v, hgtFin D.sp.cm.sig (dblSp V).gram (frameLat V) v (proj D.sp.cm.sig (dblSp V).gram v (io V (g, 1))) = 1 := by
    intro v
    have e : proj D.sp.cm.sig (dblSp V).gram v (io V (g, 1)) = 1 := by
      rw [io, proj_ioH, mem_infPts_iff_forall.1 hg v, map_one, ioH_one]
    rw [e]
    exact hgtH_of_mem (continuous_absEv v) (isCompact_KFin v) (one_mem _)
  simp only [hf, finprod_one, mul_one, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [io, projArch_ioH, map_one]
  rfl

theorem tw_bound : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (m : Measure (WO V W)) (X : Set (WO V W)), IsCovolOne (ratL W V) m X → ∀ f, IsVacVec ψ θ M M' f → ∀ a : GL (Fin V.rank) (AE D), GlobalTheory.Doubling.IsMaj V a → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D V τ * cart M τ) * compAt θ τ a.1 = 1) → ∀ P Q, ∃ C : ℝ, ∀ g ∈ GinfC V, ‖GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q)‖ ≤ C * (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w g)) ^ ((W.rank : ℝ) / 2) := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hω m X hm f hf a ha hmaj P Q
  have hpr : GlobalTheory.Published.WeilRepresentationUnitaryPair := fun D ψ S T χS χT hψ hS hT rS rT =>
    GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hS hT rS rT
  obtain ⟨omh, homh⟩ := _root_.GlobalTheory.Core.Rk.exists_doubled_weilDatum hpr D ψ V W χS χT ω hω
  have hth := _root_.GlobalTheory.DoublingTheta.thetaClause D ψ V W χS χT ω omh hω homh
  have hco := _root_.GlobalTheory.Core.Rk.coefClause_of_thetaClause D ψ V W χS χT ω omh hω hth m X hm
  have h1 := _root_.GlobalTheory.FockVecOfVac.fock_of_vac D V W S S' M M' θ ψ hω.std hθ f hf P
  have h2 := _root_.GlobalTheory.FockVecOfVac.fock_of_vac D V W S S' M M' θ ψ hω.std hθ f hf Q
  have hS := fun τ => GlobalTheory.FrameEquiv.isCartanInv_cart_model M τ
  have hT := fun τ => GlobalTheory.FrameEquiv.isCartanInv_cart_model M' τ
  have hc := _root_.GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl D θ V (cart M) a hθ hS hmaj
  have hb := _root_.GlobalTheory.Core.Rk.FockBox.isFockVec_delta D ψ θ V W (cart M) (cart M') hω.std hθ _ _ h1 h2
  have hk := _root_.GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ (dblSp V) W 1 χT omh _ (cart M') homh hθ hc.1 hT (Khat V a) (isCompact_Khat V a) hc.2 _ hb
  have hmem := _root_.GlobalTheory.SwSecMem.swSec_mem_degPS hpr D ψ V W χT omh homh m X hm _ (hth _ _ h1.1 h2.1).1 a hk
  have hI := _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D V (frameLat V) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat V) ha
  haveI := GlobalTheory.Doubling.t2Space_adeleRing' (F := D.host.F)
  obtain ⟨C, hC⟩ := GlobalTheory.Doubling.HasIwasawa.exists_norm_le continuous_absE (isCompact_Khat V a) hI hmem
  refine ⟨C, fun g hg => ?_⟩
  have e1 := (hco _ _ h1.1 h2.1).2 g
  have e2 : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ipTh m X (ω (g, 1) (ptOf ψ θ M M' f P)) (ptOf ψ θ M M' f Q) =
      swSec V W omh m X (delta V W (ptOf ψ θ M M' f P) (ptOf ψ θ M M' f Q)) (io V (g, 1)) := by
    rw [e1]; rfl
  rw [e2, ← hgt_io_eq_prod D V a ha g hg]
  have ex : (sZero V W).re + (V.rank : ℝ) / 2 = (W.rank : ℝ) / 2 := by
    simp only [sZero, Complex.div_ofNat_re, Complex.sub_re, Complex.natCast_re]; ring
  have := hC (io V (g, 1))
  rw [ex] at this
  exact this

end GlobalTheory.TwBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticePrescribedFinitelyManySplitPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl ValuativeRel

namespace GlobalTheory.LatPresc

variable {D : D7}

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 ha
  refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun w => ?_⟩
  exact (Submodule.mem_iInf _).1 h2 ⟨w.1, fun hw => w.2 (hPQ _ hw)⟩

theorem latV_le_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) ≤ latV S L' (· = v) := by
  intro y hy
  obtain ⟨⟨ε, -, -, hεint, hεat, -⟩, hSv⟩ := _root_.GlobalTheory.FinPl.localComponents D (· = v)
  have hyv := ((hSv S).2.2.2 L y hL).1 hy
  have hoff := ((_root_.GlobalTheory.FinPl.localComponents D (· ≠ v₀)).2 S).2.2.2
  have hy₀ : y ∈ latV S L (· ≠ v₀) := by
    rw [hoff L y hL]
    refine ⟨fun i => idAt_mono (fun w hw => hw ▸ hv) (hyv.1 i), fun u _ e he => ?_⟩
    by_cases huv : u = v
    · subst huv
      exact hyv.2 u rfl e he
    · obtain ⟨⟨εu, -, -, -, hεuat, hεuoff⟩, -⟩ := _root_.GlobalTheory.FinPl.localComponents D (· = u)
      have hz : e • y = 0 := by
        funext i
        have hyi : y i ∈ idOff D (· = u) :=
          (Submodule.mem_iInf _).2 fun w =>
            (Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (hyv.1 i)).2 ⟨w.1, fun hw => huv (w.2.symm.trans hw)⟩
        change e * y i = 0
        rw [← (hεuat e).1 he.1, mul_comm εu e, mul_assoc, (hεuoff (y i)).1 hyi, mul_zero]
      rw [hz]
      exact zero_mem _
  rw [h] at hy₀
  have h2 := ((hoff L' y hL').1 hy₀).2 v hv ε hεint
  have hεy : ε • y = y := funext fun i => (hεat (y i)).1 (hyv.1 i)
  rwa [hεy] at h2

theorem latV_eq_of_off {S : HSp D} {L L' : Lat S} (hL : Submodule.IsLattice D.host.E L)
    (hL' : Submodule.IsLattice D.host.E L') {v₀ v : Pl D} (hv : v ≠ v₀)
    (h : latV S L (· ≠ v₀) = latV S L' (· ≠ v₀)) : latV S L (· = v) = latV S L' (· = v) :=
  le_antisymm (latV_le_of_off hL hL' hv h) (latV_le_of_off hL' hL hv h.symm)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLat_congr {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    {L L' : Lat S} (h : latV S L (· = p.v) = latV S L' (· = p.v)) (Λ : Submodule 𝒪[k] (n → k)) :
    β.IsLat L Λ ↔ β.IsLat L' Λ := by
  unfold Frame.IsLat
  rw [h]

theorem exists_modify {ι : Type} {p : ι → SplitPt D k} (hp : Function.Injective fun i => (p i).v) {S : HSp D} {n : Type}
    [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Λ : ι → Submodule 𝒪[k] (n → k)) (hΛ : ∀ i, (Λ i).IsFullLattice k)
    {L : Lat S} (hL : IsSelfDualC S L) (l : List ι) : ∃ M : Lat S, IsSelfDualC S M ∧ (∀ i ∈ l, (β i).IsLat M (Λ i)) ∧
      ∀ v, (∀ i ∈ l, v ≠ (p i).v) → latV S M (· = v) = latV S L (· = v) := by
  induction l with
  | nil => exact ⟨L, hL, by simp, fun _ _ => rfl⟩
  | cons i l ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨M', hM', h3, h4⟩ := _root_.GlobalTheory.FrameGlob.main D k (p i) S n (β i) M (Λ i) hM (hΛ i)
    refine ⟨M', hM', fun i' hi' => ?_, fun v hv => ?_⟩
    · by_cases e : i' = i
      · subst e; exact h3
      · have hne : (p i').v ≠ (p i).v := fun e' => e (hp e')
        exact (isLat_congr (β i') (latV_eq_of_off hM'.1 hM.1 hne h4) (Λ i')).2
          (h1 i' ((List.mem_cons.1 hi').resolve_left e))
    · exact (latV_eq_of_off hM'.1 hM.1 (hv i (List.mem_cons_self ..)) h4).trans
        (h2 v fun i' hi' => hv i' (List.mem_cons_of_mem _ hi'))

theorem latAll : ∀ D : D7, LatAll D := by
  intro D k _ _ _ _ ι p I P hP n _ _ S α L hL Λ hΛ
  obtain ⟨M, hM, h1, h2⟩ := exists_modify hP.inj α Λ hΛ hL I
  exact ⟨M, hM, fun i => h1 i (hP.all i), fun x hx => h2 x fun i _ e => hx ((hP.mem x).2 ⟨i, e⟩)⟩

end GlobalTheory.LatPresc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem lagr_eq_lagr {D : D7} (A B : HSp D) (y : WO A B) :
    GlobalTheory.SiegelFormula.lagr A B y = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B y := by
  ext i j
  obtain ⟨k | k, rfl⟩ := finSumFinEquiv.surjective j
  · simp only [GlobalTheory.SiegelFormula.lagr, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, Matrix.of_apply, pairVec_inl, Equiv.symm_apply_apply,
      Sum.elim_inl]
  · simp only [GlobalTheory.SiegelFormula.lagr, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, Matrix.of_apply, pairVec_inr, Equiv.symm_apply_apply,
      Sum.elim_inr, Pi.neg_apply]

theorem swSection_eq_swSec {D : D7} (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)) (f : WO (dblSp A) B → ℂ) :
    GlobalTheory.SiegelFormula.swSection A B ν 𝓕 ω f = swSec A B ω ν 𝓕 f := by
  funext g
  simp only [GlobalTheory.SiegelFormula.swSection, GlobalTheory.SiegelFormula.valZero, swSec, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero, lagr_eq_lagr]

theorem isHeckeCharacter_inv_of_isHeckeCharacter {D : D7} {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
    rw [this]; exact h.1.inv
  · rw [MonoidHom.inv_apply, h.2 x, inv_one]

end GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem siegelWeilAll_of_hypotheses : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    GlobalTheory.Published.SiegelWeilUnitaryConvergent → ∀ D : D7, SiegelWeilFock D := by
  intro hW hWeil hIch D ψ A B ha hab hwitt χB omh homh a hmaj θ sS sB hθ hS hB hKc ν 𝓕 hcov mH hmH φ hF
  have hφ := hF.1
  have hK := _root_.GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hB (Khat A a) (isCompact_Khat A a) hKc φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hwitt' : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
    rw [GlobalTheory.RallisIP.wittIdx_eq_wittIndex]; exact hwitt
  by_cases hb : B.rank ≤ 2 * A.rank
  · have h3 : A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank := by
      rcases hwitt' with h | h
      · rw [h]; omega
      · exact h
    exact hIch D ψ A B hab hb h3 χB omh homh a hmaj hI θ sS sB hθ hS hB hKc ν 𝓕 hcov mH hmH φ hF
  · push_neg at hb
    obtain ⟨-, hW2⟩ := hWeil D A B mH hmH ha hwitt'
    obtain ⟨hint, hser⟩ := hW2 ψ χB omh homh φ hφ
    refine ⟨hint, ?_⟩
    obtain ⟨-, -, hsum⟩ : _ ∧ _ ∧ _ := by
      obtain ⟨h1, h2⟩ := hser hb ν 𝓕 hcov
      exact ⟨h1, fun g => (h2 g).1, fun g => (h2 g).2⟩
    have hmem := _root_.GlobalTheory.SwSecMem.swSec_mem_degPS hW D ψ A B χB omh homh ν 𝓕 hcov φ hφ a hK
    have hre : (A.rank : ℝ) / 2 < (sZero A B).re := by
      have : (sZero A B).re = ((B.rank : ℝ) - A.rank) / 2 := by
        simp [sZero, Complex.div_re]
      rw [this]
      have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast hb
      linarith
    have hv := GlobalTheory.Eis.SphConv.eisValueAt_flat hI hmem (GlobalTheory.Eis.sphConv D A a hI) (isHeckeCharacter_inv_of_isHeckeCharacter homh.hecT) hre
    have he : GlobalTheory.Eis.eis A (swSec A B omh ν 𝓕 φ) = ThetaMean.thetaMean omh mH φ := by
      funext g
      rw [← swSection_eq_swSec]
      exact hsum g
    rw [he] at hv
    exact hv

end GlobalTheory.Core.Rk.IP
end

