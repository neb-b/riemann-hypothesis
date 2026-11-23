module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0232
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0126
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.RankOneOfLong
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0234
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AllCuspidalOpenBound
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0213
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SwOn
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0170
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistMemWeightOneSubspace
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.InW1TwistAtMember
theorem twist_mem_weightOne_subspace_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  intro _ _ hL
  refine GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ => ?_
  intro a
  rw [n.tie.twOf_eq a]
  exact GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice (w.D Z) nch n.tie B.coeffGaloisSubfield_isGalois _ ((w.D Z).nd.w_tw a)
end GlobalTheory.HeightCounting.InW1TwistAtMember
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzero_index_place_tw_of : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => ∀ a : (w.D Z).nd.Loc, (w.D Z).ntw.NonzeroIndexPlace ((w.D Z).ntw.twOf a) := by
  first | exact @_root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt | exact _root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt | (intros; apply _root_.GlobalTheory.HeightCounting.InW1TwistAtMember.twist_mem_weightOne_subspace_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UbcStringO
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.UbcString
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
end GlobalTheory.UbcString
theorem GlobalTheory.UbcString.ubc_string_o_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc), ∀ x ∈ ZgoodN D.nd D.naut i, ∃ P', D.naut.ptV i P' = some x ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ (B'' : Multiset ℂ) (c : ℂ), D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {c} ∧ ubc D.R.nV (D.naut.satV i P' w) = B'' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) c D.R.t ∧ ∀ a ∈ B'', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P X _ _ h7 htie i x hx
  obtain ⟨-, Sig, ⟨P', hP', hB⟩, hgood⟩ := hx
  obtain ⟨π, rfl⟩ := _root_.GlobalTheory.GoodCuspPoint.main D htie i x Sig ⟨P', hP', hB⟩ hgood
  refine ⟨P', hP', fun w hw => ?_⟩
  have hq : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hns := GlobalTheory.UbcString.not_isSplitPl_of_inert D.host w hw
  obtain ⟨hunr, hfe⟩ := hB.2.2.2.2.1 w hns
  have e1 : spehLoc D.nd D.naut ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ w =
      D.naut.locG (D.naut.tw π D.naut.etaTinv) w := by
    simp [spehLoc, D.naut.lpSum_zero, D.naut.lpTw_zero]
  have e : isoLoc D.nd D.naut (twistIso D.nd D.naut ([⟨D.R.r, π, 1⟩] ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w =
      D.naut.lpSum (D.naut.locG (D.naut.tw π D.naut.etaTinv) w)
        (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) := by
    simp only [isoLoc, twistIso, muPart, List.cons_append, List.nil_append, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, D.naut.lpSum_zero, e1]
  rw [e] at hunr hfe
  obtain ⟨ha, hb⟩ := (D.naut.unr_sum _ _).1 hunr
  have hb' : D.naut.unr ((List.range D.R.t).map (fun a : ℕ => (a : ℝ)) |>.foldr
      (fun k acc => D.naut.lpSum (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 - k)) acc) (D.naut.lpZero w)) := by
    rw [← GlobalTheory.LocalInv.list_coe]; exact hb
  have hm : D.naut.unr (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) :=
    GlobalTheory.UbcString.unr_of_foldr D.naut _ (fun k : ℝ => ((D.R.t : ℝ) - 1) / 2 - k) _ 0
      (List.mem_map.2 ⟨0, List.mem_range.2 D.R.t_odd.pos, by simp⟩) hb'
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1
    (by rw [D.naut.frobEig_card _ hm, D.naut.locG_dim] :
      Multiset.card (D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)) = 1)
  have hstr : D.naut.frobEig (spehLoc D.nd D.naut ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ w) =
      GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) c D.R.t := by
    have h := (GlobalTheory.UbcString.frobEig_foldr D.naut _ hm (fun k : ℝ => ((D.R.t : ℝ) - 1) / 2 - k)
      ((List.range D.R.t).map (fun a : ℕ => (a : ℝ)))).2
    unfold spehLoc
    rw [GlobalTheory.LocalInv.list_coe]
    refine h.trans ?_
    rw [hc]
    simp only [Multiset.map_singleton]
    rw [List.map_map, Function.comp_def, GlobalTheory.UbcString.sum_singletons (fun a : ℕ => c * ((normV w : ℕ) : ℂ) ^ ((((D.R.t : ℝ) - 1) / 2 - (a : ℝ) : ℝ) : ℂ)), GlobalTheory.DownLift.str, Multiset.range, Multiset.map_coe]
    congr 1
    refine List.map_congr_left fun k _ => ?_
    rw [hq]
    push_cast
    ring_nf
  rw [D.naut.frobEig_sum _ _ ha hb, hstr] at hfe
  refine ⟨D.naut.frobEig (D.naut.locG (D.naut.tw π D.naut.etaTinv) w), c, hc, hfe.symm, ?_⟩
  have hAut := (_root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hAF hL D P).1
  have hη : GlobalTheory.LocalInv.EtaType D.nd D.naut := by
    obtain ⟨⟨h1, -⟩, h2, -⟩ := hAut
    refine ⟨h1, fun τ z hz => ?_⟩
    rcases (h2 τ).1 with e | e <;> rw [e, Multiset.mem_singleton] at hz <;> subst hz
    · exact ⟨0, by simp⟩
    · exact ⟨-1, by push_cast; ring⟩
  have hpa := GlobalTheory.LocalInv.part_alg D.nd D.naut hη (GlobalTheory.LocalInv.weightRegular_definite D) i P' _ hB
    ⟨D.R.r, D.naut.tw π D.naut.etaTinv, 1⟩ (by simp [twistIso]) (GlobalTheory.LocalInv.r_odd D.R) odd_one
  intro α hα
  rw [← hq]
  exact ((_root_.UpperTheory.GalN.tempo' h7 D.R.r _ (GlobalTheory.LocalInv.r_odd D.R).pos hpa.1 hpa.2 w).part_tw hAut ha α hα).1.le_rpow
    (UpperTheory.GalN.one_lt_q w) (UpperTheory.GalN.half_le_r D.R)
theorem GlobalTheory.EigStrInert.str_inert_tyz : _root_.GlobalTheory.EigStrInert.strInert_tyz := by
  intro hA hL D P X hAg hconds hadm htie i hμ j hj x hx f hf y hy hy0 h hh s B hE hB w hw hinert
  obtain ⟨P', hP', hw2⟩ := _root_.GlobalTheory.UbcString.ubc_string_o_alt hA hL D P X hAg hconds hadm htie i x hx
  obtain ⟨B'', c, hc, heq, hnorm⟩ := hw2 w hinert
  have h1 := _root_.GlobalTheory.T.theta_eigen_compatibility_seventh_alt hA hL D P X hAg hconds hadm htie i hμ j hj x hx f hf y hy hy0 h hh s B hE hB w hw hinert P' hP'
  have h2 := _root_.GlobalTheory.T.good_place_split_condition_alt hA hL D P X hAg hconds hadm htie i hμ j hj w hw hinert c hc
  exact ⟨B'', by rw [h1, heq, h2], hnorm⟩
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitaryReadTrue
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC GlobalTheory.UnitaryReadTrue
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace UpperTheory.One.M
theorem unitaryRead_true_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D),
    _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → Ud.UnitaryReadS D.nbc (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro hL D T A hA j h1 h2 π
  obtain ⟨π₀, rfl⟩ := A.surj j h1 h2 π
  obtain ⟨F⟩ := _root_.GlobalTheory.FinIsoProof.finIso_nonempty D.host.E D.R.nV
  obtain ⟨U, hU⟩ := _root_.GlobalTheory.FormDictEx.exists_dict D.host.E D.R.nV F π₀
  refine ⟨U, hU.1, ?_, ?_, ?_⟩
  · intro w hw σ hσ
    obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
    obtain ⟨τ, hτ, ⟨e⟩⟩ := _root_.GlobalTheory.SplitDict.locComp_agree _ _ F π₀ U hU s σ hσ
    have h := hA j h1 h2 π₀ s τ hτ
    show _ = (T.e s.w).symm _
    have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
      unfold GlobalTheory.LocLanglands.cls
      rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
    rw [Equiv.eq_symm_apply, h, hc]
  · intro w hw hsph
    let v := GlobalTheory.SplitConjPlace.belowE (D := D) w
    have hv : NG.OverPl w v := rfl
    have hsph0 := (A.sph j h1 h2 π₀ w v hw hv).1 hsph
    obtain ⟨s, ϖ, q, hs, hq⟩ :=
      GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E w (host_unramified D.host w) (not_isSplitAt D w hw)
    obtain ⟨-, hI⟩ := _root_.UpperTheory.One.M.Sph.satAgree _ _ F π₀ U hU v w hv
    obtain ⟨⟨Dv, hDs, hDϖ⟩, hI2⟩ := hI s ϖ q hs hq
    obtain ⟨α, hα, hsat⟩ := A.sat j h1 h2 π₀ v w hv Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_dict _ _ F π₀ U hU v w hv hsph0 Dv)
    obtain ⟨α', hα', hS⟩ := hI2 Dv α hDs hDϖ hα
    refine ⟨fun w' hw' σ hσ => ?_, α', ⟨s, ϖ, q, hs, hq, hS⟩, ?_⟩
    · obtain ⟨t, rfl⟩ := exists_splitPlace_w D w' hw'
      obtain ⟨τ, hτ, ⟨e⟩⟩ := _root_.GlobalTheory.SplitDict.locComp_agree _ _ F π₀ U hU t σ hσ
      have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
        unfold GlobalTheory.LocLanglands.cls
        rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
      have := _root_.UpperTheory.One.M.New.sphGood sw hsph0 (noSplit D w v hw hv) t τ hτ
      rwa [hc] at this
    · rw [hsat]
      congr 1
      funext i
      exact (hα' i).symm
  · intro τ
    obtain ⟨b, hb, -⟩ := GlobalTheory.algWt_contragredient _ _ π₀.toAlgWt
    obtain ⟨lam, hl, hhw⟩ := _root_.GlobalTheory.WeightDict.weight_agree _ _ F π₀ U hU b hb τ
    refine ⟨lam, hl, ?_⟩
    rw [A.wt j h1 h2 π₀ b hb, A.infW j h1 h2 b τ lam.w hhw, infOf_eq_infOfWeight]
theorem cusp_read_rec_t : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → CuspReadG (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro hL D T C a P ha hP hg
  haveI := host_isCMField D.host
  have hu : (CG.mk P).IsUnitary := CsdUnitary.isUnitary_of_isCsd _ a (CG.mk P) hP
  obtain ⟨π, hπ⟩ := _root_.UpperTheory.One.M.New.cgSurj C a ha ⟨CG.mk P, hu⟩ fun w => by
    obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL D.host.E a P w
    exact (ParLawsT.cls_loc_eq_of_isLocComp hσ).symm ▸ hg w σ hσ
  refine ⟨π, (C.csd a _).2 (by rw [hπ]; exact hP), fun w σ hσ => ?_, fun τ m hm => ?_⟩
  · apply (T.e w).injective
    rw [C.loc, hπ]
    simp only [_root_.GlobalTheory.FormDict.recT_alt, Equiv.apply_symm_apply]
    exact _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ _
  · rw [C.inf, hπ]
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) hm
end UpperTheory.One.M
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitarySphericalComponentOfReading
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem unitarySphericalComponent_of_reading_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A)
      (S : Reading T), _root_.GlobalTheory.SplitRead.LawsAlt S → RowUnit S → GlobalTheory.RowSatakeBound.UnitarySphericalComponent N A := by
  intro hBZ R H what₂ N A T S hL hU i σ hσ w hw hu
  have hloc := (S i w hw).locW σ hσ
  have hsph : IsSpherical ((S i w hw).row σ).π := by
    rw [← (hL i w hw).sph _ _, ← hloc, ← T.unr]
    exact hu
  obtain ⟨α, hα⟩ := _root_.GlobalTheory.SatakeExists.main hBZ _ _ _ hsph
  have hfrob : A.frobEig (A.locW i σ w) =
      (Finset.univ.val.map fun j => (α j : ℂ)).map (·⁻¹) := by
    rw [T.frobEig w _ hu, hloc, (hL i w hw).sat _ _ α hα, Multiset.map_map]
    simp
  have h1 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w R.r (Finset.univ.val.map fun j => (α j : ℂ)) :=
    GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake H.E w R.r _ α hα (hU i w hw σ hσ)
  rw [hfrob]
  refine ⟨?_, ?_⟩
  · simpa [Multiset.map_map, Function.comp_def] using h1
  · have := GlobalTheory.RowSatakeBound.finite_residue w
    exact _root_.GlobalTheory.SatakeInv.isUnitarySatake_map_inv _ _ _ _ h1
end GlobalTheory.SplitRead
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UpperRamificationJointConditionThirdJump
section
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.JointConditionThird
theorem upper_ramification_joint_condition_third_jump_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → GlobalDatumCompatibility D' := by
  intro hL _
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ _ => ?_⟩
  refine GlobalTheory.DesignBC.jointCond_of_definite _ fun j h1 h2 => ?_
  have h := (w.st x.o.Z).B.toPre.V_posDef j h1 h2
  intro τ
  exact Or.inl (h τ)
end GlobalTheory.HeightCounting.Up.JointConditionThird
end
end
end

