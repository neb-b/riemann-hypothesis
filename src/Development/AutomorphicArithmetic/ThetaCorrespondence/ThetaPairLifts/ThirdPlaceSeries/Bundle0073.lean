module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0058
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.MeasureFailsForLargeConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1792

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParamEqUbcSatV
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.StrInert
end GlobalTheory.StrInert
theorem GlobalTheory.StrInert.param_eq_ubc_satV_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∀ P', D.naut.ptV i P' = some x → (B w).map (fun a : ℂˣ => (a : ℂ)) = ubc D.R.nV (D.naut.satV i P' w) := by
  intro hA hL D P X hX h41 h7 htie i hμ j hj x hx f hf y hy hy0 h hh s B hs hB w hw hin P' hP'
  have hv := GlobalTheory.StrInert.not_mem_badPl X.R (X.tupT (D.nd.mu i)) w hw hin
  have hns := GlobalTheory.StrInert.not_isSplitPl_of_inert D w hin
  obtain ⟨P₀, hP₀, α₀, hsat, hev⟩ := _root_.GlobalTheory.T.theta_eigen_compatibility_ninth_alt hA hL D P X hX h41 h7 htie i hμ j hj x hx f hf y hy hy0 h hh s hs w hw hin
  have hBw := hB _ hv w rfl
  rcases hBw with ⟨hsp, -⟩ | ⟨-, τ, ϖ, α, hU, hτ, hBeq, hc⟩
  · exact absurd hsp (GlobalTheory.LFun.not_isSplit_of_isInertAt hin)
  have hrank : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have key : (B w).map (fun a : ℂˣ => (a : ℂ)) = ubc (Formalism.IndefR.Links.Vc D j).rank (D.naut.satV i P₀ w) := by
    rw [hBeq, hsat]
    exact _root_.GlobalTheory.SatBcInj.bcParam_eq_ubc_of_satU_eq _ ϖ τ _ _ hU α α₀ fun d t' hd ht' => (hc d t' hd ht').symm.trans (hev τ ϖ hU hτ d t' hd ht')
  rw [key, hrank]
  have h2 := ((h41 i).2.1 P₀ P' (by rw [hP₀]; exact Option.some_ne_none x) (hP₀.trans hP'.symm)).2 w
  exact (h2 (fun hS => hns (D.nd.SQ_split i w (Or.inl hS))) (fun hQ => hns (D.nd.SQ_split i w (Or.inr hQ)))).2 hns
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PgQAllUnderInj
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.PlaceSep
variable {D : D7}
end GlobalTheory.Fam.PlaceSep
open GlobalTheory.Fam.PlaceSep in
theorem GlobalTheory.Fam.pg_qAll_under_inj_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ PP PP' : Pl D.host.E, (PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP) → (PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP') → (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  intro D L hT Gi Gl Kc Yd cX ex W hP PP PP' hPP hPP' hu
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev
  have mixed : ∀ A B : Pl D.host.E, A ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → _root_.GlobalTheory.Fam.QAllAlt W B → A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → False := by
    intro A B hA hB hAB
    obtain ⟨k, hk⟩ := (hL.Pg A).1 hA
    obtain ⟨t, ht⟩ := hB
    obtain ⟨q, hq, hqB, hne⟩ := twist_prime (hL.Q_pl t) ht
    exact not_two_primes_mem B (D.host.g_prime k) hq (hne k).symm
      (natCast_mem_of_under_eq hAB (g_mem_of_div _ hk)) hqB
  rcases hPP with h1 | h1 <;> rcases hPP' with h2 | h2
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 h1
    obtain ⟨k', hk'⟩ := (hL.Pg PP').1 h2
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with e | e
    · exact e
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) (GlobalTheory.ProjLift.not_isConjPl_of_div _ hk' hk)
  · exact (mixed PP PP' h1 h2 hu).elim
  · exact (mixed PP' PP h2 h1 hu.symm).elim
  · exact hP.sel PP PP' h1 h2 hu
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PkPlaces
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PkPlaces
theorem pk_places_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ ∅)) ∧ ∀ t, Disjoint (_root_.GlobalTheory.Fam.pk_z W).Pg ((_root_.GlobalTheory.Fam.pk_z W).Q t) ∧ (∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP')) ∧ (∃ e : AE D, IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t)) ∧ ∃ e : AE D, IsIdemSum e (∅ ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have hl : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  have hQQ : ∀ t, ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ¬ Lev.IsConjPl PP PP' :=
    fun t PP h PP' h' => ((hl.Q_pl t) PP h).2 PP' h'
  have hnc : ∀ t, ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∀ PP' ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∪ (_root_.GlobalTheory.Fam.pk_z W).Q t, ¬ Lev.IsConjPl PP PP' := by
    intro t PP h PP' h' hc
    have ha := (GlobalTheory.StepLifts.places_apart _ hl t).1
    rcases Finset.mem_union.1 h with h | h
    · exact ha PP h PP' (Finset.mem_union.1 h') hc
    · rcases Finset.mem_union.1 h' with h' | h'
      · refine ha PP' h' PP (Or.inr h) ?_
        rw [GlobalTheory.GoodPrimes.isConjPl_iff] at hc ⊢
        rw [hc, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
      · exact hQQ t PP h PP' h' hc
  refine ⟨?_, fun t => ⟨(GlobalTheory.StepLifts.places_apart _ hl t).2, ?_, ?_, ?_⟩⟩
  · rw [Finset.union_empty]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun PP h PP' h' =>
      (GlobalTheory.StepLifts.places_apart _ hl W.P.A3.A.μ0).1 PP h PP' (Or.inl h')
  · intro PP h PP' h' e
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e.symm with e' | e'
    · exact Finset.disjoint_left.1 (GlobalTheory.StepLifts.places_apart _ hl t).2 h (e' ▸ h')
    · exact (GlobalTheory.StepLifts.places_apart _ hl t).1 PP h PP' (Or.inr h') (GlobalTheory.GoodPrimes.isConjPl_iff.2 e')
  · exact GlobalTheory.CentralShift.exists_idemSum _ (hnc t)
  · rw [Finset.empty_union]
    exact GlobalTheory.CentralShift.exists_idemSum _ (hQQ t)
end GlobalTheory.PkPlaces
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtRealised
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem pt_realised_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : b.pt.RealisedCondition :=
  ⟨b.R, b.S, b.B, b.pins, b.Rr, b.recPins, rfl⟩
theorem pt_T_pb_eq_R_pb {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c) : b.pt.T.pb = b.pt.R.C.P.pb :=
  GlobalTheory.PinsFixHalf.pb_eq_of_pins b.pt.T b.pt.R.toRealDat b.pt.κ b.pt.v₀ b.pt.O b.pt.charW.base.lev b.pt.fw.laws b.pt.pins
theorem pt_realised_and_pb_eq : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), b.pt.RealisedCondition ∧ b.pt.T.pb = b.pt.R.C.P.pb :=
  fun _ _ _ b => ⟨_root_.GlobalTheory.Fc.Ind.pt_realised_alt b, _root_.GlobalTheory.Fc.Ind.pt_T_pb_eq_R_pb b⟩
end GlobalTheory.Fc.Ind
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QBaseEmpty
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BaseChain
open GlobalTheory.ChainOnto
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem cH_ne_zero_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ 0 := by
  unfold _root_.GlobalTheory.BaseChain.inverseLevelCardinality
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
theorem inverse_level_cardinality_ne_infinity (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : _root_.GlobalTheory.BaseChain.inverseLevelCardinality W ≠ ⊤ := by
  unfold _root_.GlobalTheory.BaseChain.inverseLevelCardinality
  have hpos : 0 < Nat.card (_root_.GlobalTheory.Fam.complexLevelStructure W).H := Nat.card_pos
  exact ENNReal.inv_ne_top.2 (by exact_mod_cast hpos.ne')
theorem Q_base_eq_empty (W : _root_.GlobalTheory.MiS.RealPackAlt ex) : (_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0 = ∅ :=
  Finset.eq_empty_of_forall_notMem (_root_.GlobalTheory.MiTop.not_mem_Q_base' (W := W))
theorem stageX_is_at_m (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (_ : _root_.GlobalTheory.Fam.PackageHypotheses W) : (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).Is (_root_.GlobalTheory.BaseChain.com_z W) D.R.m := by
  have lev := W.Q.charW.base.lev
  have hM := (W.Q.charW.base.models.νX W.P.A3.A.μ0)
  obtain ⟨c, hc⟩ := lev.βX
  refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_, rfl, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ ⟨c, hc⟩, hc.1,
    ⟨_, hc, fun P _ hN => ?_⟩, ⟨r_le_X, (_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0, ?_⟩, ?_, ?_⟩
  · show D.sp.X'.sig τ = _
    rw [D.X'_posDef τ, D.sp.X'_rank]; simp [sigYD, Ranks.rankY, Ranks.rankX']
  · rw [one_pow, Nat.cast_one] at hN
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hN)
  · show Lev.datY _ _ _ _ _ _ ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) _ _ _ _ = _
    rw [_root_.GlobalTheory.BaseChain.Q_base_eq_empty W]; rfl
  · exact @MeasureTheory.Measure.IsHaarMeasure.smul _ _ _ _ _ hM.1.1 _ _ (_root_.GlobalTheory.BaseChain.cH_ne_zero_alt W) (_root_.GlobalTheory.BaseChain.inverse_level_cardinality_ne_infinity W)
  · exact hM.2.mono (MeasureTheory.Measure.smul_absolutelyContinuous)
end GlobalTheory.BaseChain
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealEqOfColOK
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
theorem realEq_of_colOK_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.ColOK → RealEq f.t := by
  intro D L hT Gi Gl Kc Yd cX ex W u _ f hf j hj s s' a ha b hb φ hφ
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have hL := W.Q.charW.base.lev
  let k : Fin D.R.m := ⟨j, hj⟩
  have hexp : ∀ τ, ∃ e : ℚ, HasInfExp D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu s (j + 1)) τ e ∧
      HasInfExp D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu s' (j + 1)) τ e := by
    intro τ
    obtain ⟨n, hn, ho⟩ := hL.xi_fin s
    obtain ⟨n', hn', ho'⟩ := hL.xi_fin s'
    have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k)
      (GlobalTheory.Chain.StepVac.hasInfQ_tau ((_root_.GlobalTheory.Fam.pk_z W).C.isMu0 k).inf) τ
    exact ⟨_, GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi s) hn ho τ),
      GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi s') hn' ho' τ)⟩
  exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _ (hf.kom s j hj) (hf.kom s' j hj) hexp hexp a ha b hb φ hφ
end GlobalTheory.Fam
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecAtOfGramAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open GlobalTheory.CovTop GlobalTheory.BigTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem recAt_of_gramAt_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (hg : GramAt p i) : RecAt p i := by
  have hR := complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  have hD : (p.S false).dW i = (p.S false).D :=
    (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).dW_eq (hR.wf false) i
  have hpos : 0 < (p.S false).D := (primRows3 hp.ok hp.sep p.R p.F p.charW hp.prim).D_pos
  obtain ⟨hU, hN⟩ := _root_.GlobalTheory.FrameRead.frames_read p.R p.F false i (RealDat3.kForm_of hp.prim.unif false)
  have hn1 : (1 : ℝ) ≤ RealDat.nP p.F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hs0 : 0 < (Real.sqrt (RealDat.nP p.F.lv2 false))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by linarith))
  have hs1 : (Real.sqrt (RealDat.nP p.F.lv2 false))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hn1)
  have hli : LinearIndependent D.what₂.LL (p.R.toRealDat.bL p.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).linearIndependent.map'
      (p.R.toRealDat.WL p.F.lv2 false i).subtype (Submodule.ker_subtype _)
  have hsp : ∀ x ∈ latGood p.R.toRealDat p.F.lv2 i,
      x ∈ Submodule.span D.what₂.LL (Set.range (p.R.toRealDat.bL p.F.lv2 false i)) := by
    intro x hx
    have hxW : x ∈ p.R.toRealDat.WL p.F.lv2 false i := ⟨hx.1.2, hx.2⟩
    have e : Submodule.span D.what₂.LL (Set.range (p.R.toRealDat.bL p.F.lv2 false i)) = p.R.toRealDat.WL p.F.lv2 false i := by
      have := (Module.finBasis D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)).span_eq
      have h2 := congrArg (Submodule.map (p.R.toRealDat.WL p.F.lv2 false i).subtype) this
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h2
      exact h2
    rw [e]; exact hxW
  have key := _root_.GlobalTheory.CovolCore.lcv_div_le_neg_slope_sq D.what₂.LL _ (nrmR p.R.toRealDat i) hg.1 (latGood p.R.toRealDat p.F.lv2 i) _ (show 0 < (p.S false).dW i from hD.symm ▸ hpos)
    (p.R.toRealDat.bL p.F.lv2 false i) hli hsp ((p.S false).XW i) _ hs0 hs1 hU hN (by first | exact hp.prim.mLat i | exact (hp.prim.mLat i).toIsLattice)
  unfold RecAt
  rw [← hD]
  exact key
theorem liftRecursive_of_gram : _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.LiftRecursive := fun h =>
  Closed.imp h fun _ _ _ ⟨C, hC, x0, h⟩ =>
    ⟨C, hC, x0, fun x hx hle ι p hp i => _root_.GlobalTheory.CovTop.recAt_of_gramAt_alt p i hp.1 (h x hx hle ι p hp i)⟩
end GlobalTheory.CovTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.RefSum
section Free
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ} [Fact p.Prime]
end Free
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
def SumPtAlt : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → SumAt p i PP C u1
def ReferenceCore : Prop := _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 →
  RefAt p i (p.T.U ((i : ℕ) + 1)) (GOf p i u1) PP C
def ReferenceTheta : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (GOf p i u1) PP C
def ReferenceWeight : Prop := _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (wtOf (dat p i) u1 0) PP C
end GlobalTheory.RefSum
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ResSEqOfFlag
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.unitaryCongruence
open scoped Matrix
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped Matrix
end GlobalTheory.CongFlag
namespace GlobalTheory.CongFlag
theorem resS_eq_of_flag_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ (u u' : D.what₂.Word) (κ : GA D (D.sp.Y 0)), κ ∈ rowJ W.S.X W.Q.instEq → ∀ (c c₂ : Formalism.IndefR.Lev.EAf D) (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hc₂ : c₂ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg, (∀ ei : AE D, Formalism.L2.NTheta.IsIdemAt ei PP → toEAf D ei • (c • Matrix.mulVec (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from κ)).val (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u'))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u' (Fin.cast (rank_eq W.S.X W.Q.instEq) r)))))) = toEAf D ei • (c₂ • (Matrix.mulVec (((Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))))⁻¹ : GL (Fin (Yc D 0).rank) (Formalism.IndefR.Lev.EAf D)).val (fun r => algebraMap D.host.E (Formalism.IndefR.Lev.EAf D) (W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))))))) → Formalism.L2.DIV.resS D.host.F PP ⟨c, hc⟩ = Formalism.L2.DIV.resS D.host.F PP ⟨c₂, hc₂⟩ := by
  intro D L hT Gi Gl Kc Yd cX ex W hP _ u u' κ hκ c c₂ hc hc₂ PP hPP hEq
  have lev : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hP.bot.hyp.2.2.2.1.lev
  have hPP' : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg := hPP
  have hg := (GlobalTheory.SeeConjRead.places_over_g (_root_.GlobalTheory.Fam.pk_z W) lev).1 PP hPP'
  obtain ⟨ei, hei⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt (GlobalTheory.TypePlaces.not_isConjPl _ _ lev.Pg PP hPP' PP hPP')
  obtain ⟨hε, hε1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D ei PP hei
  exact finiteRing_sq_sub_mul_sq_eq_of_card W.S.X W.Q.instEq hP.bot.idE u u' κ hκ c c₂ hc hc₂ PP hg (toEAf D ei) hε hε1 (hEq ei hei)
end GlobalTheory.CongFlag
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBig
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn
  GlobalTheory.ExpTie
namespace GlobalTheory.ExpTie
theorem rows_big_alt : _root_.GlobalTheory.BigOn.AtPtsAlt fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ X' A : ℝ,
    Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (GlobalTheory.ExpTie.parOf (Fm.L x i) j) X' A ∧
      Formalism.CohomologicalDescent.LargeParameterEstimates.Big (GlobalTheory.ExpTie.parOf (Fm.L x i) j).L (GlobalTheory.ExpTie.parOf (Fm.L x i) j).x X' A := by
  refine ⟨1, one_pos, fun eps heps _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ?_⟩⟩
  obtain ⟨x0, hx0⟩ := Formalism.CohomologicalDescent.LargeParameterEstimates.eventually_large_parameter_bound eps (2 * |Fm.Ct| + 2) heps
  refine ⟨max x0 2, fun x hx hle i _ _ _ j => ?_⟩
  have hCt := Fm.Ct_eq x i
  refine ⟨(Fm.L x i).sc.X', x ^ (2 * |Fm.Ct| + 2),
    rows_big_of_largeParameter (Fm.L x i) (Fm.params x hx i) j eps _ x (Fm.L_x x i hx) (Fm.L_eps x i) ?_ ?_
      ((le_max_right _ _).trans hle) (hx0 x ((le_max_left _ _).trans hle))⟩
  · rw [hCt]
    linarith [le_abs_self Fm.Ct]
  · rw [hCt]
    linarith [le_abs_self Fm.Ct, abs_nonneg Fm.Ct]
end GlobalTheory.ExpTie
end
end
end

