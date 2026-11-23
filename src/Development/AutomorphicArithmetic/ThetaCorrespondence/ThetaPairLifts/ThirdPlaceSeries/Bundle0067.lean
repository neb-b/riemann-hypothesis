module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1903
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0391
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JumpSetDistinctOfRealPlaceFacts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0063

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefCaseCore
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefCore
theorem defCase_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → DefCase (p.T.U ((i : ℕ) + 1)) (xiR D) ∧ Finite (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ Nonempty (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ (∀ σ, GoodEmb p.T.Q.c σ → ∀ g, (p.T.dict ((i : ℕ) + 1) σ g).2 ∈ ((p.T.U ((i : ℕ) + 1) σ).X (p.T.dict ((i : ℕ) + 1) σ g).1).dom) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M _ hm _ hW _ hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  obtain ⟨hp, hq, hr⟩ := hW.sig
  have hk := D.R.m_add_three_le_k
  have hq0 : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [hq]; rfl
    simpa [dat, hm] using this
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by
    have : (dat p i).p = D.R.k + ((i : ℕ) + 1) - 1 := by rw [hp]; rfl
    simp only [dat] at this
    omega
  refine ⟨⟨hq0, hp1, ?_, hJ.pins.2.1.2, hF, hJ.unf _ hj, ?_⟩, CompFin.finite_comp _ _, ?_, ?_⟩
  · exact goodAt_of_two_primes hJ.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  · exact (GlobalTheory.LevGeo.laws_core D p.T _ hJ hj).xiAbs
  · exact (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ _ _ (by omega)).1
  · intro σ hσ g
    exact GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.dict_mem_dom p.T hJ _ hj σ hσ g
end GlobalTheory.DefCore
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EqOneOfLevCong
section
set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BaseLevelInj
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR
end GlobalTheory.BaseLevelInj
set_option maxHeartbeats 1000000 in
open GlobalTheory.BaseLevelInj in
theorem GlobalTheory.BaseLevelInj.eq_one_of_lev_sub_mem_Mb : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (Xo := (p.T.Q.Xo ((i : ℕ) + 1))) (c := p.T.Q.c) → ∀ g : (p.F.lv2.lvl false).P, (∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev (g : p.P.Gp) x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) → g = 1 := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hi hG hW hH hF g hg
  obtain ⟨κ, hlift, happ⟩ := (p.pins i).2.lift.lev (g : p.P.Gp)
  have hβ := p.charW.base.lev.βW i
  have hSt := Formalism.L2.DIV.parLev_St hlift.2.1
  have hfc := GlobalTheory.LevelAction.finCong_of_mem_St hβ hSt
  have hι := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hMb : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb := by
    have h0 : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← p.T.Q.l.prod] at h0
    exact (Ideal.mul_le_inf.trans inf_le_left : p.T.Q.l.Mb * _ ≤ p.T.Q.l.Mb) h0
  have h4 := _root_.GlobalTheory.LevelMoveCong.mulVec_sub_mem_hat_smul (Wc D i) (iotaW p.T i) hι p.T.Q.l.M p.T.Q.l.Mb (Mfr p.T.Q.l) p.T.Q.l.coprime hMb κ hfc
    ((p.O i).lev (g : p.P.Gp)) happ hg
  have h3 := _root_.GlobalTheory.CovolCong.cong_latC_of_cong_latG (Wc D i) _ _ h4
  rw [← GlobalTheory.PrincInLevel.eq_latC hβ] at h3
  have h2 := hatL_cong_of_hat (Wc D i) κ _ _ h3
  have hfr : Formalism.L2.DIV.IsFrame (p.R.βW i) (p.R.ΛW i) := by obtain ⟨c, h, -⟩ := hβ; exact h
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hred : ∀ PP ∈ p.R.Pg, Formalism.L2.DIV.redFn (p.R.βW i) PP (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    intro PP hP
    refine GlobalTheory.T.frameReduction_eq_one_of_congruent_mod_ideal _ _ _ hfr hSt _ h2 PP ?_
    rw [hhalf]
    exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
  have hT1 : Formalism.L2.DIV.rTup (p.R.βW i) (p.R.datWp i p.R.triv) (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (p.R.βW i) PP.1 _) = 1
    rw [hred PP.1 PP.2]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  have he : p.R.eG (g : p.P.Gp) = 1 := by rw [← hlift.2.2]; exact hT1
  have : (g : p.P.Gp) = 1 := by rw [← map_one p.R.eG] at he; exact p.R.eG.injective he
  exact Subtype.ext this
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EtaCharUnramAt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.TupChars
section Loc
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Loc
section Pack
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex}
theorem under_ne_alt (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (t : W.P.T) {PP P' : Formalism.L2.DIV.Pl D.host.E} (hPg : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hQ : P' ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t) :
    P'.under (𝓞 D.host.F) ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
  intro heq
  have hL := hP.bot.hyp.2.2.2.1.lev
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPg
  obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t P' hQ
  have hmemK : ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (PP.under (𝓞 D.host.K)).asIdeal := by
    have h := (_root_.GlobalTheory.Fam.pk_z W).C.P.pb_over k
    have hk' : PP.under (𝓞 D.host.K) = (_root_.GlobalTheory.Fam.pk_z W).C.P.pb k := hk
    rw [hk']; exact h
  have hmemE : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := hmemK
    simpa using h2
  have hmemF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ PP.asIdeal
    simpa using hmemE
  rw [← heq] at hmemF
  have hmemE' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal := by
    have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ P'.asIdeal := hmemF
    simpa using h2
  haveI : Finite (kP P') := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  have : P'.asIdeal.IsPrime := P'.isPrime
  haveI : Nontrivial (kP P') := inferInstance
  haveI : Fintype (kP P') := Fintype.ofFinite _
  have h0g : ((D.host.g k : ℕ) : kP P') = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem (I := P'.asIdeal)).2 hmemE'
    simpa using this
  have h0q : ((q : ℕ) : kP P') = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero (kP P')
  have hd1 : ringChar (kP P') ∣ D.host.g k := ringChar.dvd h0g
  have hd2 : ringChar (kP P') ∣ q := ringChar.dvd h0q
  have hcop : Nat.Coprime q (D.host.g k) := (Nat.coprime_primes hq (D.host.g_prime k)).2 (hne k)
  have h1 : ringChar (kP P') = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  exact CharP.ringChar_ne_one h1
theorem charUnramAt_xi_under (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (t : W.P.T) {PP : Formalism.L2.DIV.Pl D.host.E} (hPg : PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  have hL := hP.bot.hyp.2.2.2.1.lev
  refine GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w hw => ?_
  refine (GlobalTheory.LFun.unrAt_iff_of_chrEq (hL.xi t) w).2 ?_
  by_contra hu
  rcases (hL.Q_ram t w).1 hu with h | ⟨P', hP', hc⟩
  · exact _root_.GlobalTheory.TupChars.under_ne_alt hP t hPg h hw
  · exact _root_.GlobalTheory.TupChars.under_ne_alt hP t hPg hP' ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc).trans hw)
theorem charUnramAt_eta (hP : _root_.GlobalTheory.Fam.PackageHypotheses W) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (_root_.GlobalTheory.Fam.pk_z W).eta v := by
  have hL := hP.bot.hyp.2.2.2.1.lev
  exact GlobalTheory.SeeSaw.LevelTest.charUnramAt_of fun w _ => (GlobalTheory.LFun.unrAt_iff_of_chrEq hL.eta w).2 ((_root_.GlobalTheory.Fam.pk_z W).C.isEta.unr w)
end Pack
theorem gLoc_chars_of_gRead : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c), f.RowOK → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ t (n : ℕ) (G : Fin n → GLoc v) pl, _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ i, (G i).Chars (f.t t) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR _ t n G pl hG i
  have hq : (G i).q.v = (pl i).1.under (𝓞 D.host.F) := (hG.idem i).2
  have hxi : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t) (G i).q.v := hq ▸ _root_.GlobalTheory.TupChars.charUnramAt_xi_under hP t (pl i).2
  have heta : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D (_root_.GlobalTheory.Fam.pk_z W).eta (G i).q.v := _root_.GlobalTheory.TupChars.charUnramAt_eta hP _
  let M : ℕ → (AE D)ˣ →* Circle := (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t
  let μ : ℕ → (G i).kˣ →* ℂˣ := fun m =>
    if 1 ≤ m ∧ m ≤ D.R.m then cmp (G i).q ((Lift.chrStep M (_root_.GlobalTheory.Fam.pk_z W).eta m).1⁻¹) else (G i).S.μ m
  have hμ : ∀ m, 1 ≤ m → m ≤ D.R.m → μ m = cmp (G i).q ((Lift.chrStep M (_root_.GlobalTheory.Fam.pk_z W).eta m).1⁻¹) :=
    fun m h1 h2 => if_pos ⟨h1, h2⟩
  have hunit : ∀ m (x : (G i).kˣ), valuation (G i).k (x : (G i).k) = 1 → μ m x = (G i).S.μ m x := by
    intro m x hx
    by_cases hm : 1 ≤ m ∧ m ≤ D.R.m
    · rw [hμ m hm.1 hm.2]
      apply Units.ext
      rw [cmp_apply, hG.mu i m hm.1 hm.2 x (GlobalTheory.LocChar.unitsHom (ofSplit (G i).q) x) rfl]
      have hx1 := unit_trivial (G i).q hxi x hx
      have e : (Lift.chrStep M (_root_.GlobalTheory.Fam.pk_z W).eta m).1 = (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta m).1 * (_root_.GlobalTheory.Fam.pk_z W).toLevCh.xi t := by
        simp only [Lift.chrStep, M, LevCh.mu, Lift.tup]
        split_ifs
        · exact mul_right_comm _ _ _
        · rfl
      rw [MonoidHom.inv_apply, MonoidHom.inv_apply, e, MonoidHom.mul_apply, hx1, mul_one]
    · simp only [μ, if_neg hm]
  have htame : ∀ m, GlobalTheory.SplitWeil.IsTame (μ m) := by
    intro m x hx
    rw [hunit m x (val_eq_one_of_sub x hx)]
    exact (G i).S.tame m x hx
  have hm2 : Even D.R.m := D.R.m_even
  refine ⟨μ, htame, hunit, fun j ρ h => ?_, fun j σ h => ?_⟩
  · obtain ⟨-, -, hV, hW⟩ := (hR.row t).sBF j ρ h
    have hV' : ((f.t t).sBF j ρ h).χV = M (j + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ := hV
    have hW' : ((f.t t).sBF j ρ h).χW = M (j + 1) := hW
    have hodd : Odd (j + 1) := by
      obtain ⟨r, hr⟩ := hm2
      exact ⟨j / 2, by omega⟩
    have hμj : μ (j + 1) = cmp (G i).q ((M (j + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹)⁻¹) := by
      rw [hμ (j + 1) (by omega) (by omega)]
      simp only [Lift.chrStep, if_pos hodd]
    rw [hV', hW', hμj]
    refine ⟨isComp_cmp _ _, cmp (G i).q (M (j + 1)), isComp_cmp _ _, fun x hx => ?_⟩
    apply Units.ext
    rw [Units.val_mul, cmp_apply, cmp_apply, Units.val_one, ← Circle.coe_mul, ← MonoidHom.mul_apply]
    have e : M (j + 1) * (M (j + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹)⁻¹ = (_root_.GlobalTheory.Fam.pk_z W).eta := by
      rw [_root_.mul_inv_rev, inv_inv, mul_comm, mul_assoc, inv_mul_cancel, mul_one]
    rw [e, unit_trivial (G i).q heta x hx, Circle.coe_one]
  · obtain ⟨-, -, hV, hW⟩ := (hR.row t).sFB j σ h
    have hV' : ((f.t t).sFB j σ h).χV = M (j + 1 + 1) := hV
    have hW' : ((f.t t).sFB j σ h).χW = M (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ := hW
    have heven : ¬ Odd (j + 1 + 1) := by
      obtain ⟨r, hr⟩ := hm2
      rw [Nat.not_odd_iff_even]
      exact ⟨j / 2 + 1, by omega⟩
    have hμj : μ (j + 1 + 1) = cmp (G i).q (M (j + 1 + 1))⁻¹ := by
      rw [hμ (j + 1 + 1) (by omega) (by omega)]
      simp only [Lift.chrStep, if_neg heven]
    rw [hV', hW', hμj]
    refine ⟨isComp_cmp _ _, cmp (G i).q (M (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹), isComp_cmp _ _, fun x hx => ?_⟩
    apply Units.ext
    rw [Units.val_mul, cmp_apply, cmp_apply, Units.val_one, ← Circle.coe_mul, ← MonoidHom.mul_apply]
    have e : M (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ * (M (j + 1 + 1))⁻¹ = (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ := by
      rw [mul_right_comm, mul_inv_cancel, one_mul]
    rw [e, MonoidHom.inv_apply, unit_trivial (G i).q heta x hx, inv_one, Circle.coe_one]
end GlobalTheory.TupChars
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvWCOnPtOfGuarded
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
namespace GlobalTheory.Fc.Ind
theorem evWC_onPt_of_guarded_alt (prem : ∀ {eps : ℝ}, FamP eps → Prop) (G : PtP) (T : ℝ → ℝ → PtP)
    (h : Closed FamHyp fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p =>
      G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p)
    (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜) (hd : ∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm)
    (hR : EvW _root_.GlobalTheory.Fc.Ind.RowPointSummands 𝒜 σ) (hG : EvW (_root_.GlobalTheory.Fc.Ind.conditionOnPoint G) 𝒜 σ) : EvWC prem (fun C CH => _root_.GlobalTheory.Fc.Ind.conditionOnPoint (T C CH)) 𝒜 σ := by
  have h' : Closed (W3 𝒜) fun Fm CH => prem Fm → ∃ C0 : ℝ, 0 ≤ C0 ∧ _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p =>
      G _ (objAt Fm x hx i) _ p → ∀ C, C0 ≤ C → T C CH _ (objAt Fm x hx i) _ p := by
    obtain ⟨a, ha, h⟩ := h
    refine ⟨a, ha, fun e he hle => ?_⟩
    obtain ⟨K, hK⟩ := h e he hle
    exact ⟨K, fun Fm CH hc hL => hK Fm CH (_root_.GlobalTheory.BigTop.famHyp_of_working_duty 𝒜 _ Fm hc (hd _ Fm (w3_a hc))) hL⟩
  refine Closed.imp (Closed.and h' (Closed.and hR hG)) ?_
  rintro eps Fm CH - ⟨h1, h2, h3⟩ hc hp
  obtain ⟨C0, hC0, a, ha⟩ := h1 hp
  obtain ⟨b, hb⟩ := h2 hc
  obtain ⟨c, hc'⟩ := h3 hc
  refine ⟨C0, hC0, fun C hC => ⟨max a (max b c), fun x hx hle i => ?_⟩⟩
  have e1 : a ≤ x := (le_max_left _ _).trans hle
  have e2 : b ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have e3 : c ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  exact ha x hx e1 i (σ Fm (w3_a hc) x hx i).pt (hb x hx e2 i) (hc' x hx e3 i) C hC
end GlobalTheory.Fc.Ind
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactAtOfRows
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
noncomputable section
namespace GlobalTheory.CovTop.MeasRd
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
end GlobalTheory.CovTop.MeasRd
namespace GlobalTheory.CovTop.MeasRd
open GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes in
theorem exactAt_of_rows_alt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz)
    (hp : p.PointConditions') (hM : OneMeasure D) (i : Fin D.R.m) : ExactAt p i := by
  intro σ f
  have hTau : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have hk : p.κ = kapTop D := KapIs.eq (κ := p.κ) p.fw.kap hTau
  have ha : wtA (p.κ i) = wtA (kapTop D i) := by rw [hk]
  have hn : (p.κ i).n = (kapTop D i).n := by rw [hk]
  have hG : Gk p i = GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i := by unfold Gk GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW; rw [hk]
  obtain ⟨-, hd, h2⟩ := hM _ p.R.toRealDat.toLevCh _ p.charW.base.lev i p.R.toRealDat.triv
  have hmod := p.charW.base.models
  obtain ⟨h0, ht, he, -⟩ := h2 _ _ (hmod.νW i)
  obtain ⟨s, hs_def⟩ : ∃ s, s = sgAt D.what₂.embLL (InfinitePlace.mk σ) := ⟨_, rfl⟩
  have hs := sgAt_mk_eq D.what₂.embLL σ
  rw [← hs_def] at hs
  show ‖(p.R.toRealDat.FW i).j (sgAt D.what₂.embLL (InfinitePlace.mk σ)) _‖ = _
  rw [← hs_def]
  have hgd : goodOf p.T.Q.c (res p.T s) = goodOf p.T.Q.c (res p.T σ) := by
    rcases hs with h | h
    · rw [h]
    · rw [h]; exact GlobalTheory.CompHt.goodOf_conj (c := p.T.Q.c) (res p.T σ)
  have hgood := goodEmb_goodOf p.T.Q.c (res p.T s)
  have hV : p.T.V ((i : ℕ) + 1) (gd p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgood
  obtain ⟨-, hrange, hip⟩ := hmod.HW i s
  by_cases hf0 : f = 0
  · subst hf0
    have hy : ((p.fw.e i 0 : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) = 0 := by
      rw [map_zero]; rfl
    have hz := petW_smul (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
      (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) 0 0
    rw [map_zero, norm_zero, zero_mul, zero_smul] at hz
    rw [hy, map_zero, norm_zero, ZeroMemClass.coe_zero, hz, mul_zero]
  set y : Fin (p.R.toRealDat.nW i) → D.what₂.LL := ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    with hy
  have hy0 : y ≠ 0 := fun h => hf0 ((p.fw.e i).map_eq_zero_iff.1 (Subtype.ext h))
  set x := (p.R.toRealDat.FW i).j s y with hx_def
  have hx : (p.R.toRealDat.HW i s).e x ∈ p.R.toRealDat.Wall i s := hrange ▸ LinearMap.mem_range_self _ x
  set f' := rdU (p.T.U ((i : ℕ) + 1) (gd p.T s)) (f : p.T.R ((i : ℕ) + 1)) with hf'_def
  have hf' : f' ∈ scalarForms p.T i (gd p.T s) := by
    have := ((mem_cusp _ _ _ _ _ _).1 f.2).2 _ hgood
    show f' ∈ holSub _ (modelWt _ (wtZ (wtA (kapTop D i)) (kapTop D i).n))
    rw [modelWt_wtZ, ← ha, ← hn]
    exact this
  have hc : Corr p.T i s hV ((p.R.toRealDat.HW i s).e x) f' := by
    by_cases hgs : GoodEmb p.T.Q.c (res p.T s)
    · have hgd' : gd p.T s = res p.T s := by show goodOf _ _ = _; rw [goodOf, if_pos hgs]
      have hV' : p.T.V ((i : ℕ) + 1) (res p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ hgs
      have hpre : ∃ j' : (Fin (p.R.toRealDat.nW i) → D.what₂.LL) →ₛₗ[s] (p.R.toRealDat.HW i s).H,
          ∀ g : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n,
            ((p.R.toRealDat.HW i s).e (j' ((p.fw.e i g : (p.R.toRealDat.FW i).WK) :
              Fin (p.R.toRealDat.nW i) → D.what₂.LL))) (p.v₀ i s) =
              hV' ▸ p.T.phiJ ((i : ℕ) + 1) (res p.T s) (wtA (p.κ i)) (g : p.T.R ((i : ℕ) + 1)) := by
        by_contra hne
        have hj0 := p.fw.ev0 i s hgs hV' hne
        have hli := (hp.prim.unif i s).1 1 (fun _ => y) (linearIndependent_unique_iff.2 hy0)
        rw [hj0] at hli
        exact hli.ne_zero 0 (LinearMap.zero_apply _)
      refine Or.inl ⟨hgs, p.v₀ i s, (p.fw.hv₀ i s).1, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (p.fw.ev i s hgs hV' hpre f).trans ?_
      show phiC p.T hV' (wtA (p.κ i)) _ = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha]
      exact phiC_congr hgd'.symm _ _ _ _
    · have hgd' : gd p.T s = resC p.T s := by show goodOf _ _ = _; rw [goodOf, if_neg hgs]
      have hVc : p.T.V ((i : ℕ) + 1) (resC p.T s) = Wc D i := p.fw.laws.spaceW _ (inR i) _ (good_resC p.T hgs)
      obtain ⟨v, hv, hvf⟩ := (p.bar i s hgs hVc).1 (hp.jEvBar i s hgs hVc)
      refine Or.inr ⟨hgs, v, hv, ?_⟩
      rw [hf'_def, adFun_rdU]
      refine (hvf f).trans (funext fun g => ?_)
      show starRingEnd ℂ (phiC p.T hVc (wtA (p.κ i)) _ g) = _
      generalize (f : p.T.R ((i : ℕ) + 1)) = F0
      rw [ha, phiC_congr hgd' hV hVc]
  have e := (he p.T p.fw.laws p.fw.alg_eq p.R.toRealDat.θ hmod.inf s (p.R.toRealDat.MW i s) hV _ hx f' hf' hc).2
  rw [← hip, inner_self_eq_norm_sq_to_K] at e
  have e' : ‖x‖ ^ 2 = ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i) * probSq p.T i (gd p.T s) f' := by
    have : (((‖x‖ ^ 2 : ℝ)) : ℂ) = _ := (Complex.ofReal_pow _ _).trans e
    exact_mod_cast this
  rw [hf'_def, probSq_rdU] at e'
  unfold petW
  rw [← hgd, hG, ← Real.sqrt_sq (norm_nonneg x), e', Real.sqrt_mul' _ (sq_nonneg _),
    Real.sqrt_sq (petAt_nonneg _ _ _ _ _ _ _)]
  rfl
end GlobalTheory.CovTop.MeasRd
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactRanksAlongTiedFamily
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem exact_ranks_along_tied_family_alt : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (eps : ℝ) (Fm : FamP eps), _root_.Formalism.L2.TwistSelectionFunctions Fm →
    ∀ C0 Cg cb Cu cT CT : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT := by
  intro hU eps Fm s C0 Cg cb Cu cT CT
  refine ⟨max s.1 (Fm.x1 + 1), fun x hx i hh => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hx)
  have R := s.2 x hx1 (le_trans (le_max_left _ _) hx) i
  have hr := R.T.theta.real
  have hm : ∀ u, StandardLattice.Mu0Tie (Fm.D x i) u := _root_.GlobalTheory.mu0Tie_of_colsTiedSym _ R.T.cols
  have h4f : StandardLattice.Conclusion4f (Fm.D x i) (Fm.ex x hx1 i).lev :=
    StandardLattice.HarishChandraReduction.rankFormula_of_classNumber _ _ (ColClassNumber.classNumber_all _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, h0, h1, -⟩ := hh.1
  have hS : ∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j) :=
    Fin.forall_fin_two.2 ⟨RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 0) h0,
      RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 1) h1⟩
  exact exact_ranks_of_record (Fm.D x i) hS (RankVolume.definiteSpaceVolume_eq_mass_of_volumeComparison (fun D => hU D) _ hr)
    (StandardLattice.factDstar_fam Fm x hx1 i)
    (fun u => h4f (first_type_prime_large_of_record _) hS u
      (RankSplit.splitsF_of_norm _ _ ((Fm.D x i).mem u).A.T_prime (hT u).1) (hm u))
end GlobalTheory
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSelfDualLatY
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SDLatY
theorem exists_selfDual_latY_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j, j < D.R.m → ∃ L : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) L := by
  intro D L hT Gi Gl Kc Yd cX ex W hp j hj
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  exact ⟨(_root_.GlobalTheory.Fam.pk_z W).ΛY j, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D (Yc D j) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) _ (hC.lev.βY j hj)⟩
end GlobalTheory.SDLatY
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HoldsAll
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.JumpStatement
theorem holds_all_alt : ∀ D : D7, _root_.Formalism.MainNotions.AdmissibleParameterJ.JumpClosed D := _root_.GlobalTheory.JumpSets.stmtJ_holds_alt
end GlobalTheory.JumpStatement
end
end

