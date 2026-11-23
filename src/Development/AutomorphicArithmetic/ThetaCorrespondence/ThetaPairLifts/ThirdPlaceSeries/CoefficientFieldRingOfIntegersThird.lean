module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0680
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0232
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0114
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0021
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0249
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0126
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0156
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0239
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDivisorEigenIndexThirdComponent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0174
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0246
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0142
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0225
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
set_option maxHeartbeats 4000000 in
theorem third_place_fixed_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ)
    (L : LocAll (lay0 (Dof x))) (hB : _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L) :
    ∃ Q : _root_.GlobalTheory.NPin.CharacterChoiceData hL (withLoc L), Q.cf = cfL L (cfOf x) ∧ Q.C = chL L l.c.ch ∧ HEq Q.tp (tpL L l.c.tp) ∧
      HEq Q.rep (repOf x.r.Y) ∧ HEq Q.M (mtL L l.mt.M) := by
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hB
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have key : ∀ (xi : (Dof x).what₂.Tup → HChar (Dof x).host.E) (Q : (Dof x).what₂.places.Pl → Finset (PlE (Dof x).host)),
        MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * xi μ) Q → l.c.tp.xi = xi → l.c.ch.Q = Q →
          MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
      intro xi Q h hx hQ
      subst hx hQ
      exact h
    exact key _ _ l.mt.mt l.c.xi_eq l.c.Q_eq
  let nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) := by
    with_unfolding_all
      exact
        { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
          low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
          M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := hmt, big := big, L := L, Sp := Sp, Au := Au, ss := ss,
          eq := rfl, pack := rfl }
  have hval : ValLL0 (withLoc L) (cfL L (cfOf x)) := by
    with_unfolding_all exact ⟨l.a.val.mu0, l.a.val.eta, l.a.val.chiPsi, l.a.val.del, l.a.val.del'⟩
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.NPin.exists_character_choice_of_nTrue_split hL _ _ _ _ nt hval
    (fun σ σ' h => x.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) l.a.elem.star l.a.elem.int l.a.elem.split
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
  exact ⟨Q, h1, h2, h3, h4, h5⟩
end GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
namespace GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
open GlobalTheory.HeightCounting.Fin3 GlobalTheory.HeightCounting.Up.RealOfReading
set_option maxHeartbeats 4000000 in
theorem readCoefField_eq_cfL_of_moved_copy_coherent : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), _root_.GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → m.z.R.C = cfD x L := by
  intro hL _ _
  refine StepW.of_all fun K B f T w _ _ _ P x l big L hB hO m _ _ s r _ => ?_
  exact m.z.lev.C

-- Compare the data fields after identifying the stage indices.
private theorem mtReal_heq {D D' : D7} (hD : D = D')
    {μ : D.what₂.Tup} {μ' : D'.what₂.Tup} (hμ : HEq μ μ') {j : ℕ}
    {m : MtReal D μ j} {m' : MtReal D' μ' j}
    (hw : HEq m.wt m'.wt) (hJ : HEq m.J m'.J) (hχ : HEq m.χ m'.χ)
    (hr : HEq m.real m'.real) : HEq m m' := by
  cases hD
  obtain rfl := eq_of_heq hμ
  cases m
  cases m'
  dsimp only at hw hJ hχ hr
  obtain rfl := eq_of_heq hw
  obtain rfl := eq_of_heq hJ
  obtain rfl := eq_of_heq hχ
  obtain rfl := eq_of_heq hr
  rfl

private theorem charFrame_heq {D D' : D7} (hD : D = D')
    {c : CharFrame D} {c' : CharFrame D'}
    (hP : HEq c.P c'.P) (hW : HEq c.W c'.W) (hμ : HEq c.mu0 c'.mu0)
    (hη : HEq c.eta c'.eta) (hχ : HEq c.chiPsi c'.chiPsi)
    (hδ : HEq c.del c'.del) (hδ' : HEq c.del' c'.del') : HEq c c' := by
  cases hD
  cases c
  cases c'
  dsimp only at hP hW hμ hη hχ hδ hδ'
  obtain rfl := eq_of_heq hP
  obtain rfl := eq_of_heq hW
  obtain rfl := eq_of_heq hμ
  obtain rfl := eq_of_heq hη
  obtain rfl := eq_of_heq hχ
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hδ'
  rfl

private theorem nChoice_heq {D D' : D7} (hD : D = D')
    {c : NChoice D} {c' : NChoice D'}
    (hTw : HEq c.twI c'.twI) (hsd : HEq c.sd c'.sd) (hQ : HEq c.Q c'.Q)
    (hk : HEq c.k' c'.k') (hψ : HEq c.psi' c'.psi') (hO : HEq c.Oe c'.Oe)
    (hcr : HEq c.crOe c'.crOe) (halg : HEq c.algOe c'.algOe) (halg' : HEq c.algOOe c'.algOOe)
    (hemb : HEq c.embW c'.embW) (hMt : HEq c.eMt c'.eMt) : HEq c c' := by
  cases hD
  cases c
  cases c'
  dsimp only at hTw hsd hQ hk hψ hO hcr halg halg' hemb hMt
  obtain rfl := eq_of_heq hTw
  obtain rfl := eq_of_heq hsd
  obtain rfl := eq_of_heq hQ
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq hψ
  obtain rfl := eq_of_heq hO
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq halg
  obtain rfl := eq_of_heq halg'
  obtain rfl := eq_of_heq hemb
  obtain rfl := eq_of_heq hMt
  rfl

private theorem tupTied_heq {D D' : D7} (hD : D = D')
    {cf : CharFrame D} {cf' : CharFrame D'} (hcf : HEq cf cf')
    {ch : NChoice D} {ch' : NChoice D'} (hch : HEq ch ch')
    {tp : TupTied D cf ch} {tp' : TupTied D' cf' ch'}
    (hξ : HEq tp.xi tp'.xi) (hψ : HEq tp.psi tp'.psi) : HEq tp tp' := by
  cases hD
  obtain rfl := eq_of_heq hcf
  obtain rfl := eq_of_heq hch
  cases tp
  cases tp'
  dsimp only at hξ hψ
  obtain rfl := eq_of_heq hξ
  obtain rfl := eq_of_heq hψ
  rfl

private abbrev LinkedDataIndices :=
  Σ D : D7, (Σ cf : CharFrame D, Σ ch : NChoice D, TupTied D cf ch) × MtFam D

private theorem linkedDataIndices_congr {D D' : D7} (hD : D = D')
    {cf : CharFrame D} {cf' : CharFrame D'} (hcf : HEq cf cf')
    {ch : NChoice D} {ch' : NChoice D'} (hch : HEq ch ch')
    {tp : TupTied D cf ch} {tp' : TupTied D' cf' ch'} (htp : HEq tp tp')
    {M : MtFam D} {M' : MtFam D'} (hM : HEq M M') :
    (⟨D, ⟨cf, ch, tp⟩, M⟩ : LinkedDataIndices) = ⟨D', ⟨cf', ch', tp'⟩, M'⟩ := by
  cases hD
  obtain rfl := eq_of_heq hcf
  obtain rfl := eq_of_heq hch
  obtain rfl := eq_of_heq htp
  obtain rfl := eq_of_heq hM
  rfl

private theorem linkedDataIndices_eq (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
    (x : St P) (L : LocAll (lay0 (Dof x))) (l : StrictHenselianAcyclicLevel hL x) :
    (⟨withLoc L, ⟨cfL L (cfOf x), chL L l.c.ch, tpL L l.c.tp⟩, mtL L l.mt.M⟩ :
        LinkedDataIndices) =
      ⟨DL x L, ⟨cfD x L, characterChoiceLocal L l, localCharacterTupleAgreement L l⟩,
        localMultiplicityFamily L l⟩ := by
  have hD := (DL_eq x L).symm
  have hM : HEq (mtL L l.mt.M) (localMultiplicityFamily L l) := by
    refine Function.hfunext rfl fun μ μ' hμ => ?_
    have hμ' : μ = μ' := eq_of_heq hμ
    subst μ'
    refine Function.hfunext rfl fun j j' hj => ?_
    have hj' : j = j' := eq_of_heq hj
    subst j'
    refine Function.hfunext rfl fun h₁ h₁' _ => ?_
    refine Function.hfunext rfl fun h₂ h₂' _ => ?_
    apply mtReal_heq hD (HEq.refl μ) <;> with_unfolding_all rfl
  have hcf : HEq (cfL L (cfOf x)) (cfD x L) := by
    apply charFrame_heq hD <;> with_unfolding_all rfl
  have hch : HEq (chL L l.c.ch) (characterChoiceLocal L l) := by
    apply nChoice_heq hD <;> with_unfolding_all rfl
  have htp : HEq (tpL L l.c.tp) (localCharacterTupleAgreement L l) := by
    apply tupTied_heq hD hcf hch <;> with_unfolding_all rfl
  exact linkedDataIndices_congr hD hcf hch htp hM

set_option maxHeartbeats 4000000 in
theorem third_place_linked_data_exists : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedData hL D') := by
  intro hL hP hX
  have agreement := StepW.and
    (ThirdAgree.third_components_agree_alt hL hP hX)
    (GlobalTheory.T.ordinary_idempotent_third_component_of_cmDatum_alt hL hP hX)
  have readingInputs := StepW.and
    (ThirdTied.third_component_hecke_character_tuple_alt hL hP hX)
    (StepW.and (GlobalTheory.HeightCounting.Fin.finite_types_with_local_conditions_alt hL hP hX)
      (StepW.and (GlobalTheory.T.eigen_index_divisibility_of_cmDatum_alt hL hP hX) agreement))
  have fitsAndGap := StepW.and
    (ThirdFits.third_component_fits_integral_lattice_alt hL hP hX) GapAllStates.gapR_allSt
  have inputs := StepW.and fitsAndGap (StepW.and SizePar.exists_params_alt.2 readingInputs)
  refine StepW.trans inputs (StepW.of_all ?_)
  intro K B f T w _ _ h P x l
  obtain ⟨⟨hfits, hgap⟩, hpar, htp, hty, hidx, hag, he0⟩ := h
  refine ⟨fun _ => ∅, fun L hB hO => ?_⟩
  obtain ⟨Q₀, hcf₀, hch₀, htp₀, hrep₀, hM₀⟩ := third_place_fixed_alt hL hP x l _ L hB
  let CompatibleChoice (i : LinkedDataIndices) : Prop :=
    ∃ Q : GlobalTheory.NPin.CharacterChoiceData hL i.1,
      Q.cf = i.2.1.1 ∧ Q.C = i.2.1.2.1 ∧ HEq Q.tp i.2.1.2.2 ∧
        HEq Q.rep (repOf x.r.Y) ∧ Q.M = i.2.2
  have choice₀ : CompatibleChoice
      ⟨withLoc L, ⟨cfL L (cfOf x), chL L l.c.ch, tpL L l.c.tp⟩, mtL L l.mt.M⟩ :=
    ⟨Q₀, hcf₀, hch₀, htp₀, hrep₀, eq_of_heq hM₀⟩
  obtain ⟨Q, hcf, hch, htup, hrep, hM⟩ :=
    Eq.mp (congrArg CompatibleChoice (linkedDataIndices_eq hL x L l)) choice₀
  obtain ⟨x', hx'⟩ := _root_.GlobalTheory.Mem.R3.Rw.st_of_fits hX.weil hX.ds hP.hc hP.decay K B f T w P (oL x L) (hfits P x l _ L hB hO) x.G_eq
    x.etaF (bkL L)
  obtain ⟨o, fits', G_eq', etaF', bk', m, cp, co, s, r, pn⟩ := x'
  dsimp only at hx'
  subst hx'
  have hC : m.z.R.C = cfD x L := m.z.lev.C
  have ht := htp P x l _ L hB hO m cp co s r pn
  have hT := hty P x l _ L hB hO m cp co s r pn
  obtain ⟨Xd, E, ⟨labPi⟩⟩ := hidx P x l _ L hB hO m cp co s r pn
  have parameters : ∃ C, Nonempty (ParameterChoice' (DL x L) C) :=
    Eq.mpr (congrArg (fun D => ∃ C, Nonempty (ParameterChoice' D C)) (DL_eq x L))
      ((hpar P x).2 L)
  have hg : GlobalTheory.LiftRows.Given m.z.R.toRealDat m.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak m.z.R m.z.F m.z.pins.char m.exAt).1, parameters, m.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ m.z.pins.char.base.lev hT, m.z.pins.keep.guard, hgap P x⟩
  obtain ⟨ag⟩ := hag P x l _ L hB hO m cp co s r pn hC Xd E labPi
    m.z.pins.char.base ht hg m.z.pins.char.fullP Q.rep hrep
  have e0 := he0 P x l _ L hB hO m cp co s r pn hC Xd E labPi
    m.z.pins.char.base ht hg m.z.pins.char.fullP
  let reading := realOfRead (D := DL x L) m.z.R.toRealDat m.z.F.lv2 r.Y
    (localCharacterTupleAgreement L l) hC Xd E labPi m.z.pins.char.base ht hg
    m.z.pins.char.fullP
  have he : GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector reading := by
    with_unfolding_all exact e0
  obtain ⟨linked, -, -⟩ := exists_linked_data_of_agreement Q reading hcf hch htup hM HEq.rfl ag he
  exact Eq.mp (congrArg (fun D => Nonempty (GlobalTheory.NRows.LinkedData hL D)) (DL_eq x L))
    ⟨linked⟩
end GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_system_third_place_linked_data : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (_root_.GlobalTheory.NRows.LinkedData hL D') := by
  exact _root_.GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning.third_place_linked_data_exists
end
end
