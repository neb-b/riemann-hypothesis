module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0352
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0053
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0052
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0222
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowJOnOfRealisations
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx NumberField GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.JOnRow
theorem row_jOn_of_realisations_alt : ∀ (Bd : BdT) (Q' : V4.Slot) (Lk : LkT Bd), Row Q' Lk (AtAll fun D O _ _ => ∃ (Rc : _root_.Formalism.L2.RecTAlt O.ex) (P : RowSideFamily O.ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks D.what₂.LL) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (s : ℕ), P.A3.fam3.Ok3 s ∧ P.A3.fam3.TypesSep3 ∧ PrimRows3 Q.Rl Q.F) → R0.JInvariantConditionAtConstructedPoints Q' Lk := by
  intro Bd Q' Lk h
  refine Row.imp h fun 𝒜 σ _ hA => ?_
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ hc _ => ?_⟩⟩
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx' : Fm.x1 < x := by linarith
  obtain ⟨Rc, P, Dcf, Spf, Zscf, S, Ks, i1, i2, i3, Q, s, h1, h2, h3⟩ := hA Fm (w3_a hc) x hx' i
  exact _root_.GlobalTheory.T.V0_map_iota_eq_top_real_alt _ _ _ _ _ _ _ _ _ Rc P Dcf Spf Zscf S Ks i1 i2 i3 Q s h1 h2 h3
end GlobalTheory.JOnRow
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeExJoinPin
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
namespace GlobalTheory.Mem.JPin
set_option maxHeartbeats 4000000 in
theorem seeEx_joinPin_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Yd cX) (x : TwIn ex) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : SPack D fun u => (Rc.T.cols.forms u).to0) (S : SRest P) (y : _root_.GlobalTheory.Mem.R3.RealInAlt x Rc (S.toRealSpectralMatching Rc)) (c : ℝ), Holds x.R x.F → SeeAt x.R.toRealDat x.F.lv2 P.X P.inst y.tS → EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G (iotaX P.X P.inst).toMulEquiv y.tS c → RowJ x.R.toRealDat x.Y.eE P.X P.inst P.G y.tS S.j → _root_.Formalism.IndefR.IndefiniteRealisationExtends (_root_.GlobalTheory.Mem.R3.realisationOfInput y) ∧ _root_.GlobalTheory.Mem.JTop.JoinPinAlt (_root_.GlobalTheory.Mem.R3.realisationOfInput y) := by
  intro D L hT Gi Gl K Yd cX ex x Rc P S y c _ hS hE hR
  have hι : y.ιS = (iotaX P.X P.inst).toMulEquiv :=
    (GlobalTheory.Mem.JIota.heq_iota_iff D P.X P.inst y.ιS).1 y.ιS_eq
  have hinj : Function.Injective x.R.HE.e := x.pins.char.base.models.HE.1
  have hread : ∀ y1, x.Y.eE (D.jEE (x.Z.eRR y1)) = Tw.out (s := twAt D.what₂.embLL x.A3.A.v0) (E := x.R.HE.H)
      ((x.R.toCx3 x.F).iC x.F.cr true x.A3.A.μ0 (cpt x.A3.A.v0.embedding y1)) := by
    intro y1
    have h1 := x.Y.eE_read (D.jEE (x.Z.eRR y1))
    rw [x.Z.jEE y1] at h1
    exact hinj ((PiTensorProduct.lift : Mult.MMap (x.R.MY 0) ≃ₗ[ℂ] _).injective h1).symm
  refine ⟨⟨⟨y.tS, hS.fin, ?_, ?_⟩, c, ?_⟩, x.Y.eE, ?_, ?_⟩
  · show ConjLevel y.tS⁻¹ (JR x.R.toRealDat x.F.lv2) (chiR x.R.toRealDat x.F.lv2) (y.ιS ⁻¹' concreteLevelAdelicSubset P.X)
      (fun k => adelicCharacterOfHidaSetting P.X (y.ιS k))
    rw [hι]
    exact hS.conj
  · exact hS.mat
  · show EvalTieT (MP x.R.toRealDat) x.R.toRealDat.ν0 x.R.toRealDat.fd0 (EP x.R.toRealDat x.F.lv2) P.X P.G y.ιS y.tS c
    rw [hι]
    exact hE
  · intro y1 y' h
    obtain rfl := eq_of_heq h
    exact hread y1
  · intro hF
    have hj : _root_.Formalism.L2.SG.JoinSI.spectralRowIsometry (S.toRealSpectralMatching Rc) hF = S.j :=
      _root_.Formalism.L2.SG.JoinSI.isometryOfJoin_eq_of_conj_compat (S.toRealSpectralMatching Rc) hF S.j fun F => S.rowPin F
    rw [hj]
    exact hR
end GlobalTheory.Mem.JPin
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeeIsoOfSeeExStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_limit_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), _root_.Formalism.IndefR.IndefiniteRealisationExtends Q → (Q.Rl.toCx3 Q.F).SEEIso Q.sEE := by
  first | exact @_root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt | exact _root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt | (intros; apply _root_.GlobalTheory.Div.SeeIsoClose.seeIso_of_seeEx_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StrInertTyz
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigStrInert
abbrev _root_.GlobalTheory.EigStrInert.strInert_tyz : Prop :=  GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)
end GlobalTheory.EigStrInert
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.EX GlobalTheory.EX.OB
namespace GlobalTheory.Fc.Ind
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure PointSummands (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : _root_.Formalism.L2.RecTAlt O.ex
  S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R
  P : RowSideFamily O.ex
  pin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)
  Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)
  ok1 : P.A3.fam3.Ok3 1
  B : _root_.Formalism.IndefR.RealTBAlt R P Dcf Spf (GlobalTheory.Fc.zsc P DH.1.1 DH.1.2 c) S
  Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q
  psi : PsiPPTie D P.P0 P.ψ0 P.Ps P.ψs P.I.eG
  pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q
  muDef : ∀ C CH : ℝ, (B.Q.Rl.toCx3 B.Q.F).MuDef B.Q.F.cr (B.Q.Rl.num B.Q.F C CH) B.Q.Rl.mu
  recPins : _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
def FiringPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  b.B.Q.Rl.toRealDat.ExAt ∧ JEvBar b.B.T b.B.Q.Rl.toRealDat b.B.κ ∧ GeoAct b.B.T b.B.Q.Rl.toRealDat b.B.κ b.B.v₀ ∧
    EvInj b.B.T b.B.Q.Rl.toRealDat b.B.v₀
def summandRealBound : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows b.B
def ThresholdPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  RecTie.ThetaFireRow (RecTie.toLiftReal b.B.Q.Rl.toRealDat b.B.Q.F.lv2 b.Rr.tupT b.Rr.hm b.Rr.hTop b.Rr.hinj) b.Rr.IL
def FramePointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q
def VisibleExamplePointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q
def summandPrimitive : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
def DivisorPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D O _ b =>
  DivRows3 D b.P.A3 b.P.P0 b.P.ψ0 b.P.Ps b.P.ψs b.P.Zs b.P.S0 b.P.S1 O.ex.p0 b.P.C b.P.NuC b.P.I
def summandDegreeZero : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun D _ _ b =>
  D.what₂.D0 = (b.P.A3.A.fam.R b.P.A3.A.fam.μ0).dZ (b.P.A3.A.fam.lvl b.P.P0 b.P.ψ0) (b.P.Zs.Z b.P.A3.A.fam.μ0)
def NormJumpPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ O _ b => _root_.Formalism.IndefR.NX.RealExpansionMajorant b.B.Q b.B.Q.cG b.B.Q.Sx b.B.Q.nexp O.ex.nch
def IotaPointSummands : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ∀ x : b.S.X.B.I.E, HEq (b.S.X.ιE x) x
def summandL3Bound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).L3 (b.B.Q.Rl.num b.B.Q.F C CH)
def summandNormBound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).ON (b.B.Q.Rl.num b.B.Q.F C CH)
def summandL6Bound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr true).L6 (b.B.Q.Rl.num b.B.Q.F C CH)
def summandFunctionalBound (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b => ((b.B.Q.Rl.toCx3 b.B.Q.F).data b.B.Q.F.cr false).FUN (b.B.Q.Rl.num b.B.Q.F C CH)
def SmallPointSummands (C CH : ℝ) : BdP _root_.GlobalTheory.Fc.Ind.PointSummands := fun _ _ _ b =>
  (∀ w, (b.B.Q.Rl.toCx3 b.B.Q.F).W1 b.B.Q.F.cr (b.B.Q.Rl.num b.B.Q.F C CH) w → w ∈ b.B.Q.Rl.twPl) ∧
    (b.B.Q.Rl.toCx3 b.B.Q.F).SEEIso b.B.Q.sEE ∧ PassIn3 b.B.Q.Rl b.B.Q.F C CH
end GlobalTheory.Fc.Ind
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaFireRowRecTieStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indefinite_scale_theta_identity_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks), ∀ (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q), Q.Rl.toRealDat.ExAt → Formalism.IndefR.RecTie.ThetaFireRow (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.hTop Qr.hinj) Qr.IL := by
  first | exact @_root_.GlobalTheory.thetaFireRow_recTie_alt | exact _root_.GlobalTheory.thetaFireRow_recTie_alt | (intros; apply _root_.GlobalTheory.thetaFireRow_recTie_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam
variable {D : D7}
section Package
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (u : D.what₂.Word) (g : Geo D)
variable {R P u g}
end Package
section Read
variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)
end Read
section Real
open GlobalTheory.MiS
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex)
abbrev pk_z := W.Q.Rl.toRealDat
abbrev complexLevelStructure : LevelP (_root_.GlobalTheory.Fam.pk_z W).Pg D.R.r ℂ := (_root_.GlobalTheory.Fam.pk_z W).levR W.Q.F.lv2 true
def LevelCondition (u : D.what₂.Word) (μ : D.what₂.Tup) (x : GA D D.sp.X') (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (μ = D.what₂.mu0 → LevG (W.R.T.cols.forms u).clsP.toG x J χ) ∧ ∀ h : μ ≠ D.what₂.mu0, LevG (W.R.T.tw.pt.cls u μ h) x J χ
def ReadsCoefficients (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup) (G : D.what₂.Amb μ)
    (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : Prop :=
  (∀ h : μ = D.what₂.mu0, ReadsG (W.R.T.cols.forms u).clsP.toG (W.R.T.cols.forms u).valP.eW j x
    ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) G h)) f) ∧
  ∀ h : μ ≠ D.what₂.mu0, ReadsG (W.R.T.tw.pt.cls u μ h) (W.R.T.tw.pt.val u μ h).eW j x ((D.eMtTw u μ).symm G) f
def leadingLinearMap (t : W.P.T) (F : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL) : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ) :=
  (_root_.GlobalTheory.Fam.pk_z W).cX.toMap (_root_.GlobalTheory.Fam.pk_z W).prX (((_root_.GlobalTheory.Fam.pk_z W).HX t).e ((_root_.GlobalTheory.Fam.pk_z W).jX t (W.Q.F.eV (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs t F)))
def LeadingReadAt (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') : Prop :=
  GlobalTheory.Core.Rk.Top.IsJ u (_root_.GlobalTheory.Fam.pk_z W).MX j ∧ x ∈ GfC D.sp.X' ∧ ∀ t : W.P.T,
    _root_.GlobalTheory.Fam.LevelCondition W u (W.P.I.tup t) x (levS _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z W).βX (datXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) t)) ∧
    ∀ (F : Fin ((W.P.A3.side3 W.P.Ps W.P.ψs W.P.Zs).nV t) → D.what₂.LL) (F' : Fin ((W.Q.F.fc (_root_.GlobalTheory.MiS.packageCoefficientSpace W).zs).Df1.nV t) → D.what₂.LL),
      HEq F F' → _root_.GlobalTheory.Fam.ReadsCoefficients W u j x (W.P.I.tup t) (W.P.I.jA t ((rV0 D W.P.A3.A W.P.Ps W.P.ψs t).mulVec F)) (_root_.GlobalTheory.Fam.leadingLinearMap W t F')
def LeadingReadStatement : Prop := ∃ x, ∀ u, ∃ j, _root_.GlobalTheory.Fam.LeadingReadAt W u j x
def tailCoefficient (u : D.what₂.Word) (j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup)
    (ψ : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) (f : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : ℂ :=
  if h : ∃ G, _root_.GlobalTheory.Fam.ReadsCoefficients W u j x μ G f then
    if h0 : μ = D.what₂.mu0 then
      (D.mem u).P.Ptil (Eq.rec (motive := fun C _ => C.cls D.R.m → C.Y D.R.m → ℂ)
        (Eq.rec (motive := fun ν _ => (D.chTw u ν).cls D.R.m → (D.chTw u ν).Y D.R.m → ℂ) ψ h0) (D.memberColumns_twistedChain_base u))
        ((D.eMt u).symm (Eq.rec (motive := fun ν _ => D.what₂.Amb ν) h.choose h0))
    else (D.PTw u μ).Ptil ψ ((D.eMtTw u μ).symm h.choose)
  else 0
structure FamilyCharacter (u : D.what₂.Word) where
  g : Geo D
  j : SmT (_root_.GlobalTheory.Fam.pk_z W).MX →ₗ[ℂ] (FrP D → ℂ)
  row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g t
  col : ∀ t : W.P.T, ColCh u (D.chTw u (W.P.I.tup t))
variable {W} {u : D.what₂.Word} (f : _root_.GlobalTheory.Fam.FamilyCharacter W u)
abbrev FamilyCharacter.c : Comm D := commOf (_root_.GlobalTheory.Fam.pk_z W) u f.g
abbrev FamilyCharacter.t (t : W.P.T) : Tup f.c :=
  tupOf (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u f.g t (f.row t) (f.col t) fun ψ F => _root_.GlobalTheory.Fam.tailCoefficient W u f.j f.g.bT (W.P.I.tup t) ψ F.1
end Real
end GlobalTheory.Fam
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
theorem transport_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ sp : SplitPlace D.host.E, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i))) = s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := by
  intro _ hL D P X A _ _ _ i hμ j hj f y hy h hOps s hEig sp hG hJ ϖ hϖ k hk
  have hn : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hLab := isLab_std A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk
  have hsum := eig_sum X hμ j f y hy h hOps s hEig sp.w hG (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) hLab
  have hGf := GlobalTheory.DefLiftHecke.rep_mem_GfC (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)
  classical
  let xi : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j) → Formalism.AUTREP.GAf D.host.E D.R.nV := fun γ =>
    if hγ : γ ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j) then ((A.PV j).onto γ hγ).choose else 1
  have hxi : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (A.PV j).ψ (xi γ) = γ := fun γ hγ => by
    simp only [xi, dif_pos (hGf γ hγ)]
    exact ((A.PV j).onto γ (hGf γ hγ)).choose_spec
  have hT : ∀ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k, TrivOutside {sp.v} x := fun x hx => hx.1
  suffices key : ∀ (m : ℕ) (e : j.1 + 1 = m) (p1 : 1 ≤ m) (p2 : m ≤ D.R.m),
      (∀ κ : Formalism.AUTREP.GAf D.host.E D.R.nV, TrivOutside {sp.v} κ →
        (κ ∈ (P.M (D.nd.mu i) m p1 p2).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧
          ∀ hκ : κ ∈ (P.M (D.nd.mu i) m p1 p2).J, (P.M (D.nd.mu i) m p1 p2).χ ⟨κ, hκ⟩ = 1) →
      NG.heckeD (P.M (D.nd.mu i) m p1 p2).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k)
          ((P.M (D.nd.mu i) m p1 p2).real (e ▸ f)) =
        s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M (D.nd.mu i) m p1 p2).real (e ▸ f) from key _ hj _ _ hJ
  intro m e
  subst e
  intro p1 p2 hJ
  have hF : ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g =
      A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g))) := fun g => A.real (D.nd.mu i) hμ j f g
  have hinv : ∀ κ (hκ : κ ∈ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ ⟨κ, hκ⟩ = 1 →
      ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * κ) = (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g := by
    intro κ hκ h1 g
    have hmem : (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f ∈ Formalism.L2.NG.TypeSp (P.M (D.nd.mu i) (j.1 + 1) p1 p2).wt.ρ
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ := by
      rw [← (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real_range]
      exact LinearMap.mem_range_self _ _
    have := congrFun (hmem.2 ⟨κ, hκ⟩) g
    rw [h1] at this
    simp only [Units.val_one, one_smul] at this
    exact this
  have hmemT : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), xi γ ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k := by
    intro γ hγ
    refine (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk _).2 ⟨γ, hγ, ?_⟩
    rw [hxi γ hγ, inv_mul_cancel]
    exact GlobalTheory.DefLiftHecke.one_mem_hyp _ _
  funext g
  show (∑ᶠ c : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J,
      if hc : ∃ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k,
          (x : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J) = c then
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * hc.choose) else 0) = _
  rw [finsum_cosets (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J _ (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) xi _
    ?h1 ?h2 ?h3 ?h4 g]
  case h1 => exact hmemT
  case h2 =>
    intro x hx
    obtain ⟨γ, hγ, hm⟩ := (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk x).1 hx
    refine ⟨γ, hγ, ?_⟩
    rw [← hxi γ hγ, ← map_inv, ← map_mul] at hm
    obtain ⟨hU, hT'⟩ := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).1 hm
    exact (hJ _ hT').1.2 hU
  case h3 =>
    intro γ hγ γ' hγ' hm
    have ht := triv_mul (triv_inv (hT _ (hmemT γ hγ))) (hT _ (hmemT γ' hγ'))
    have hU := (hJ _ ht).1.1 hm
    have hh := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).2 ⟨hU, ht⟩
    rw [map_mul, map_inv, hxi γ hγ, hxi γ' hγ'] at hh
    exact rep_inj _ _ _ hLab γ hγ γ' hγ' hh
  case h4 =>
    intro y hy y' hy' hm g0
    have ht := triv_mul (triv_inv (hT _ hy)) (hT _ hy')
    have := hinv _ hm ((hJ _ ht).2 hm) (g0 * y)
    rw [mul_assoc, mul_inv_cancel_left] at this
    exact this
  rw [Pi.smul_apply, hF g]
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * xi γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) :=
        Finset.sum_congr rfl fun γ hγ => by rw [hF, ← mul_assoc, map_mul, hxi γ hγ]
    _ = A.eW _ hμ j (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) := (map_sum _ _ _).symm
    _ = _ := by rw [hsum, map_smul]
end GlobalTheory.EigTransport
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UsedAll
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mi
namespace GlobalTheory.MiS.Check
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem used_all_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (t : W.P.T) : Formalism.IndefR.RecTie.Used0 D (W.P.I.tup t) := by
  rcases W.Q.charW.tup.mu_used t with h | ⟨w, h⟩
  · rw [h]; exact used_base W.P
  · right
    have e : W.Q.Rl.mu = W.P.S0.μ := mu_eq_of_heq W.P W.Q.zs _ W.Q.s0
    refine ⟨D.plEq.symm w, ?_⟩
    rw [W.P.tied.div.tup.muAt, Equiv.apply_symm_apply, ← h, e]
    rfl
end GlobalTheory.MiS.Check
end
end
end

