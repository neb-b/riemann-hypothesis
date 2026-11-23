module

public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InpAtOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.RowDataTransport
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
set_option maxHeartbeats 16000000 in
theorem inpAt_of_alt [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields}
    {e : X.Tau → (X.E →+* D.what₂.LL)} {c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs}
    {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)} {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P c.face Sp Zsc S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P c.face Sp Zsc) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P c.face Sp Zsc) Cl CHl)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (Ce : ℝ) (hDIV : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce)
    (hTw : TieTwRec L (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.Tw)
    (hD : D.what₂.D0 = (P.A3.A.fam.R P.A3.A.fam.μ0).dZ (P.A3.A.fam.lvl P.P0 P.ψ0)
      ((_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs.Z P.A3.A.fam.μ0))
    (h11 : LiftExponentAtTwisted P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.μ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.Tw
      (Zsc (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).J0)
    (hdgA : ∃ dg : ℕ, 0 < dg ∧ (∀ j t, (P.A3.A.fam.L j t).DG (P.A3.A.fam.lvlA P.P0 P.ψ0) ∣ dg) ∧
      ∀ u, ArithAt P.A3 s P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc _ Cl CHl (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI)
        (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
        (fun _ => divSize L Ce) dg)
    (what₂ : ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.col NuC I →
      HEq I P.I → ∀ u, RowsU c (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI)
        (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
        (I.wU u) (Cons.nuOf L u (I.eNu u))) :
    _root_.Formalism.L2.RowDataTransport.InpAtAlt c Q hOk hsep Cl CHl hP hI Del h0 lam0 C0 ce Ch Sw C1 eJ H := by
  intro NuC I hT hI'
  obtain ⟨dg, hdg, hdvd, hA⟩ := hdgA
  have hN := inEta3_num (G := P.Gp) L P.A3 (P0 := P.P0) (ψ0 := P.ψ0) (Zs := (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)
    (S0 := (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData) (tup := I.tup) Ce hDIV rfl hT.num hTw hD
  have hr := what₂ NuC I hT hI'
  choose ch T hF hrest using hr
  choose X0 hX0 hn hnP cb hrest2 using hrest
  refine ⟨fun u => ((DivisionInputsWithoutNorm.ofRows (hrest2 u).2.2.2 (Formalism.L2.DIV.Cons.sgRec_fin L u) (hrest2 u).2.1 (hrest2 u).2.2.1
      (X0 u) (hX0 u) (ch u) (hn u) (hnP u) (cb u) (hrest2 u).1 h11 dg hdg hdvd (hA u)).toDef hN).toDivInputs0R hOk hsep,
    fun u => T u, fun u => hF u⟩
end Formalism.L2.RowDataTransport
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JoinPin
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.JTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def JoinPinAlt (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) : Prop :=
  ∃ eE : D.what₂.EE →ₗ[ℂ] Q.Rl.HE.H,
    (∀ y y', HEq y y' → eE (D.jEE (P.I.eRR y)) =
      Tw.out (s := Formalism.L2.SG.JoinSI.twQ P) (E := Q.Rl.HE.H)
        ((_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).iC Q.F.cr true P.A3.A.μ0 (cpt P.A3.A.v0.embedding y'))) ∧
    ∀ hF : Formalism.L2.SG.PackageTie2.FinX S.Y, GlobalTheory.Mem.SRe.RowJ Q.Rl.toRealDat eE S.X S.inst S.G Q.tS (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S hF)
theorem bR_heq_eMu_single (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) (hPin : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation Q) (u : D.what₂.Word) (i : Fin (P.Dc.a (P.I.wU u))) :
    HEq (Q.bR (P.I.wU u) i) (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
  refine HEq.trans (heq_of_eq (hPin.bR_read (P.I.wU u) i)) ?_
  have key : ∀ (w : D.what₂.Word) (hw : w = u) (hc : P.Dc.a (P.I.wU u) = P.Dc.a (P.I.wU w)),
      HEq (D.eMu w (D.jN w (P.I.eNu w (Pi.single (Fin.cast hc i) 1))))
        (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
    intro w hw hc
    subst hw
    rfl
  exact key _ (Q.wdD_wU u) _
end GlobalTheory.Mem.JTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionFirstAlt
section
set_option synthInstance.maxHeartbeats 200000

section
namespace LinearIndependenceOfCarries
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.ReadingExt
open Module
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def finrankCoordinateEquiv (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      (Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL) :=
  LinearEquiv.funCongrLeft D.what₂.LL D.what₂.LL (finCongr (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i))
def embeddingAtIndex (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (Y.MjH ((i : ℕ) + 1)).V →ₗ[D.what₂.LL] Q.Sx.WL ((i : ℕ) + 1) :=
  (Q.nexp.fi i).e.symm.toLinearMap ∘ₗ jDL Q.Rl Q.F.lv2 i ∘ₗ (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i).toLinearMap ∘ₗ (P.JM.eW i).symm.toLinearMap
def embeddingAtLevel (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] Q.Sx.WL j
  | 0 => 0
  | k + 1 => if h : k < D.R.m then _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex Q ⟨k, h⟩ else 0
theorem embeddingAtLevel_succ_eq_embeddingAtIndex (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel (Y := Y) Q ((i : ℕ) + 1) = _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex Q i := by
  obtain ⟨k, h⟩ := i
  simp [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel, h]
theorem jDL_injective_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Function.Injective (jDL Q.Rl Q.F.lv2 i) := by
  have h : LinearIndependent D.what₂.LL (Q.Rl.toRealDat.bL Q.F.lv2 false i) :=
    (Module.finBasis D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)).linearIndependent.map' (Submodule.subtype _)
      (Submodule.ker_subtype _)
  exact linearIndependent_iff_injective_fintypeLinearCombination.1 h
theorem embeddingAtIndex_injective (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Function.Injective (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex (Y := Y) Q i) := by
  intro x y h
  have h1 := (Q.nexp.fi i).e.symm.injective h
  have h2 := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.jDL_injective_alt Q i h1
  exact (P.JM.eW i).symm.injective ((_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i).injective h2)
theorem e_embeddingAtLevel_succ_eq_jDL_of_heq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V)
    (y : Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL)
    (h : HEq ((P.JM.eW i).symm x) y) : (Q.nexp.fi i).e (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel Q ((i : ℕ) + 1) x) = jDL Q.Rl Q.F.lv2 i y := by
  rw [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel_succ_eq_embeddingAtIndex]
  have h1 : _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.finrankCoordinateEquiv Q i ((P.JM.eW i).symm x) = y := comp_cast_of_heq (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i) _ y h
  simp only [_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, h1]
theorem jDa_injective_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Function.Injective (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel (Y := Y) Q j) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hk : k < D.R.m := by omega
  have e := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel_succ_eq_embeddingAtIndex (Y := Y) Q ⟨k, hk⟩
  have h := _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtIndex_injective (Y := Y) Q ⟨k, hk⟩
  rw [← e] at h
  exact h
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in
set_option synthInstance.maxHeartbeats 400000 in
theorem embW_comp_algebraMap_eq_fracExt_comp_iotaK (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) :
    (ex.nch.embW w).comp (algebraMap Q.Sx.Ks D.what₂.LL) =
      (fracExt ex.nch w).comp (ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w)) :=
  GlobalTheory.Proof.FractionFieldEmbeddingCompat.embCompat D ex.nch hc Q.Sx.Ks Q.Sx.kKs Q.Sx.kKs_spec w _ rfl
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_ext_alt (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hk : (Q.Sx.A j).IsKsForm) :
    ∃ e : Q.Sx.WL j →ₛₗ[ex.nch.embW w]
        FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w),
      (∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK Q.Sx j),
        e (∑ k, a k • (show ↥(Q.Sx.A j).WK from f k).1) =
          ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
            (Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm
              ((1 : KB Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[Q.Sx.Ks] f k)) ∧
      (∀ (ι : Type) (v : ι → Q.Sx.WL j), LinearIndependent D.what₂.LL v →
        LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => e (v a))) := by
  letI aK : Algebra Q.Sx.Ks (FractionRing (D.ntw.O (ex.nch.twI w))) := (ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w)).toAlgebra
  letI aE : Algebra (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) := (fracExt ex.nch w).toAlgebra
  haveI : IsScalarTower (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = fracExt ex.nch w (algebraMap _ (FractionRing (D.ntw.O (ex.nch.twI w))) x)
      rw [IsScalarTower.algebraMap_apply (D.ntw.O (ex.nch.twI w)) (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))]
      simp [fracExt, IsFractionRing.map]
  obtain ⟨⟨e, he, -⟩, hC, -⟩ := GlobalTheory.SemilinearExt.semilinearExtension Q.Sx.Ks D.what₂.LL (Q.Sx.WL j) (Q.Sx.A j).WK hk
    (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) (ex.nch.embW w)
    (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_comp_algebraMap_eq_fracExt_comp_iotaK hc Q w) (D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) (Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2)
  exact ⟨e, fun n a f => he (Fin n) a f, fun ι v hv => li_of_carries e (hC e he) hv⟩
open GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion in
set_option synthInstance.maxHeartbeats 400000 in
theorem embW_Ks_alt (hc : NChTie D ex.nch) (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (w : D.what₂.places.Pl) (j : ℕ) (a : Q.Sx.Ks)
    (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) :
    (ex.nch.embW w (algebraMap Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m :
        FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) =
      (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
        ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m) := by
  letI aE : Algebra (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) := (fracExt ex.nch w).toAlgebra
  haveI : IsScalarTower (D.ntw.O (ex.nch.twI w)) (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w)) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = fracExt ex.nch w (algebraMap _ (FractionRing (D.ntw.O (ex.nch.twI w))) x)
      rw [IsScalarTower.algebraMap_apply (D.ntw.O (ex.nch.twI w)) (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))]
      simp [fracExt, IsFractionRing.map]
  have e1 : ex.nch.embW w (algebraMap Q.Sx.Ks D.what₂.LL a) =
      algebraMap (FractionRing (D.ntw.O (ex.nch.twI w))) (FractionRing (ex.nch.Oe w))
        (show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) :=
    RingHom.congr_fun (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_comp_algebraMap_eq_fracExt_comp_iotaK hc Q w) a
  rw [e1]
  exact GlobalTheory.SemilinearExt.algebraMap_tmul (O := D.ntw.O (ex.nch.twI w)) _ m
set_option synthInstance.maxHeartbeats 400000 in
theorem reading_ext_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → ∃ (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm) ∧ (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) ∧ (∀ w j (a : B.Q.Sx.Ks) (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (ex.nch.embW w (algebraMap B.Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m : FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK B.Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m)) ∧ (∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => eM w j ((Y.MjH j).b a))) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B _ _ hc
  have hks : ∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm := by
    intro j h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk : k < D.R.m := by omega
    exact GlobalTheory.isKsForm_of_formsIso _ _ (B.Q.nexp.fi ⟨k, hk⟩) (B.fw.ks ⟨k, hk⟩)
  have hE := fun w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.exists_ext_alt hc B.Q w j h1 h2 (hks j h1 h2)
  choose E hE1 hE2 using hE
  classical
  let eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)]
      D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w) := fun w j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then (E w j h.1 h.2).comp (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j) else 0
  have heM : ∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V), eM w j x = E w j h1 h2 (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j x) := by
    intro w j h1 h2 x
    simp only [eM, dif_pos (And.intro h1 h2)]
    rfl
  refine ⟨_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q, eM, fun i x y h => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.e_embeddingAtLevel_succ_eq_jDL_of_heq B.Q i x y h, hks, ?_, fun w j a m => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embW_Ks_alt hc B.Q w j a m, ?_⟩
  · intro w j h1 h2 x n a f hx
    rw [heM w j h1 h2, hx]
    exact hE1 w j h1 h2 n a f
  · intro w j _ h1 h2
    have hv : LinearIndependent D.what₂.LL (fun a => _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j ((Y.MjH j).b a)) :=
      (Y.MjH j).b.linearIndependent.map' (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.embeddingAtLevel B.Q j) (LinearMap.ker_eq_bot.2 (_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.jDa_injective_alt B.Q j h1 h2))
    have h := hE2 w j h1 h2 _ _ hv
    simp only [heM w j h1 h2]
    exact h
end GlobalTheory.CompanionTheory.ReadingExt
end
end
end LinearIndependenceOfCarries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.lattice_family_adoption_first_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q), NChTie D ex.nch → ∃ (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → (B.Q.Sx.A j).IsKsForm) ∧ (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) ∧ (∀ w j (a : B.Q.Sx.Ks) (m : D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), (ex.nch.embW w (algebraMap B.Q.Sx.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m : FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)) = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] ((show FractionRing (D.ntw.O (ex.nch.twI w)) from ιK B.Q.Sx (ex.nch.twI w) (ex.nch.sd w) a) • m)) ∧ (∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → LinearIndependent (FractionRing (ex.nch.Oe w)) (fun a => eM w j ((Y.MjH j).b a))) := by
  first | exact @_root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt | exact _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt | (intros; apply _root_.LinearIndependenceOfCarries.GlobalTheory.CompanionTheory.ReadingExt.reading_ext_alt <;> assumption)
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatticeFamilyAdoptionSecondAltAlt
section
set_option synthInstance.maxHeartbeats 200000

section
namespace GroupAverageFixedPoints
section
noncomputable section
open scoped TensorProduct
open Module
namespace GlobalTheory.CompanionTheory.LatSpan
section Rep
variable {F M Γ : Type} [Field F] [AddCommGroup M] [Module F M] [Group Γ] [Fintype Γ]
variable (a : Γ →* Module.End F M) (P : Subgroup Γ) [Fintype P] (t : P →* Fˣ) (E : Module.End F M)
end Rep
section Ext
variable {O K K'' Fm : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end Ext
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
section Main
variable {LL O K K'' Fm WL Γ : Type} [Field LL] [CharZero LL] [AddCommGroup WL] [Module LL WL]
  [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm] [Group Γ] [Fintype Γ]
end Main
section Lat
variable {LL Oe K'' V T : Type} [Field LL] [NumberField LL] [AddCommGroup V] [Module LL V] [Module (𝓞 LL) V]
  [IsScalarTower (𝓞 LL) LL V] [CommRing Oe] [IsDomain Oe] [Field K''] [Algebra Oe K''] [IsFractionRing Oe K'']
  [AddCommGroup T] [Module K'' T] [Module Oe T] [IsScalarTower Oe K'' T]
end Lat
end GlobalTheory.CompanionTheory.LatSpan
end
end
end
section
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
section Form
variable {Ks LL WL : Type} [Field Ks] [Field LL] [Algebra Ks LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  {WK : Submodule Ks WL}
  {O K K'' : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [Algebra Ks K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
end Form
section Iso
open Formalism.IndefR.NX Formalism.IndefR.Arith
variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
end Iso
end GlobalTheory.CompanionTheory.LatSpan
end
end
section
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX
section PiLocalization₂
variable {D : D7} (c : NChoice D) (w : D.what₂.places.Pl)
attribute [local instance] algKK
variable {c w}
end PiLocalization₂
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
section Alg
variable {k A G : Type} [Field k] [Ring A] [Algebra k A] [Group G]
end Alg
end GlobalTheory.CompanionTheory.LatSpan
noncomputable section
open scoped TensorProduct
open Module NumberField
namespace GlobalTheory.CompanionTheory.LatSpan
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith
section Stage2
variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}
attribute [local instance] algKK
end Stage2
end GlobalTheory.CompanionTheory.LatSpan
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CompanionTheory.LatSpan
attribute [local instance] algKK
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem lattice_of_lifts_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B hPin hRec jD eM hN hjD hSum w j hne h1 h2
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, j = (i : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  have hgrp := P.tied.div.grp
  have hIe : P.I.eG = B.Q.Rl.eG.trans B.Q.cG := hPin.eGtie
  have hC : ∀ h, (Formalism.L2.DIV.idemOf P.A3.A.X).coeff h = ((D.nexp.eLL0 (P.I.eG h) : D.LL0) : D.what₂.LL) := fun h =>
    D.what₂.embLL.injective ((hgrp.e0 h).trans (D.nStage_trivialCharacter_coeff_eq _).symm)
  obtain ⟨e, he1, he2⟩ := stage2 (w := w) hN P.I.eG B.Q.Sx ((i : ℕ) + 1) (B.Q.Rl.FW i) (B.Q.nexp.fi i) (B.fw.ks i)
    (fun s => by rw [hIe]; exact B.Q.nexp.geq i s) (B.Q.nexp.rho _ h1 h2) (B.Q.nexp.chi _ h1 h2)
    (B.Q.nexp.eF _ _ _ h1 h2) (B.Q.nexp.act _ _ _ h1 h2) (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) hC P.P0 P.ψ0⁻¹
    hgrp.lvl0 (fun u hu => by
      obtain ⟨x, hx1, hx2⟩ := hgrp.psi0 u hu (ex.nch.twI w) (ex.nch.sd w)
      exact ⟨x, hx1, hx2⟩)
  have hd := _root_.Formalism.IndefR.finrank_WL_eq_dW B.Q i
  have hForm := isKsForm_of_iso (B.Q.nexp.fi i) (B.fw.ks i)
  have heM : ∀ x, eM w ((i : ℕ) + 1) x = e (jD ((i : ℕ) + 1) x) := by
    intro x
    obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hForm
    have hx : jD ((i : ℕ) + 1) x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    let f : Fin n → FmK B.Q.Sx ((i : ℕ) + 1) := fun k => ⟨b k, hbK k⟩
    have h5 := hSum w ((i : ℕ) + 1) h1 h2 x n a f ha.symm
    rw [h5, ← ha]
    exact (he1 n a f).symm
  have hWg : (B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) =
      B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i := rfl
  have hrange : Set.range (eM w ((i : ℕ) + 1)) =
      (fun y => e ((B.Q.nexp.fi i).e.symm y)) ''
        ((B.Q.Rl.FW i).Wgood P.P0 P.ψ0⁻¹ (fun g => (Formalism.L2.DIV.idemOf P.A3.A.X).coeff g) : Set _) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x), ?_, ?_⟩
      · rw [hjD i x _ (heq_cast hd ((P.JM.eW i).symm x))]
        rw [SetLike.mem_coe, hWg]
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Module.finBasis D.what₂.LL _ k).2
      · simp only [LinearEquiv.symm_apply_apply, heM]
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, hWg] at hy
      let Bs := Module.finBasis D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)
      let z : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL := Bs.equivFun ⟨y, hy⟩
      let x := P.JM.eW i (z ∘ Fin.cast hd.symm)
      have hH : HEq ((P.JM.eW i).symm x) z := by
        simp only [x, LinearEquiv.symm_apply_apply]
        exact (heq_cast hd.symm z).symm
      have h6 := hjD i x z hH
      have h7 : Formalism.IndefR.NX.jDL B.Q.Rl B.Q.F.lv2 i z = y := by
        simp only [Formalism.IndefR.NX.jDL, Fintype.linearCombination_apply]
        have h8 := Bs.sum_equivFun ⟨y, hy⟩
        have h9 : ((∑ k, Bs.equivFun ⟨y, hy⟩ k • Bs k : B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i) : Fin (B.Q.Rl.nW i) → D.what₂.LL) = y :=
          congrArg Subtype.val h8
        rw [AddSubmonoidClass.coe_finsetSum] at h9
        exact h9
      refine ⟨x, ?_⟩
      rw [heM]
      change e _ = e ((B.Q.nexp.fi i).e.symm y)
      rw [← h7, ← h6, LinearEquiv.symm_apply_apply]
  refine isLatIn_span (ex.nch.embW w) (integers_embed _) (eM w ((i : ℕ) + 1)) (Y.MjH ((i : ℕ) + 1)).L
    (Y.MjH_good _).2.1 (Y.MjH_good _).2.2 _ ?_
  rw [hrange]
  exact he2
end GlobalTheory.CompanionTheory.LatSpan
end
end
end
end
end GroupAverageFixedPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.lattice_family_adoption_second_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), NChTie D ex.nch → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → NForms.IsLatIn (Submodule.span (ex.nch.Oe w) (eM w j '' ((Y.MjH j).L : Set (Y.MjH j).V))) ((((NForms.V0 D (ex.nch.twI w) j (ex.nch.sd w)).restrictScalars (D.ntw.O (ex.nch.twI w))).baseChange (FractionRing (ex.nch.Oe w))).restrictScalars (ex.nch.Oe w)) := by
  first | exact @_root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt | exact _root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt | (intros; apply _root_.GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lattice_of_lifts_alt <;> assumption)
end
end
end

