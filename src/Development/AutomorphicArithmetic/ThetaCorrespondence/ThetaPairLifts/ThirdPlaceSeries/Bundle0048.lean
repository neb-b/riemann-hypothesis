module

public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0303
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Formalism.LocalToGlobal.Bundle0002
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
open Classical in
structure IndefiniteRealisationNormalisation {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop where
  cfEq : Q.Rl.C = Rc.T.n.cf
  qGuard : Formalism.IndefR.FWT.QGuard Q.Rl.toRealDat
  hF : D.host.F = maximalRealSubfield D.host.E
  phsOne : ∀ i, Q.Rl.phs i = 1
  prXunit : Formalism.IndefR.Seed.PrIso Q.Rl.MX Q.Rl.cX Q.Rl.prX
  grpRecPin : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Q.Rl.toRealDat.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : Q.Rl.toRealDat.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf P.A3.A.X).coeff g) = D.ntypes.e0.coeff ((Q.Rl.eG.trans Q.cG) g)) ∧
    (∀ kv, Q.Rl.toRealDat.C.P.Div kv.1 (plg kv).1) ∧
    ∀ g kv, Q.Rl.toRealDat.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((Q.Rl.eG.trans Q.cG) g kv)
  fdiag : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)
  pgEq : Q.Rl.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE)
  tSfin : Q.tS ∈ Formalism.L2.Theta.GfC (Yc D 0)
  tSpin : (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel Q.tS⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq Q.tS
  eGtie : P.I.eG = Q.Rl.eG.trans Q.cG
  betaStd : (∀ i, Q.Rl.βV i = 1) ∧ Q.Rl.βX = 1
  bR_read : ∀ x i, Q.bR x i = D.eMu (Q.wdD x) (D.jN (Q.wdD x) (P.I.eNu (Q.wdD x)
    (Pi.single (Fin.cast (congrArg P.Dc.a (Q.wU_wdD x)).symm i) 1)))
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def IndefiniteRealisationExtends (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop :=
  (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) ∧
    ∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Q.Rl.MY 0) Q.Rl.ν0 Q.Rl.fd0 (Q.Rl.toRealDat.EEat (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G Q.ιS Q.tS c'
end Formalism.IndefR
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem finrank_WL_eq_dW (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) = (P.A3.indefDown P.S0).dW i :=
  congrFun (dW_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0) i
def indefiniteDownJoin (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (y : Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) :
    Fin (Q.Rl.nW i) → D.what₂.LL :=
  Formalism.IndefR.NX.jDL Q.Rl Q.F.lv2 i (y ∘ Fin.cast (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i))
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure IndefiniteRealisationRecursion (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Type 1 where
  tupT : D.what₂.Tup → P.T
  hm : 0 < D.R.m
  hTop : Formalism.IndefR.RecTie.TopMultH Q.Rl.toRealDat
  hinj : ∀ i t, Function.Injective (Q.Rl.toRealDat.extV i t)
  Ish : Formalism.IndefR.RecTie.RowIds (Formalism.BasicNotions.RowSide.sharp D) (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) true
  I0 : Formalism.IndefR.RecTie.RowIds ex.p0.s (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) false
  IL : Formalism.IndefR.RecTie.LiftIds (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj)
  Kc : Formalism.IndefR.RecTie.ColReal D
  E : EigIdx D Y
  labPi : E.Pi → P.A3.A.fam.base.Ix
  PY : Formalism.IndefR.principalLevelFrame.RowPsi (Yc D 0) D.R.r
  PW : ∀ i, Formalism.IndefR.principalLevelFrame.RowPsi (Wc D i) D.R.r
  eFT : D.what₂.FT ≃ Formalism.IndefR.principalLevelFrame.FTR Q.Rl.θ PY (Q.Rl.MY 0)
    (fun b => levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b)))
    (fun b => Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b))) (fun _ => Q.Rl.e0)
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  ιW : ∀ i, ↥(Formalism.L2.Theta.GfC (Yc D 0)) →* ↥(Formalism.L2.Theta.GfC (Wc D i))
  Tp : Formalism.L2.Host.TupTied D Q.Rl.C ex.nch
  recR : Formalism.IndefR.RecTie.RecReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj ex.p0 Ish I0 IL Kc E labPi PY PW eFT piOf ιW ex.nch Tp
  tpEq : HEq Tp Rc.T.n.tp
  tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ
  tupT_tup : ∀ t, tupT (P.I.tup t) = t
  muEq : Q.Rl.mu = P.S0.μ
  mtRead : Formalism.IndefR.RecTie.MtRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (twPOf P tupT tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (fun i => (P.A3.indefDown P.S0).dW i)
    (fun i y => P.I.jW i y) (_root_.Formalism.IndefR.indefiniteDownJoin Q)
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q)
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupT_inj_used {μ μ' : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (hμ' : Formalism.IndefR.RecTie.Used0 D μ')
    (h : Qr.tupT μ = Qr.tupT μ') : μ = μ' := by
  apply Qr.Tp.xi_inj
  rw [← Qr.recR.tupXi μ hμ, ← Qr.recR.tupXi μ' hμ', h]
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupleRead_baseTuple_eq_family : Qr.tupT D.what₂.mu0 = P.A3.A.μ0 :=
  Q.charW.base.lev.xi_inj (by rw [Qr.recR.tupXi D.what₂.mu0 (Or.inl rfl), Qr.Tp.trueColumnChoices_heckeChar_reference_eq_one, Q.charW.base.lev.xi_base])
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tw_iff (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) (w : D.what₂.places.Pl) : D.plEq w ∈ Q.Rl.twPl ↔ D.what₂.muAt w ≠ D.what₂.mu0 := by
  have h0 := Qr.tupleRead_baseTuple_eq_family
  constructor
  · intro hw he
    apply Q.charW.tup.mu_ne (D.plEq w) hw
    rw [← Qr.recR.tupAt w, he, h0]
  · intro hne
    by_contra hw
    apply hne
    apply Qr.tupT_inj_used (Or.inr ⟨w, rfl⟩) (Or.inl rfl)
    rw [Qr.recR.tupAt w, Q.charW.tup.mu_off (D.plEq w) hw, h0]
end RealRec
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
def _root_.Formalism.IndefR.IndefiniteRealisationRecursion.PartsRow (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) : Prop :=
  Formalism.IndefR.RecTie.PartsRec Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.PY Qr.PW Qr.eFT Qr.E Qr.labPi Qr.piOf Qr.Ish.prt Qr.IL.prtW
end RealRec
end Formalism.IndefR
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InnerTheta
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaRead
open MeasureTheory Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
  Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.ThetaTri
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Pair
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
end Pair
section Unit
variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
end Unit
section Row
variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
end Row
section Forms
variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} {X : GlobalTheory.NJoin.RealAt D cf nch tp}
  {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
end Forms
section Canon
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)
set_option maxHeartbeats 1000000 in
theorem integral_theta_evaluation_thetaKO {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (Y : RowMod D P.rep k)
    (hc : GlobalTheory.NJoin.IsCanon X j hk Y) (x : D.what₂.Mt μ k) (y : D.what₂.Mj k) :
    inner ℂ y (D.what₂.thetaP μ k x) = (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) *
      ∫ g in X.R.fdW j, star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc ⟨Y.φ y, Y.φ_mem y⟩ g) *
        (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
          (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT μ) (X.fn hμ j (hk.symm ▸ x) h)) ∂(X.R.νV j (X.tupT μ))) ∂(X.R.νW j) := by
  subst hk
  obtain ⟨-, -, -, -, hB, hφ⟩ := Classical.choose_spec (Classical.choose_spec hc)
  refine (Y.φ_inner _ _).trans ((hB _ (Y.φ_mem _) _ (Y.φ_mem _)).trans (congrArg (fun z => (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) * z) ?_))
  exact ipM_theta X hμ j x y (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (Y.φ y)) (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (Y.φ (D.what₂.thetaP μ (j.1 + 1) x))) (hφ y) (hφ _)
end Canon
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (x : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (y : D.what₂.Mj (D.nd.j i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)), (F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = (P.M.loc i).real x → inner ℂ y (D.what₂.thetaP (D.nd.mu i) (D.nd.j i) x) = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (_root_.GlobalTheory.ThetaTri.standardSchwartzFunctionMap j (X.tupT (D.nd.mu i))) F ⟨Y.φ y, Y.φ_mem y⟩ := by
  intro hL D P X A i j hj Y hc hμ x y F hF
  have hf : _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F = X.fn hμ j (hj.symm ▸ x) := by
    refine Eq.trans ?_ (ext_real_cast X.given.core.models.cV A hμ j _ hj (D.nd.j_range i).1 (D.nd.j_range i).2 x)
    show (X.R.cV j).ext (fun k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm
      ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))) = _
    rw [hF]
    rfl
  rw [_root_.GlobalTheory.ThetaRead.integral_theta_evaluation_thetaKO X hμ j _ hj Y hc x y, ← hf]
  rfl
end GlobalTheory.ThetaRead
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NXNMjT
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR.NX
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
set_option synthInstance.maxHeartbeats 400000 in
def RealExpansionMajorant (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (cG : Formalism.L2.DIV.G0 Q.Rl.Pg D.R.r ≃* G0g D.nd) (Sd : RatDat D.ntw)
    (Yr : NExpRealS Q.Rl cG Sd) (c : NChoice D) :
    Prop :=
  ∃ jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] Sd.WL j,
    (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V)
      (y : Fin (Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i)) → D.what₂.LL),
      HEq ((P.JM.eW i).symm x) y → (Yr.fi i).e (jD ((i : ℕ) + 1) x) = jDL Q.Rl Q.F.lv2 i y) ∧
    Nonempty (NMjRR Q.Rl cG Sd Yr Y c jD)
end Formalism.IndefR.NX
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PassIn3AtRealT
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem passIn3_at_realT_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Del h0 : ℕ) (c : ℝ) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf (fun Zs => let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs; { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }) S Ks), IsTotallyComplex D.what₂.LL → Formalism.MainNotions.PrimeDegreeVariant.LevelRatioBound D → P.A3.fam3.Ok3 1 → PrimRows3 Q.Rl Q.F → ∀ C CH : ℝ, PassIn3 Q.Rl Q.F C CH := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Del h0 c S Ks _ _ _ Q hTC hadm hOk hP C CH
  haveI : IsTotallyComplex D.what₂.LL := hTC
  exact GlobalTheory.passIn3_of_rows D P.Gp P.Pl0 P.I0 P.T P.A3 Ks Q.Rl Q.F C CH Q.charW hOk hP
    (fun k => ⟨_, Rc.T.n.types.O k, Rc.T.n.types.eSer_def k⟩) hadm rfl rfl
end GlobalTheory
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRows
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.PtSt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy
theorem reducedMultiplicity_of_rows' :
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → _root_.GlobalTheory.NRows.PointConditions' D → SumRepresentations.ReducedMultiplicityStatement D := by
  intro hL D I R i _
  have hInt : Rows.IsotInternal D.what₂ := I.isot
  have h42 : SumRepresentations.Conclusion42 D := (I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) R.a R.b).2.2
  have h1 := map_MjSig_eq D i hInt (h42 i) (R.c.parUp i) (R.c.downMem i) (R.typeNZ i)
  exact ⟨h1, (SumRepresentations.good_part_image_iff D.nd D.naut i hInt (h42 i) h1).2 (R.c.goodPart i)⟩
end GlobalTheory.PtSt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtKOfReal
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.L2.RowDataTransport
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
abbrev packageOfPrimitiveLinks [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P Dcf Spf Zscf) Cl CHl) :=
  primitivePackageFullHecke hOk hsep Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl Q.charW hP hI
def InpAtAlt [_root_.NumberField.IsTotallyComplex D.what₂.LL] {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields}
    {e : X.Tau → (X.E →+* D.what₂.LL)} (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)} {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P c.face Sp Zsc S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P c.face Sp Zsc) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P c.face Sp Zsc) Cl CHl)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1) : Prop :=
  ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).Zs
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.base.toIndefData (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core.cols.col NuC I →
      HEq I P.I →
      ∃ inp : ∀ u, DivInputs0R (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q hOk hsep Cl CHl hP hI).core
          (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
          (I.wU u) (Cons.nuOf L u (I.eNu u)) (sgRec L u),
        ∃ hQ : ∀ u, ChainTie (inp u).ch (c.memQ (I.wU u)), ∀ u, FirstCols c.hE (hQ u)
theorem ptK_of_real_alt [_root_.NumberField.IsTotallyComplex D.what₂.LL] (Rc : _root_.Formalism.L2.RecTAlt ex) (R : _root_.Formalism.L2.DIV.DivisionKernelData ex) (hT : R.T = Rc.T)
    (hpin : _root_.Formalism.L2.Rows.RowSideDeterminedAlt Rc.T R.P) (hkap : RowsHoldKap3 R.P) (hPt : RowsHoldDcPt3 R.P)
    (hR : DivRows3 D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.P.Zs R.P.S0 R.P.S1 ex.p0 R.P.C R.P.NuC R.P.I) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc R.P R.c.face R.Sp R.Zsc S Ks) (hsep : R.P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT R.P R.c.face R.Sp R.Zsc) Q.sEE (hkCan R.P.A3) Cl CHl)
    (hI : PassIn3 Q.Rl (faceT R.P R.c.face R.Sp R.Zsc) Cl CHl)
    (C Cabs : ℝ) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : R.P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (hInp : _root_.Formalism.L2.RowDataTransport.InpAtAlt R.c Q R.ok1 hsep Cl CHl hP hI Del h0 lam0 C0 ce Ch Sw C1 eJ H)
    (hN : NprimeDef D L) (hh : ∀ u, D.div.h u = hExpl6 D L Y Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.c.face R.Sp R.Zsc
      (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs).Z.num Cl CHl) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    Nonempty (_root_.Formalism.L2.DIV.DivisionPackageKernel' R C Cabs) := by
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs = R.P.Zs := Q.zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.base.toIndefData R.P.S0 := Q.s0
  have hS1 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.cols.toIndefData R.P.S1 := Q.s1
  have hRows : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).core.base.toIndefRows (Classical.choose R.hr.rows0) :=
    rows_heq hZs _ _ (hS0.trans (heq_of_eq (Classical.choose_spec R.hr.rows0).symm))
  have hDc : HEq (R.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI).Zs) R.P.Dc :=
    (congr_arg_heq R.c.face hZs).trans (heq_of_eq R.colTie.1)
  exact _root_.Formalism.L2.DIV.pkg_of_rowsK_alt R hR C Cabs Cl CHl _ (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks Q R.ok1 hsep Cl CHl hP hI) hZs hRows hS1 Q.col
    Del h0 lam0 C0 ce Ch Sw C1 eJ H
    (fun NuC I hT' hI' => ⟨Formalism.L2.G.ServJointF.brTied_of hT' ⟨1, R.ok1.ok2⟩ (dcPt_move hPt hZs hDc hS0 hS1 hI'),
      hInp NuC I hT' hI'⟩)
    hN Y (fun σ => (hkap σ).trans (congrFun (kap_heq hZs hS1) _).symm) (fun u => ⟨rfl, HEq.rfl, rfl, hDel, hh0⟩) hh hF
    hC0 hC1 hC2 hCabs hLa
end Formalism.L2.RowDataTransport
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPins3Iff
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
structure IndefiniteRealisationNormalisationDegreeThree {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop where
  muDef : ∀ C CH : ℝ, (Q.Rl.toCx3 Q.F).MuDef Q.F.cr (Q.Rl.num Q.F C CH) Q.Rl.mu
namespace Pins3
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem muDef_iff_alt (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) :
    (Q.Rl.toCx3 Q.F).MuDef Q.F.cr (Q.Rl.num Q.F C CH) Q.Rl.mu ↔
      ∀ w, w ∈ Q.Rl.twPl ↔ (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w := by
  have ht := Q.charW.tup
  constructor
  · rintro ⟨_, _, _, h4⟩
    exact h4
  · intro h
    refine ⟨fun w hw => ht.mu_ne w ((h w).2 hw), fun w _ => ht.mu_conj w, fun w => ?_, h⟩
    show Q.Rl.mu w = _
    split_ifs with hw
    · rfl
    · exact ht.mu_off w fun hm => hw ((h w).1 hm)
theorem realPins3_iff_twPl_iff_W1 (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) :
    _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree Q ↔ ∀ w, w ∈ Q.Rl.twPl ↔ (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F 0 0) w :=
  ⟨fun h => (_root_.Formalism.IndefR.Pins3.muDef_iff_alt Q 0 0).1 (h.muDef 0 0), fun h => ⟨fun C CH => (_root_.Formalism.IndefR.Pins3.muDef_iff_alt Q C CH).2 h⟩⟩
end Pins3
namespace RealPins3
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
theorem _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree.w1 (h : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree Q) (C CH : ℝ) :
    ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl :=
  fun w hw => (h.muDef C CH).2.2.2 w |>.2 hw
end RealPins3
end Formalism.IndefR
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsUOfColPinsStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_columns_from_ties_alt : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  first | exact @_root_.GlobalTheory.ColRows.rowsU_of_colPins_alt | exact _root_.GlobalTheory.ColRows.rowsU_of_colPins_alt | (intros; apply _root_.GlobalTheory.ColRows.rowsU_of_colPins_alt <;> assumption)
end
end

