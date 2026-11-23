module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AdmissibleOfTransported
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0044
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0045
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0877
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0301
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0047
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimesSmallAlongFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleOfTransported
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef
namespace Formalism.L2.SG.JoinSI
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Twist
variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (s : Bool) (σ : K →+* ℂ)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE)
end Twist
section At
variable {D : D7}
variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}
end At
section Ties
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}
theorem adm13_of_transported_join (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R)
    {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    {P' : CxData A} {fc : DefSub A → DefFace Bs}
    {eV : ∀ t, (Fin ((fc P'.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P'.EE →ₗ⋆[ℂ] (fc P'.zs).Sp.HH} {s : Bool} {σ : K →+* ℂ}
    (hM : P'.MIstar2 eV sEE) (J : JoinAt S.X S.G S.Y (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S) S.tr P' fc eV sEE s σ) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  adm13_of_colJoin hM J hF (S.hI hF) (_root_.Formalism.L2.SG.JoinSI.eHH_sEE_eq_conjHH_isometryOfJoin S hF) (_root_.Formalism.L2.SG.JoinSI.colJoinS_of_spectral_ties_real S hF) R.pin.buDef hon
end Ties
section Real
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
variable {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks}
theorem adm13_of_kernel_join (hM : (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).MIstar2 (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE) (J : _root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  _root_.Formalism.L2.SG.JoinSI.adm13_of_transported_join S hM J.toJoinAt hF hon
end Real
end Formalism.L2.SG.JoinSI
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EMEqThPe
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open Formalism.L2.Rows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.ClassSumLift
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}
  {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem indefDown_dW_eq_finrank_WL (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    (P.A3.indefDown P.S0).dW i = Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) := by
  have hz := Q.zs
  have hs := Q.s0
  have key : ∀ (Z : DefSub P.A3.fam3.amb3) (S' : IndefData (P.A3.side3 P.P0 P.ψ0 Z)), Z = P.Zs → HEq S' P.S0 →
      P.S0.dW i = S'.dW i := by
    intro Z S' h1 h2
    subst h1
    rw [eq_of_heq h2]
  exact key _ _ hz hs
theorem exists_sum_smul_eq_of_isKsForm (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (hk : (Q.Rl.FW i).IsKsForm)
    (v : Fin (Q.Rl.nW i) → D.what₂.LL) :
    ∃ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK Q.Sx ((i : ℕ) + 1)),
      (Q.nexp.fi i).e (∑ k, a k • (show ↥(Q.Sx.A ((i : ℕ) + 1)).WK from f k).1) = v := by
  obtain ⟨n, b, hb, -, -, -, hs⟩ := hk
  have hv : v ∈ Submodule.span D.what₂.LL (Set.range b) := by rw [hs]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hv
  refine ⟨n, a, fun k => (⟨(Q.nexp.fi i).e.symm (b k), ((Q.nexp.fi i).wk _).2 (by
    rw [LinearEquiv.apply_symm_apply]; exact hb k)⟩ : ↥(Q.Sx.A ((i : ℕ) + 1)).WK), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← ha]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  congr 1
  exact (Q.nexp.fi i).e.apply_symm_apply _
set_option synthInstance.maxHeartbeats 400000 in
theorem at_index_alt (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (hP : _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q)
    (hD : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I)
    (w : D.what₂.places.Pl) (i : Fin D.R.m) (h1 : 1 ≤ (i : ℕ) + 1) (h2 : (i : ℕ) + 1 ≤ D.R.m)
    (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (jD : (Y.MjH ((i : ℕ) + 1)).V → B.Q.Sx.WL ((i : ℕ) + 1))
    (hjD : ∀ (x : (Y.MjH ((i : ℕ) + 1)).V)
      (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL),
      HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD x) = jDL B.Q.Rl B.Q.F.lv2 i y)
    (eMj : (Y.MjH ((i : ℕ) + 1)).V → FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)]
      D.nexp.Fm (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w))
    (hsum : ∀ (x : (Y.MjH ((i : ℕ) + 1)).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx ((i : ℕ) + 1)),
      jD x = ∑ k, a k • (show ↥(B.Q.Sx.A ((i : ℕ) + 1)).WK from f k).1 →
      eMj x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          (B.Q.nexp.eF (ex.nch.twI w) ((i : ℕ) + 1) (ex.nch.sd w) h1 h2).symm
            ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k))
    (x : D.what₂.MtL (D.what₂.muTw w) ((i : ℕ) + 1)) (hx : x ∈ Idx.TjV D (D.what₂.muTw w) ((i : ℕ) + 1))
    (z : (Y.MjH ((i : ℕ) + 1)).V)
    (hz : Y.jM _ z = D.what₂.thetaP (D.what₂.muTw w) _ (D.what₂.jMt (D.what₂.muTw w) _ x)) :
    eMj z = NChoice.thPe D ex.nch w ((i : ℕ) + 1) (ex.nch.eMt w ((i : ℕ) + 1) x) := by
  have ht : P.I.tup (Qr.tupT (D.what₂.muAt w)) = D.what₂.muTw w :=
    (Qr.tupTie _ (Or.inr ⟨w, rfl⟩)).trans ((D.what₂.muAt_or w).resolve_left hw)
  obtain ⟨x', e1⟩ := exists_cast ((i : ℕ) + 1) _ _ ht x
  obtain ⟨c, rfl⟩ := (P.I.eMt i _).surjective x'
  obtain ⟨y, e2⟩ := exists_heq_fin (_root_.GlobalTheory.ClassSumLift.indefDown_dW_eq_finrank_WL B.Q i) (((P.A3.indefDown P.S0).θ i _).mulVec
        ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i _).mulVec c))
  obtain ⟨n, a, f, e3⟩ := _root_.GlobalTheory.ClassSumLift.exists_sum_smul_eq_of_isKsForm B.Q i (B.fw.ks i) (jDL B.Q.Rl B.Q.F.lv2 i y)
  rw [hP w i h1 h2 _ ht hw c x e1 hx y e2 n a f e3]
  apply hsum
  apply (B.Q.nexp.fi i).e.injective
  rw [e3]
  apply hjD
  have : z = P.JM.eW i (((P.A3.indefDown P.S0).θ i (Qr.tupT (D.what₂.muAt w))).mulVec
        ((lPrj D P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 P.Zs) i (Qr.tupT (D.what₂.muAt w))).mulVec c)) := by
    apply Idx.jM_inj Y
    rw [hz, P.tied.mjH.j_eq, ← hD.thTheta, e1]
    exact theta_cast _ _ _ ht _
  rw [this, LinearEquiv.symm_apply_apply]
  exact e2
end GlobalTheory.ClassSumLift
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.ClassSumLift.eM_eq_thPe_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S) (_ : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation B.Q) (_ : _root_.Formalism.IndefR.IndefiniteRealisationRecursion B.Q) (jD : ∀ j, (Y.MjH j).V →ₗ[D.what₂.LL] B.Q.Sx.WL j) (eM : ∀ w j, (Y.MjH j).V →ₛₗ[ex.nch.embW w] FractionRing (ex.nch.Oe w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) j (ex.nch.sd w)), DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I → _root_.GlobalTheory.ExportPin.IndefiniteClassSumCondition B.Q → (∀ (i : Fin D.R.m) (x : (Y.MjH ((i : ℕ) + 1)).V) (y : Fin (Module.finrank D.what₂.LL (B.Q.Rl.toRealDat.WL B.Q.F.lv2 false i)) → D.what₂.LL), HEq ((P.JM.eW i).symm x) y → (B.Q.nexp.fi i).e (jD ((i : ℕ) + 1) x) = jDL B.Q.Rl B.Q.F.lv2 i y) → (∀ w j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : (Y.MjH j).V) (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → FmK B.Q.Sx j), jD j x = ∑ k, a k • (show ↥(B.Q.Sx.A j).WK from f k).1 → eM w j x = ∑ k, ex.nch.embW w (a k) ⊗ₜ[D.ntw.O (ex.nch.twI w)] (B.Q.nexp.eF (ex.nch.twI w) j (ex.nch.sd w) h1 h2).symm ((1 : KB B.Q.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[B.Q.Sx.Ks] f k)) → ∀ w j, D.what₂.muAt w ≠ D.what₂.mu0 → 1 ≤ j → j ≤ D.R.m → ∀ x ∈ Idx.TjV D (D.what₂.muTw w) j, ∀ y : (Y.MjH j).V, Y.jM j y = D.what₂.thetaP (D.what₂.muTw w) j (D.what₂.jMt (D.what₂.muTw w) j x) → eM w j y = NChoice.thPe D ex.nch w j (ex.nch.eMt w j x) := by
  intro D L hT Gi Gl Kc Y cX ex Rc P Dcf Spf Zscf S B _ Qr jD eM hD hP hread hsum w j hw h1 h2 x hx y hy
  obtain ⟨i, rfl⟩ : ∃ i : Fin D.R.m, (i : ℕ) + 1 = j := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  exact _root_.GlobalTheory.ClassSumLift.at_index_alt B Qr hP hD w i h1 h2 hw (jD ((i : ℕ) + 1)) (fun x y h => hread i x y h) (eM w ((i : ℕ) + 1))
    (fun x n a f h => hsum w ((i : ℕ) + 1) h1 h2 x n a f h) x hx y hy
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EWCastSymmWtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_equivariance_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ → ∀ (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y y' : ↥Y.C), (F' : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : Y.A) = Y.ρ g y → _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (GlobalTheory.ThetaTri.valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' y' = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ φ F y := by
  first | exact @_root_.GlobalTheory.ThetaTri.lamI_inv_alt | exact _root_.GlobalTheory.ThetaTri.lamI_inv_alt | (intros; apply _root_.GlobalTheory.ThetaTri.lamI_inv_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenActionAtGoodPoint
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.PassOp
open Formalism.MainNotions.N.PlaceLabelTeichmuller
section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
end Tensor
local instance  (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
local instance  (D : D7) (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
theorem exists_isBCV_twistIso_append_mu_of_mem_Z (D : D7) (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i) (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) :
    ∃ Sig, IsBCV D.nd D.naut i PI
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) := by
  obtain ⟨P0, hP0, Pa0, hB0, hm⟩ := (D.Z_tie i x).1 hx
  obtain ⟨Pa, hB⟩ := h1 i PI
  have hperm : Pa0.Perm Pa := ((h41 i).2.1 P0 PI (by rw [hP0]; exact Option.some_ne_none x)
    (hP0.trans hPI.symm)).1 Pa0 Pa hB0 hB
  have hm' := hperm.subset hm
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm'
  set m : Part D.naut.CG := ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ with hmdef
  have hperm2 : (l₁ ++ m :: l₂).Perm ((l₁ ++ l₂) ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hB' := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm2 hB
  have hL : ∀ p ∈ l₁ ++ l₂, 1 ≤ p.a := fun p hp => (hB.1 p (by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  refine ⟨twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT, ?_⟩
  have e : twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
      D.naut.etaTinv = (l₁ ++ l₂) ++ [m] := by
    rw [show twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT ++ [muPart D.nd D.naut i])
        D.naut.etaTinv = twistIso D.nd D.naut (twistIso D.nd D.naut (l₁ ++ l₂) D.naut.etaT) D.naut.etaTinv ++
          twistIso D.nd D.naut [muPart D.nd D.naut i] D.naut.etaTinv from List.map_append ..,
      twistIso_eta D h0.1 h5.1 _ hL]
    rfl
  rw [e]
  exact hB'
theorem onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem (D : D7) (Q : PairedCharacterCondition.Pend D) (hSer : GlobalTheory.TypeLeaf.SerLoc D) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D)
    (h0 : SumRepresentations.tie0 D) (h1 : SumRepresentations.adm1 D) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (x : D.nd.X i) (hx : x ∈ D.nd.Z i)
    (PI : D.naut.AV i) (hPI : D.naut.ptV i PI = some x) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) :
    (x ∈ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
    (x ∉ D.nd.Zgood i → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := by
  have hon : ∀ σ' : D.ntypes.Par, F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' →
      (D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F) ∧
      (¬ D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0) := fun σ' hF' =>
    idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => hSer i σ' k v f F hF' hf
  have hmem : ∀ Sig (σ' : D.ntypes.Par), (∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut Sig w) →
      IsBCV D.nd D.naut i PI (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) →
      F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
    intro Sig σ' hσ hB
    have hle : D.naut.typeV i PI ≤ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ' := by
      rw [D.mtpar_tie i σ']
      exact le_iSup₂_of_le PI ⟨Sig, fun w => (hσ w).symm, hB⟩ le_rfl
    exact hle hF
  constructor
  · intro hg
    obtain ⟨-, Sig, ⟨P2, hP2, hB2⟩, hgs⟩ := (D.Zgood_tie i x).1 hg
    obtain ⟨Pa, hB⟩ := h1 i PI
    have hperm := ((h41 i).2.1 P2 PI (by rw [hP2]; exact Option.some_ne_none x)
      (hP2.trans hPI.symm)).1 _ Pa hB2 hB
    have hBPI := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨P2, hP2, hB2⟩
    exact (hon σ' (hmem Sig σ' hσ hBPI)).1 ((goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).2 hgs)
  · intro hg
    obtain ⟨Sig, hB⟩ := _root_.GlobalTheory.PassOp.exists_isBCV_twistIso_append_mu_of_mem_Z D h0 h1 h5 h41 i x hx PI hPI
    obtain ⟨σ', hσ⟩ := Q.Par_surj i x Sig ⟨PI, hPI, hB⟩
    refine (hon σ' (hmem Sig σ' hσ hB)).2 fun hgp => hg ?_
    rw [D.Zgood_tie i x]
    exact ⟨(D.Z_tie i x).1 hx, Sig, ⟨PI, hPI, hB⟩, (goodPar_iff_goodSig D Sig σ' fun w => (hσ w).symm).1 hgp⟩
theorem main_alt_alt : ∀ (D : D7) (Q : PairedCharacterCondition.Pend D), GlobalTheory.Pass.EigSpan Q → GlobalTheory.Pass.CentralElt D → GlobalTheory.TypeLeaf.SerLoc D →
    _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → SumRepresentations.tieLab D → SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm5 D → KillingConditions.CommutingEndomorphismCondition D := by
  intro D Q hEig hCen hSer h41 _ h0 h1 h5 i _ _
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  have hact : ∀ F, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
    intro F
    rw [hz]
    unfold NTypes.onMt
    rw [dite_eq_left (Subalgebra.smul_mem _ hcen _), dite_eq_left hcen, ← LinearMap.smul_apply, ← map_smul]
    rfl
  refine ⟨Q.zO i z, Q.zO_comm i z, ?_, ?_⟩
  · intro x hx u hu
    have hZ : x ∈ D.nd.Z i := (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
    have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
      rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hZ PI hPI F hF).1 hx, map_natCast]) u hu
    rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
  · intro x hx hxg u hu
    have := hEig i z x 0 (fun PI hPI F hF => by
      rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg, smul_zero, map_zero, zero_smul]) u hu
    rw [this, zero_smul]
end GlobalTheory.PassOp
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenAtInert
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.EigInert.exists_satAt_of_nonsplit_over : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (P' : D.naut.AV i) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (w : HeightOneSpectrum (𝓞 D.host.E)), NG.OverPl w v → ¬ Formalism.BasicNotions.IsSplitPl D.host w → ∀ Dv : InertDatum D.host.E D.R.nV v w, ∃ α, NG.SatAt (P.H.av.rep i P') Dv α ∧ D.naut.satV i P' w = Multiset.map α Finset.univ.val := by
  intro hL D P i P' v w hov hns Dv
  have hsph := D.nbc.embAV_sph i P' w hns
  rw [P.H.emb i P'] at hsph
  have hS : (P.H.av.rep i P').SphericalAtPlace v := (P.H.au.sph (D.nd.j i) _ _ (P.H.av.rep i P') w v hns hov).1 hsph
  obtain ⟨α, hα, hsat⟩ := P.H.au.sat (D.nd.j i) _ _ (P.H.av.rep i P') v w hov Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_sphAtG _ _ _ v w hov Dv hS)
  refine ⟨α, hα, ?_⟩
  rw [D.nbc.embAV_sat, P.H.emb]
  exact hsat
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.EigInert.eigen_at_inert_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, h Pp (Finsupp.single d 1) y = c • y := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hops Pp hG hin d hd
  classical
  have hns : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield D Pp hin
  obtain ⟨v, Dv, hov⟩ := _root_.GlobalTheory.InertDatumAtInert.main D hA.hF Pp hin
  have hfix := _root_.GlobalTheory.T.operator_eigen_good_place_first_alt hAF hL D P X hA h41 h7 htl i hμ j hj h hops Pp hG hin v hov
  obtain ⟨h0, hh0, htr⟩ := _root_.GlobalTheory.T.operator_eigen_good_place_second_alt hAF hL D P X hA h41 h7 htl i hμ j hj h hops Pp hG hin d hd v Dv hov
  obtain ⟨C, a, xs, hC⟩ := GlobalTheory.EigInert.heckeFunI_umax_sum Dv h0 hh0
  let c : ℂ := if hP : ∃ P0 : D.naut.AV i, D.naut.ptV i P0 = some x then
    Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 (_root_.GlobalTheory.EigInert.exists_satAt_of_nonsplit_over hL D P i hP.choose v Pp hov hns Dv).choose else 0
  refine ⟨c, htr f y c hy (hfix (hj ▸ f)) ?_⟩
  have key : ∀ g ∈ eigC D.nd D.naut i x, heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real g) =
      c • (P.M.loc i).real g := by
    intro g hg
    unfold eigC at hg
    refine Submodule.iSup_induction _ (motive := fun g => heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0
      ((P.M.loc i).real g) = c • (P.M.loc i).real g) hg ?_ ?_ ?_
    · intro P' g' hg'
      by_cases hP' : D.naut.ptV i P' = some x
      · rw [iSup_pos (show P' ∈ {P | D.naut.ptV i P = some x} from hP')] at hg'
        have hex : ∃ P0 : D.naut.AV i, D.naut.ptV i P0 = some x := ⟨P', hP'⟩
        have hc : c = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV _ v) h0 (_root_.GlobalTheory.EigInert.exists_satAt_of_nonsplit_over hL D P i hex.choose v Pp hov hns Dv).choose := dif_pos hex
        obtain ⟨α', hα', hsv'⟩ := _root_.GlobalTheory.EigInert.exists_satAt_of_nonsplit_over hL D P i P' v Pp hov hns Dv
        have hsv0 := (_root_.GlobalTheory.EigInert.exists_satAt_of_nonsplit_over hL D P i hex.choose v Pp hov hns Dv).choose_spec.2
        have hub : ubc D.R.nV (D.naut.satV i P' Pp) = ubc D.R.nV (D.naut.satV i hex.choose Pp) := by
          have h41i := (show _root_.Formalism.MainNotions.SumRepresentations.At.provisionFortyOne D.nd D.naut i from h41 i).2.1 P' hex.choose (by rw [hP']; simp) (by rw [hP', hex.choose_spec])
          have hS : Pp ∉ D.nd.S i := fun hm => hns (D.nd.SQ_split i Pp (Or.inl hm))
          have hQ : Pp ∉ D.nd.Q i := fun hm => hns (D.nd.SQ_split i Pp (Or.inr hm))
          exact (h41i.2 Pp hS hQ).2 hns
        rw [hsv', hsv0] at hub
        have hW := _root_.GlobalTheory.InertUbcSatake.satU_eq_of_ubc_eq _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α' _ hub h0 hh0
        rw [hc, ← hW]
        have hmem : (P.M.loc i).real g' ∈ NG.isoTyp (P.H.av.rep i P').ρ (P.H.av.rep i P').S := by
          have h2 := hg'
          rw [P.H.av.typeV] at h2
          exact h2
        exact _root_.GlobalTheory.EigIsoInert.eig_of_isoTyp_fixed _ _ (P.H.av.rep i P') v Pp hov Dv α' hα' _ hmem (hfix g') h0 hh0
      · rw [iSup_neg (show P' ∉ {P | D.naut.ptV i P = some x} from hP')] at hg'
        rw [(Submodule.mem_bot ℂ).1 hg']
        simp [hC]
    · simp [hC]
    · intro g1 g2 h1 h2
      rw [hC] at h1 h2 ⊢
      simp only [map_add (f := _), smul_add, Finset.sum_add_distrib, h1, h2]
  exact key _ hf
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSetupLarge
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem exists_setup_large_alt : Hypotheses₂ → ∀ {eps : ℝ} (Fm : FamP eps), ∀ (C C₂ : ℝ) (CT : ℕ), TwGood Fm → _root_.GlobalTheory.NLink.FactsFAlt Fm C CT → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), TwistedPlaces.ShaFinOdd (Fm.D x i) → ∀ exc : Finset ℕ, ∃ (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW) (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)), X.exc = exc ∧ _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt (Fm.L x i) ∧ _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ := by
  intro hP eps Fm C C₂ CT hTw hF
  obtain ⟨i0⟩ := Fm.Ix_zero
  have he : 0 < eps := Fm.L_eps 0 i0 ▸ (Fm.L 0 i0).sc.eps_pos
  obtain ⟨xa, hxa⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) he
  obtain ⟨xb, hxb⟩ := _root_.GlobalTheory.SpecialSmall.special_primes_small Fm 1 le_rfl
  obtain ⟨xc, hxc⟩ := hTw
  refine ⟨max xa (max xb xc), fun x hx hx1 i hsha exc => ?_⟩
  have hxa' : xa ≤ x := le_trans (le_max_left _ _) hx
  have hxb' : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxc' : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, N0, S, hgood⟩ := hxc x hxc' hx1 i
  obtain ⟨hfa, -⟩ := hF x hx1 i
  obtain ⟨HW, F, ⟨Cm⟩⟩ := _root_.GlobalTheory.HWL.exists_hw_fon_cmp_of_integral hP.bs (Fm.D x i)
  have hCLw : (Fm.params x hx1 i).CLw ≤ Fm.PK.getD 7 0 := by
    rw [← Fm.params_K x hx1 i]
    exact le_refl _
  have hsx : xa ≤ (Fm.L x i).sc.x := by rw [Fm.L_x x i hx1]; exact hxa'
  obtain ⟨hpar, hpar67⟩ := hxa (Fm.D x i) (Fm.L x i) (Fm.params x hx1 i) (Fm.L_eps x i) hCLw hsx
  obtain ⟨X, hcan, -, hexc, hI, -⟩ := _root_.GlobalTheory.HubX.exists_canonical_hubData_with_bounds GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.L x i) HW (rowC C₂)
    hfa.adm.1.1.2.2.2.1 hfa.Conclusion1.1 (fun _ _ _ _ => 0) (fun _ => exc) ⟨twE Fm x hx1 i, N0, S⟩
  obtain ⟨-, hbig, hsplit, -⟩ := hxb x hxb' hx1 i
  have hrow : GlobalTheory.PtCore.GoodPtRow (Fm.D x i) :=
    GlobalTheory.Proof.LocalGlobalAssembly.main _ hfa.adm.1.1.1 hfa.Conclusion1.2.2 hfa.Conclusion2.2.2
  have h6 := GlobalTheory.JointSix.main GlobalTheory.Published.cheb_holds (Fm.D x i) (Fm.ex x hx1 i).nch X.r X.ρ hcan.fam hfa.nct hfa.trip
    hfa.same hrow (GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred _ hfa.rhoBar)
  have hkill : KillingConditions.KillAt X.ρ := _root_.GlobalTheory.NLink.twist_kills_selmer (Fm.D x i) (Fm.ex x hx1 i).nch X.I X.ρ hfa.nct (hI ▸ hgood) h6
  exact ⟨HW, F, Cm, X, hexc, hfa.admJ _ hpar, ⟨hfa, hcan, hpar, hpar67, hbig, hsplit, hkill, hsha⟩⟩
end GlobalTheory.NLink
end
end

