module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0427
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InclMulInvMul
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEmbFIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0459
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvSmulMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.R3.Rw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}


set_option maxHeartbeats 2000000 in
structure Ext (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') : Prop where
  H : HEq z'.core.Q.H z.core.Q.H
  l : HEq z'.core.Q.l z.core.Q.l
  c : HEq z'.core.Q.c z.core.Q.c
  Dw : HEq z'.core.Q.Dw z.core.Q.Dw
  Xo : HEq z'.core.Q.Xo z.core.Q.Xo
  U : HEq z'.core.U z.core.U
  V : HEq z'.core.V z.core.V
  dict : HEq z'.core.dict z.core.dict
  mu : HEq z'.core.mu z.core.mu
  Kf : HEq z'.core.Kf z.core.Kf
  cE : HEq z'.core.cE z.core.cE
  chiW : HEq z'.core.chiW z.core.chiW
  x₀ : HEq z'.core.x₀ z.core.x₀
  iota : HEq z'.core.iota z.core.iota
  ψ : HEq z'.R.ψ z.R.ψ
  θ : HEq z'.R.θ z.R.θ
  βW : HEq z'.R.βW z.R.βW
  βY : HEq z'.R.βY z.R.βY
  nW : HEq z'.R.nW z.R.nW
  βV : HEq z'.R.βV z.R.βV
  ΛV : HEq z'.R.ΛV z.R.ΛV
  ΛW : HEq z'.R.ΛW z.R.ΛW
  Pg : HEq z'.R.Pg z.R.Pg
  eG : HEq z'.R.eG z.R.eG
  Sb : HEq z'.R.Sb z.R.Sb
  BV : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.cV i').W (z.R.cV i).W ∧ HEq (z'.R.cV i').ρ (z.R.cV i).ρ ∧ HEq (z'.R.vacP i') (z.R.vacP i) ∧
    HEq (z'.R.ioP i') (z.R.ioP i) ∧ HEq (z'.R.ωP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq (z'.R.BV i') (z.R.BV i)
  MW : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).H (z.R.MW i (w.st Z).toD7.what₂.embLL).H ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).nacg (z.R.MW i (w.st Z).toD7.what₂.embLL).nacg ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).ips (z.R.MW i (w.st Z).toD7.what₂.embLL).ips ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).σ (z.R.MW i (w.st Z).toD7.what₂.embLL).σ ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).lam (z.R.MW i (w.st Z).toD7.what₂.embLL).lam ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).ε (z.R.MW i (w.st Z).toD7.what₂.embLL).ε ∧
    HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).fr (z.R.MW i (w.st Z).toD7.what₂.embLL).fr ∧ HEq (z'.R.MW i' (w'.st Z').toD7.what₂.embLL).enum (z.R.MW i (w.st Z).toD7.what₂.embLL).enum ∧
    HEq (z'.R.HW i' (w'.st Z').toD7.what₂.embLL) (z.R.HW i (w.st Z).toD7.what₂.embLL) ∧
    HEq (z'.geo.v₀ i' (w'.st Z').toD7.what₂.embLL) (z.geo.v₀ i (w.st Z).toD7.what₂.embLL) ∧
    ∀ φ φ', HEq φ' φ → HEq ((z'.R.FW i').j (w'.st Z').toD7.what₂.embLL (z'.geo.fw.e i' φ' : (z'.R.FW i').WK).1)
      ((z.R.FW i).j (w.st Z).toD7.what₂.embLL (z.geo.fw.e i φ : (z.R.FW i).WK).1)
  forms : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
    ∀ (k : Fin (z.R.nW i)) (k' : Fin (z'.R.nW i')), (k : ℕ) = k' →
      (w'.st Z').toD7.what₂.embLL ((z'.geo.fw.e i' φ' : (z'.R.FW i').WK).1 k') =
        (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)
  W1 : ∀ v v', Below (w.D Z) (w'.D Z') v v' → (v ∈ z.W1 (fun _ _ => 0) ↔ v' ∈ z'.W1 fun _ _ => 0)
  cV : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.cV i').nW (z.R.cV i).nW ∧ HEq (z'.R.cV i').iW (z.R.cV i).iW
  pb : HEq z'.core.pb z.core.pb
  ΛY : HEq z'.R.ΛY z.R.ΛY
  κ : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.geo.κ i').aP (z.geo.κ i).aP ∧ HEq (z'.geo.κ i').aM (z.geo.κ i).aM ∧ (z'.geo.κ i').n = (z.geo.κ i).n
  ref : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (z'.R.vP i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.HV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.thF i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.thG i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.νV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.fdV i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt')))) (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq (z'.R.νW i') (z.R.νW i) ∧ HEq (z'.R.fdW i') (z.R.fdW i)
  jL : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok)
      (ok' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).Ok)
      (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (φ' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).EqFun),
      (∀ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (φ'.1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 d).1)) →
      HEq (z'.R.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))).1 ((i' : ℕ) + 1)).res ok' φ' :))))
        (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))))


def Fine (z : Dat (w.st Z) w.I hX T Wt) : Prop := z.R.toRealDat.ExAt ∧ GlobalTheory.RealGeo.InGeo z.geo ∧ CoreP z ∧ z.Std

def DatExS : Prop := StepW Pinned fun _ B f T w => ∀ (Z : w.Lt) (hX : B.fields.Ok), GrpTrue Z.N f → GrpAt (w.st Z) w.I →
  VolTieG (w.D Z) → ∃ z : Dat (w.st Z) w.I hX T {v | B.places.resChar v ∈ T.pl}, Fine z

def DatExt : Prop := StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∃ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' ∧ Ext z z'

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.StdModel

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

section Ker

variable {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)}
    {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX}

theorem stdKer_iff (t : KerEntTied ex) : I.StdKer l Z t ↔ I.StdKerTie l Z t :=
  ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩,
    fun ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, m, n, o, p⟩⟩

end Ker

section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

end Tw




section Frames

open GlobalTheory.Mem.FormSym


end Frames

end GlobalTheory.Mem.Col2.StdModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IntertwinersExistScalarUpdateInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.ResEx

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

open GlobalTheory.Mem.R3.Res

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 2000000 in
theorem baseWeight_scalar_update_invariant {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} {F : Face D A} (h : R.BaseW F) (k l) :
    (R.upd6 k l).BaseW F :=
  ⟨h.lev, ⟨h.grp.red_R, h.grp.red_L, h.grp.levels, h.grp.record, h.grp.chiW⟩,
    ⟨h.fam.tie, h.fam.Sb, h.fam.roots, h.fam.pl_onto, h.fam.degR, h.fam.degL, h.fam.muVal, h.fam.etaVal⟩,
    ⟨h.models.inf, h.models.vpos, h.models.cX, h.models.cV, h.models.prX, h.models.HX, h.models.HV, h.models.HE, h.models.HW,
      h.models.gE, h.models.gW, h.models.jX, h.models.jV, h.models.νY, h.models.νY', h.models.ν0, h.models.νX, h.models.νV,
      h.models.νW, h.models.BV, h.models.order⟩, RealDat.weak_chain_of_scalar_update h.chain k l, RealDat.weak_theta_props_of_scalar_update h.thP k l⟩


set_option maxHeartbeats 2000000 in
theorem intertwinersExist_scalar_update_invariant {A : FamIn D.what₂.LL G Pl0 T D.R.m} {R : RealDat D A Ks} (e : R.ExAt) (k l) : (R.upd6 k l).ExAt :=
  ⟨e.ItY, e.ItX, e.ioY, e.ioX, e.Th, e.ioP, e.thF, e.thG⟩


set_option maxHeartbeats 2000000 in
theorem nz_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (k l) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ)
    (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    (∃ j, NzAt (R.updS k l) F F0 j w ∨ NzAt (R.updS k l) F F0 j (Formalism.DivisionValues.conjPl w)) ↔
      ∃ j, NzAt R F F0 j w ∨ NzAt R F F0 j (Formalism.DivisionValues.conjPl w) :=
  (complexSide_nonzeroIndexPlaces_iff_self (R.updS k l) F { R.num F 0 0 with F0 := F0 } w).symm.trans
    (complexSide_nonzeroIndexPlaces_iff R F k l R.err0 F.Dc F.Sp F.Zsc { R.num F 0 0 with F0 := F0 } w)


open Classical in
def kapOf (S : RealDat3 D A3 Ks) : ℝ :=
  if h : ∃ κ, Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
      ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0 then h.choose else S.kap

theorem kapOf_eq (S : RealDat3 D A3 Ks) (κ : ℝ)
    (hκ : Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ)
    (hn : ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0) : kapOf S = κ := by
  have h : ∃ κ, Lift.IsKap D.R.m (fun t => S.Th t ∘ₗ LinearMap.adjoint (S.Th t)) S.EEp3 S.lamN κ ∧
      ∃ t p, S.EEp3 p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 D.R.m, S.lamN t j p ≠ 0 := ⟨κ, hκ, hn⟩
  obtain ⟨t, p, hp, hl⟩ := hn
  unfold kapOf
  rw [dite_eq_left h]
  exact Lift.IsKap.unique h.choose_spec.1 hκ t p hp hl


set_option maxHeartbeats 2000000 in
theorem isScal_kapOf (S : RealDat3 D A3 Ks) (F : Face3 D A3) (h0 : S.eigenvalue_at_base_of_scalar) (h1 : S.scal_off F) (h2 : S.zero_part_eigenvalue_convention F)
    (h3 : S.scal_abs F) (h4 : S.scal_tup) : (S.updS (kapOf S) S.lam3).IsScal F := by
  refine ⟨h0, fun κ h h' => kapOf_eq S κ h h', fun i p v l hv hp he => ?_, fun i t p hp => ?_, fun i p v hv hp => ?_, h4⟩
  · exact h1 i p v l hv ((RealDat3.partAt_updS _ _ _ _ _).1 hp) ((RealDat3.sim_updS _ _ _ _ _ _).1 he)
  · rw [RealDat3.zs_updS]
    exact h2 i t p hp
  · rw [RealDat3.zs_updS]
    exact h3 i p v hv fun hl => hp ((RealDat3.partAt_updS _ _ _ _ _).2 hl)

variable {f : T' → T} {μ : T'} {R : RealDat3 D (A3.comap id (f μ)) Ks} {mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T'}
  {tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}


set_option maxHeartbeats 4000000 in
theorem pins_updS (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) (k l) (hs : ((dat3 f μ R mu tw).updS k l).IsScal (bare3 _ P0 ψ0 P1 ψ1)) :
    Pins ((dat3 f μ R mu tw).updS k l) (bare3 _ P0 ψ0 P1 ψ1) cG := by
  have i := isInert mu tw h.char.inert
  have u := isTup hf h.char.tup n
  have kv := keep mu tw h.keep
  exact ⟨⟨baseWeight_scalar_update_invariant (baseW (A := A3.A) mu tw hf h.char.base e) k _, ⟨i.tie, i.onto, i.hR, i.hL, i.SF⟩,
      fun t => h.char.fullY (f t), fun t => h.char.fullX (f t), fun i t => h.char.fullP i (f t), hs,
      ⟨u.mu_off, u.mu_used, u.mu_ne, u.mu_conj, u.mu_on⟩, h.char.phase, h.char.allPl⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩, h.phs, h.trSem⟩


set_option maxHeartbeats 4000000 in
theorem pins_kapOf (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (n : NewTup R mu tw) :
    Pins ((dat3 f μ R mu tw).updS (kapOf (dat3 f μ R mu tw)) (dat3 f μ R mu tw).lam3) (bare3 _ P0 ψ0 P1 ψ1) cG :=
  pins_updS hf h e n _ _ (isScal_kapOf _ _ (fun i t => h.char.scal.lam0 i (f t)) h.char.scal.off
    (fun i t => h.char.scal.abs0 i (f t)) h.char.scal.abs fun i t => h.char.scal.tup i (f t))

end Generic

section Record

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' : Set X.B.places.Pl}



set_option maxHeartbeats 4000000 in
theorem exAt_res (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (e : z.R.toRealDat.ExAt) : (z.resR h).toRealDat.ExAt :=
  Res.exAt (A := (famR X I hX (usedOf I T Wt) z.Xg z.tr).A) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R.toRealDat) (z.resMu h) (z.resTw Wt') e



set_option maxHeartbeats 4000000 in
theorem pins_resK (z : Dat X I hX T Wt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt') (e : z.R.toRealDat.ExAt) :
    Pins ((z.resR h).updS (kapOf (z.resR h)) (z.resR h).lam3) (face0 X I hX (usedOf I T Wt') z.Xg z.tr) z.cG := by
  have hp := z.pins
  rw [columnChoiceReferenceFace_eq_bareFaceTwoLevels] at hp ⊢
  exact pins_kapOf (A3 := famR X I hX (usedOf I T Wt) z.Xg z.tr) (Ks := z.core.Q.c.F) (f := inclU I (usedOf_mono I T h))
    (μ := mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt'))) (R := z.R) (P0 := lev0 I) (ψ0 := chr0 I) (P1 := lev1 I) (ψ1 := chr1 I)
    (mu := z.resMu h) (tw := z.resTw Wt') (inclU_injective (usedOf_mono I T h)) (cG := z.cG) hp e (z.newTup h hc)


variable (z : Dat X I hX T Wt) (e : z.R.toRealDat.ExAt) (h : Wt' ⊆ Wt) (hc : ConjStable X Wt')





end Record

end GlobalTheory.Mem.R3.ResEx

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3.ResTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B}
  {Wt Wt' Wt'' : Set X.B.places.Pl} (z : Dat X I hX T Wt)





end GlobalTheory.Mem.R3.ResTest

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesOfLifts
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.StateChecks

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Wt : Set B.places.Pl}

section Types

variable {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 T₀ : Type}
  {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m}
  {R : RealDat a.D A Ks} (F : Face a.D A) (y : Hd R) (y' : HdB b R) (E : Hs)

end Types

section Std

variable {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))


set_option maxHeartbeats 2000000 in
theorem std_cpR (z : Dat a.st I hX T Wt) (h : z.Std) :
    @BrgStd b.st px I hX (usedOf I T Wt) z.Xg z.tr (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Formalism.L2.Pj.instCMHost (@Late.st B C a).toD7) (@Formalism.L2.Pj.Par.H (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.l (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Formalism.L2.Pj.Par.c (@Late.st B C a).toD7 (@Formalism.L2.Pj.Core.Q (@Late.st B C a).toD7 (@Formalism.L2.Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z)))
      (by
        with_unfolding_all
          exact (@RealDat3.toRealDat b.st.toD7 _ _ _ _ _ _
            (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _
            (alg (a := a) b z.alg) (cpR b z) :)) := by
  with_unfolding_all exact (h :)


set_option maxHeartbeats 2000000 in
theorem std_of_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) (h : z₀.Std) : z.Std := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((y))).symm : _)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact std_cpR b z₀ h

end Std

section StdState

theorem St.std {P : Pre2 K w} (x : St P) : x.m.z.Std :=
  std_of_copy (B := B) (C := w.C) (a := P.Z₀) x.o.Z P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.std

end StdState

end GlobalTheory.Mem.R3.Rw.StateChecks

end
end

