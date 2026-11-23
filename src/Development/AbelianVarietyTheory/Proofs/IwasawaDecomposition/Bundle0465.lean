module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NontrivialReferenceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsDivStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0460
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0025
public import Lean
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLtGrpTrue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem exists_lt_grpTrue (hG : GlobalTheory.Published.GreenCuspidal) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T)
    (hO : K.Over B.toPre) (hX : B.fields.Ok) (G : GJStage B w.C) :
    ∃ Z : w.Lt, Z.G = G ∧ GrpTrue Z.N f ∧ GrpAt (w.st Z) w.I ∧ DV.KapDef (w.D Z) := by
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  obtain ⟨kb, ks, hk⟩ := GlobalTheory.Mem.Df.Model.exists_ka B
  let W' : RowsRest B w.C :=
    { R.W with
      eOp := fun _ => 0
      eOp_idem := fun _ => LinearMap.comp_zero _
      eOp_sa := fun _ => LinearMap.IsSymmetric.zero
      kaBig := kb
      kaSmall := ks }
  obtain ⟨V, -⟩ := GlobalTheory.Mem.DivModel.exists_divStage B w.C W'
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K B w.C W' G.cd hO (GlobalTheory.Mem.Df.cols_pos w.I w.ok w.pins w.l hX)
    (show R.W.Drows ≤ R.W.Dall by rw [R.std.drows, R.std.dall])
  have hMt : ∀ (μ : w.C.Tup) (j : ℕ), W'.eMt μ j = 0 := fun μ j => by
    haveI := R.std.mt μ j
    exact LinearMap.ext fun _ => Subsingleton.elim _ _
  obtain ⟨N, -, -, hN, -⟩ := GlobalTheory.Mem.Top.exists_nStage_grpTrue hG B w.C W' R.std.sha (fun j v _ _ => R.std.eta j v)
    (fun _ => rfl) hMt f
  refine ⟨⟨W', V, S, N, G⟩, rfl, hN, GlobalTheory.Mem.R3.Model.grpAt_of_grpTrue (w.st ⟨W', V, S, N, G⟩) w.I w.ok (by show GrpTrue N w.I.C; rw [w.C_eq]; exact hN),
    hk w.C W' rfl rfl V S N G⟩

end GlobalTheory.Mem.R3.Rw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formsCoordinates_indexOfFamilyTuple_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  first | exact @GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | exact GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf | (intros; apply GlobalTheory.Mem.R3.Rw.mAU_mLU_ixOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HoldsLOfCopy
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.DatCopy

namespace GlobalTheory.Mem.R3.LiftCopy

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Three

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} {R : RealDat3 a.D A Ks} {F : Face3 a.D A}

theorem holdsL_tr (h : HoldsL R F) : letI := alg b iK; HoldsL (real3 b R) (face3 b F) := by
  let := alg b iK
  constructor
  case heckeR => exact (by with_unfolding_all exact (h.heckeR :))
  case heckeL => exact (by with_unfolding_all exact (h.heckeL :))
  case hecke =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 =>
        (∃ hE, Cx.HeckeIntertwiningDefinite A X hE) ∧ ∃ hW, Cx.HeckeIntertwiningLifts A X hW)
        (toCx3_eq b R F)).mp h.hecke :)
  case gUnit => exact (by with_unfolding_all exact (h.gUnit :))
  case gEquiv =>
    with_unfolding_all
      exact ((congrArg (fun u : Parts R =>
        Cx.GEquiv3 A (cxW R F u) (R.gEx F) ∧
          Cx.LiftGroupEquivariance A (cxW R F u) (R.gWx F))
        (parts_eq b R F)).mp h.gEquiv :)
  case block =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => X.zs.InBlock)
        (toCx3_eq b R F)).mp h.block :)
  case liftTest =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTest X)
        (toCx3_eq b R F)).mp h.liftTest :)
  case liftTestB =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTestB X false)
        (toCx3_eq b R F)).mp h.liftTestB :)
  case liftOnto =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 =>
        ∀ hW, Cx.HeckeIntertwiningLifts A X hW → U2.OntoC A X F.P0 F.ψ0 F.P1 F.ψ1 hW)
        (toCx3_eq b R F)).mp h.liftOnto :)
  case unif => exact (by with_unfolding_all exact (h.unif :))
  case mLat =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => X.MLat false)
        (toCx3_eq b R F)).mp h.mLat :)
  case levW =>
    with_unfolding_all
      exact ((congrArg (fun u : Parts R =>
        Cx.LevelTypeOfLifts A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc)
          (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) false F.P0 F.ψ0)
        (parts_eq b R F)).mp h.levW :)
  case thmA =>
    with_unfolding_all
      exact ((congrArg (fun W : type_of% R.Wp3 => ∀ i t,
        Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (W i) fun p => R.lam3 i t p A.A.v0)
        (wp3_apply_eq_sq_mul_sub_sq_mul b R)).mp h.thmA :)
  case sumW =>
    with_unfolding_all
      exact ((congrArg (fun X : Cx.CxData A.fam3.amb3 => X.PartsW false)
        (toCx3_eq b R F)).mp h.sumW :)
  case aux => exact (by with_unfolding_all exact ((realAdelicInertTransport_furtherRows b h.aux) :))
  case ok => exact (by with_unfolding_all exact (h.ok :))
  case sep => exact (by with_unfolding_all exact (h.sep :))

theorem holdsL_back (h : letI := alg b iK; HoldsL (real3 b R) (face3 b F)) : HoldsL R F := by
  have h2 := holdsL_tr (a := b) a (iK := alg b iK) h
  exact (by with_unfolding_all exact ((cast (congrArg (fun R' : RealDat3 a.D A Ks => HoldsL R' F) (twice_eq b R).symm) ((h2))) : _))

end Three

section Dat

variable {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {Tw : Top.TwDat B} {Wt : Set B.places.Pl}
  (s : SameGrp a b) {z : Dat a.st I hX Tw Wt}

theorem holdsL_of_copy (h : HoldsL (DatCopy.copy b s z).R (DatCopy.copy b s z).F) :
    HoldsL z.R z.F :=
  holdsL_back b (iK := z.alg) (by
    with_unfolding_all exact (h :))

end Dat

end GlobalTheory.Mem.R3.LiftCopy

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdxDefsUp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up
variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

abbrev refUp (Z : w.Lt) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) : Refill Z :=
  { Refill.ofDiv Z N h with S := S' }


open Formalism.BasicNotions.DivX (md) in
set_option maxHeartbeats 1000000 in
def divBack {Z : w.Lt} {S' : SStage B w.C Z.W} {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ}
    (X : DivX (w.D (SRe.upL Z S' N h))) : DivX (w.D Z) :=
  { X with md := fun S κ p _ la z => { md X S κ p la z with } }


set_option maxHeartbeats 1000000 in
theorem grpAt_up {Z : w.Lt} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (x : GrpAt (w.st Z) w.I) : GrpAt (w.st (SRe.upL Z S' N h)) w.I :=
  ⟨(by with_unfolding_all exact (x.pl :)), (by with_unfolding_all exact (x.idem :)), (by with_unfolding_all exact (x.cen :))⟩


set_option maxHeartbeats 1000000 in
theorem muIsW_up {Z : w.Lt} {Wt : Set B.places.Pl} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V)
    (h : B.Word → ℝ) (x : V4.MuIsW (w.st Z) f T Wt w.I.xi) : V4.MuIsW (w.st (SRe.upL Z S' N h)) f T Wt w.I.xi := by
  exact
    { inj := by with_unfolding_all exact (x.inj :)
      range := by with_unfolding_all exact (x.range :)
      mu0 := by with_unfolding_all exact (x.mu0 :)
      star := by with_unfolding_all exact (x.star :)
      star' := by with_unfolding_all exact (x.star' :)
      tw := by with_unfolding_all exact (x.tw :)
      on := by with_unfolding_all exact (x.on :)
      off := by with_unfolding_all exact (x.off :)
      sub := by with_unfolding_all exact (x.sub :)
      supp := by with_unfolding_all exact (x.supp :) }


set_option maxHeartbeats 1000000 in
theorem rowInt_up {Z : w.Lt} (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
    (x : GlobalTheory.PerQ.RowInt w.I w.l Z) : GlobalTheory.PerQ.RowInt w.I w.l (SRe.upL Z S' N h) :=
  ⟨(by with_unfolding_all exact (x.ref :)), (by with_unfolding_all exact (x.tw :))⟩


set_option maxHeartbeats 1000000 in
theorem idxDefs_up {Z : w.Lt} {S' : SStage B w.C Z.W} {N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V} {h : B.Word → ℝ}
    (Y : DivX (w.D (SRe.upL Z S' N h))) (hI : IdxDefs (w.D Z) (divBack Y)) : IdxDefs (w.D (SRe.upL Z S' N h)) Y :=
  ⟨(by with_unfolding_all exact (hI.Ij_def :)), (by with_unfolding_all exact (hI.jw_def :))⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftIdentificationsOfLiftsComparisonStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftIdentifications_of_liftsComparison : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → DV.LamDef D → ∀ (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → D.what₂.Mt (y.tup t) ((i : ℕ) + 1)) (t : LfT y F rep (Mt := fun μ j => ⟨D.what₂.Mt μ j⟩) jL ⟨fun j => ⟨D.what₂.Mj j⟩, D.what₂.MjLat, D.what₂.thetaP, D.what₂.isot⟩), ∃ (I : LiftIds (y.L F)) (mj : GlobalTheory.RealGeo.MjTie R F), LiftTie (y.L F) I ∧ (∀ i π, I.prtW i π = y.prtW F i (rep π)) ∧ (∀ i x, (I.jMj i x).1 = t.jMj i x) ∧ (∀ μ h i x, (I.jMt μ h i x).1 = t.jMt μ i x) ∧ ∀ i x, mj.eW i x = t.eW i x := by
  first | exact @GlobalTheory.Mem.R3.Rw.LiftRd.liftTie_of_lfT | exact GlobalTheory.Mem.R3.Rw.LiftRd.liftTie_of_lfT | (intros; apply GlobalTheory.Mem.R3.Rw.LiftRd.liftTie_of_lfT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsCompatibleOtherLaterStagesOfSameChoicesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (Φ : Type) (rep : Φ → _) (Mt : C.Tup → ℕ → Hs) (l : LfD B.O (B.embLL.comp B.OtoLL) C.Tup Φ Mt) jL (t : LfT y F rep (Mt := Mt) jL l) jL', HEq jL' jL → ∃ t' : @LfT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) Φ ((by with_unfolding_all exact (rep :))) Mt jL' l, letI := alg b iK; HEq t'.eW t.eW ∧ HEq t'.jMt t.jMt := by
  first | exact @GlobalTheory.Mem.R3.Rw.lfT_of_same | exact GlobalTheory.Mem.R3.Rw.lfT_of_same | (intros; apply GlobalTheory.Mem.R3.Rw.lfT_of_same <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Bare

open GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl Polynomial

def cenPull {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ H) →ₐ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ G) :=
  ((MonoidAlgebra.domCongr ℂ ℂ e.symm : MonoidAlgebra ℂ H →ₐ[ℂ] MonoidAlgebra ℂ G).comp
    (Subalgebra.center ℂ (MonoidAlgebra ℂ H)).val).codRestrict _ fun z => by
      rw [Subalgebra.mem_center_iff]
      intro b
      obtain ⟨c, rfl⟩ := (MonoidAlgebra.domCongr ℂ ℂ e.symm).surjective b
      change _ * MonoidAlgebra.domCongr ℂ ℂ e.symm z = MonoidAlgebra.domCongr ℂ ℂ e.symm z * _
      rw [← map_mul, ← map_mul, Subalgebra.mem_center_iff.1 z.2 c]

theorem coeff_cenPull {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) (g : G) :
    (cenPull e z : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g) :=
  MonoidAlgebra.coeff_domCongr (R := ℂ) e.symm (z : MonoidAlgebra ℂ H) g

theorem cenPull_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) {z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)}
    {z' : Subalgebra.center ℂ (MonoidAlgebra ℂ G)}
    (h : ∀ g, (z' : MonoidAlgebra ℂ G).coeff g = (z : MonoidAlgebra ℂ H).coeff (e g)) : cenPull e z = z' := by
  apply Subtype.ext
  ext g
  rw [coeff_cenPull, h]

attribute [local instance] GlobalTheory.Mem.Top.factType


set_option synthInstance.maxHeartbeats 400000 in
def reser {R : Ranks} {H : Host R} {what₂ rows' : Rows.Data R} {N : NData R H what₂} {N' : NData R H rows'} {A : NAut N} {A' : NAut N'}
    (T : NTypes A) (T' : NTypes A')
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Mt μ j)) : NTypes A :=
  { T with
    eSer := T'.eSer
    eSer_idem := T'.eSer_idem
    eSer_central := T'.eSer_central
    eSer_orth := T'.eSer_orth
    eSer_zero := T'.eSer_zero
    eSer_sum := T'.eSer_sum
    cenAmb := a
    cenMt := b }

theorem goodElement_mem_center_groupAlgebra {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (T : NTypes A) :
    T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) := by
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  exact (TypesInhab.good_sum (I := Σ k : Fin 2, N.PlG k) (P := fun kv => Fin R.r → ZMod (H.g kv.1))
    (fun kv p => T.eSer kv.1 (Formalism.CyclotomicNorms.monicOf p))
    (fun a => T.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))) T.e0 (fun g => rfl)
    (fun _ _ => T.eSer_idem _ _) (fun _ _ => T.eSer_central _ _)
    (fun _ p q hpq => T.eSer_orth _ _ _ fun h => hpq (funext fun i => by
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt p i, h, Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]))).1

theorem exists_nStage_act {B : Base} {C C₀ : Cols B} {W₀ : RowsRest B C₀} (N₀ : NStage B C₀ W₀) {f : Fr B.toPre}
    (h₀ : GrpTrue N₀ f) (W : RowsRest B C) (hsha : ShaOK B.toPre W.shaLen) (heta : ∀ j w, W.etaJ j w = 0)
    {G : Type} [Group G] (e₀ : G ≃* G0g N₀.nd)
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Mt μ j))
    (ha : ∀ z : Subalgebra.center ℂ (MonoidAlgebra ℂ G),
      (∀ g, (z : MonoidAlgebra ℂ G).coeff g = N₀.ntypes.e0.coeff (e₀ g)) → (∀ μ, W.eOp μ = a μ z) ∧ ∀ μ j, W.eMt μ j = b μ j z) :
    ∃ N : NStage B C W, IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      (∀ μ z, N.ntypes.cenAmb μ z = a μ (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z)) ∧
      ∀ μ j z, N.ntypes.cenMt μ j z = b μ j (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z) := by
  obtain ⟨ldat, hsha⟩ := hsha
  let nd := trueLayer B C W f.W ldat hsha
  have hE : IsEmpty nd.Loc := ⟨fun i : Empty => i.elim⟩
  let A : NAut nd := GaloisStage.nAut nd (fun k v => above f.P (nd.g_split k) v)
    (fun k v => div_over f.P (above_div _ _ v)) (fun k => above_injective f.P (nd.g_split k))
    (fun k v v' => not_isConjPl f.P (nd.g_split k) (above_div _ _ v) (above_div _ _ v'))
  have hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  have hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  choose tg htg using fun (k : Fin 2) (v : nd.PlG k) =>
    GlobalTheory.TameInertiaGen.exists_tameGenAt B.host.E nd.Om (A.plGw k v) (nd.plOm.1 (A.plGw k v)) (nd.plOm.2 _)
  choose s hs using fun k : Fin 2 => SerInhab.exists_isSer B.R.r (B.host.g k) B.toPre.restRowsFiniteGroupCard (B.host.g_prime k)
    B.toPre.restRowsFiniteGroupCard_pos ((dvd_pow_self _ (GaloisStage.f_pos B.R).ne').trans
      (Finset.dvd_prod_of_mem (fun k : Fin 2 => (Nat.card (GL (Fin B.R.r) (ZMod (B.host.g k)))) ^ B.R.f)
        (Finset.mem_univ k)))
  obtain ⟨T₀⟩ : Nonempty (NTypes A) := ⟨TypesInhab.types0 hl hi B.g_cond B.BB_disj tg htg s hs⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨ω, -⟩ := TypesInhab.exists_char (A := MonoidAlgebra ℂ (G0g nd)) 0 one_ne_zero (by simp)
  let eR : G ≃* G0g nd := e₀.trans (grpEquiv N₀.naut A)
  let T : NTypes A := reser (retype T₀ hl hi (fun k => labDat (B.host.g k)) ω) N₀.ntypes
    (fun μ => (a μ).comp (cenPull eR)) (fun μ j => (b μ j).comp (cenPull eR))
  have hT : TypesTrue T f.P f.W :=
    ⟨fun k v => above_div f.P (nd.g_split k) v, fun _ => rfl, fun _ _ _ => rfl, fun k p => h₀.ser k p⟩
  have hco : ∀ g, T.e0.coeff (grpEquiv N₀.naut A g) = N₀.ntypes.e0.coeff g := TypesTrue.typeIdempotent_coeff_across_layers h₀ hT
  have hc : T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g nd)) := goodElement_mem_center_groupAlgebra T
  have hz := ha (cenPull eR ⟨T.e0, hc⟩) fun g => (coeff_cenPull eR _ g).trans (hco (e₀ g))
  have htie : T.IdempotentMatchesAction := by
    refine ⟨fun μ => ?_, fun μ j => ?_⟩
    · rw [NTypes.onAmb, dite_eq_left hc]
      exact hz.1 μ
    · rw [NTypes.onMt, dite_eq_left hc]
      exact hz.2 μ j
  have hy : ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := fun x => by
    obtain ⟨g, rfl⟩ := (grpEquiv N₀.naut A).surjective x
    exact ⟨_, (N₀.nStage_trivialCharacter_coeff_eq g).trans (hco g).symm⟩
  choose e hee using hy
  let tw := GaloisStage.nTw B.LL0 nd
  have hT' : IsEmpty tw.Tw := ⟨fun i : Empty => i.elim⟩
  obtain ⟨Y, hY, ⟨th⟩⟩ := exists_nexp_nth_of_isEmpty B C W nd tw hT' e
  exact ⟨{
    toLocStage := L
    nd := nd
    ntw := tw
    naut := A
    nbc := GaloisStage.nBC A
    nexp := Y
    ntypes := T
    nStage_trivialCharacter_compat := htie
    nStage_trivialCharacter_coeff_eq := fun g => by rw [hY]; exact hee g
    nth := th
    nbr := fun i => hE.elim i
    nbr_ind := fun i => hE.elim i
    self_good := fun i => hE.elim i
    ntwbr := fun i => hT'.elim i
    ntwbr_ind := fun i => hT'.elim i
    loc_tie := fun i => hE.elim i
    bc_tie := fun i => hE.elim i
    rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i
    Z_tie := fun i => hE.elim i
    Zgood_tie := fun i => hE.elim i
    etaJ_tie := fun j w _ _ => (heta j w).trans (Finset.sum_eq_zero fun i _ => hE.elim i).symm },
    hE, hT, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem read_unique {E : Type} [Field E] [NumberField E] {S : Finset (Pl E)} {r p : ℕ} (g : ∀ P : S, GL (Fin r) (kP P.1))
    {S' : Finset (Pl E)} (g' : ∀ P : S', GL (Fin r) (kP P.1))
    (hg : ∀ (P : Pl E) (h : P ∈ S) (h' : P ∈ S'), g' ⟨P, h'⟩ = g ⟨P, h⟩) (P : S) (P' : S') (hP : P.1 = P'.1)
    (i : ZMod p ≃+* kP P.1) (i' : ZMod p ≃+* kP P'.1) {x x' : GL (Fin r) (ZMod p)}
    (h : g P = Formalism.UG.bc (i : ZMod p →+* kP P.1) x) (h' : g' P' = Formalism.UG.bc (i' : ZMod p →+* kP P'.1) x') : x = x' := by
  obtain ⟨P, hS⟩ := P
  obtain ⟨P', hS'⟩ := P'
  dsimp only at hP
  subst hP
  rw [hg P hS hS', h, Subsingleton.elim (i' : ZMod p →+* kP P) (i : ZMod p →+* kP P)] at h'
  ext a b
  exact i.injective (congrArg (fun u : GL (Fin r) (kP P) => (u : Matrix (Fin r) (Fin r) (kP P)) a b) h')

theorem e_eq_act {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] {O : Type} [CommRing O] {φ : O →+* ℂ}
    {σ : K →+* ℂ} {m : Mat1 K G} {s : Sp1 O φ G} (t : Tie1 σ m s) {e : MonoidAlgebra K G} (h : m.Laws σ e)
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (hz : ∀ g, σ (e.coeff g) = (z : MonoidAlgebra ℂ G).coeff g) :
    s.e = s.act z := by
  refine LinearMap.ext_on_range t.forms.span fun i => ?_
  rw [t.forms.op_eq, t.cen z e hz, h.E_eq]

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

theorem exists_bare {K : Ctx} (P : Pre2 K w) :
    ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧
        ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR := by
  letI := P.z.alg
  let e₀ : Gc B w.px ≃* G0g P.Z₀.N.nd := P.z.R.eG.trans P.z.cG
  have hgood : ∀ g, B.embLL ((idemOf P.z.Xg).coeff g) = P.Z₀.N.ntypes.e0.coeff (e₀ g) := P.z.good.2
  obtain ⟨N, hE, hN, hA, hM⟩ := exists_nStage_act P.Z₀.N P.grp (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) P.q.sha
    (fun _ _ => rfl) e₀ (fun μ => (P.q.p.sA true μ).act) (fun μ j => (P.q.p.sL μ j).act) fun z hz =>
      ⟨fun μ => e_eq_act (P.q.t.tA true μ) (P.q.t.lawsA true μ) z fun g => (hgood g).trans (hz g).symm,
       fun μ j => e_eq_act (P.q.p.tL μ j) (P.q.t.lawsL μ j) z fun g => (hgood g).trans (hz g).symm⟩
  have hpl : ∀ k v, P.Z₀.N.naut.plGw k ((plEquiv P.Z₀.N.naut N.naut k).symm v) = N.naut.plGw k v := fun k v => by
    rw [← TypesTrue.plGw_plEquiv P.grp hN, Equiv.apply_symm_apply]
  refine ⟨N, hE, hN, fun V S G => ⟨?_, fun eR hR => ?_⟩⟩
  · obtain ⟨plg, hp⟩ := P.grpAt.pl
    obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent
      (w.st (RowPk.Over.Z (q := P.q) ⟨_, _, V, S, N, G⟩)).toD7
    refine ⟨⟨(Equiv.sigmaCongrRight fun k => (plEquiv P.Z₀.N.naut N.naut k).symm).trans plg, fun kv => ?_⟩, hi, hc⟩
    exact ⟨(hp ⟨kv.1, _⟩).1.trans (hpl kv.1 kv.2), (hp ⟨kv.1, _⟩).2⟩
  · have he : e₀.trans (grpEquiv P.Z₀.N.naut N.naut) = eR := by
      obtain ⟨plg, iso, h1, h2⟩ := hR
      obtain ⟨plg₀, iso₀, k1, -, -, k2⟩ := P.z.pins.keep.grp
      refine MulEquiv.ext fun g => funext fun kv => ?_
      exact (read_unique g (P.z.R.eG g) (P.z.idG g) (plg kv) (plg₀ ⟨kv.1, (plEquiv P.Z₀.N.naut N.naut kv.1).symm kv.2⟩)
        ((h1 kv).trans ((k1 ⟨kv.1, _⟩).trans (hpl kv.1 kv.2)).symm) (iso kv) (iso₀ ⟨kv.1, _⟩) (h2 g kv) (k2 g ⟨kv.1, _⟩)).symm
    subst he
    exact ⟨fun μ z z' hz x => by rw [hA, cenPull_eq _ hz], fun μ j z z' hz x => by rw [hM, cenPull_eq _ hz]⟩

theorem stepW_bare : StepW (pinAnd HasPk) fun K B f T w => ∀ (P : Pre2 K w), ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧ ∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR :=
  StepW.of_all fun _ _ _ _ _ _ _ _ P => exists_bare P

end GlobalTheory.Mem.R3.Rw.Bare

end
end

