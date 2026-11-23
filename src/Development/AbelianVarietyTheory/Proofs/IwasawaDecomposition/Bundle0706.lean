module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0216

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnParamsInstanceData
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.TwistedScalarIndependence

theorem dep_imp {α : Sort _} {β : α → Sort _} (P : ∀ a, β a → Prop) {a a' : α} {b : β a} {b' : β a'} (h : a' = a) (hb : HEq b' b)
    (H : P a b) : P a' b' := by
  subst h
  cases hb
  exact H

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}

section Field

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
  (lam : type_of% R.lam3) (err : type_of% R.err0)

abbrev newR : RealDat3 D A3 Ks := (R.updS R.kap lam).withErr err

variable {R F} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp₀ Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc₀ Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {Y' : Read (A3 := A3) (newR R lam err).toRealDat (reFace F Dc Sp Zsc).lv2 X0}


set_option maxHeartbeats 4000000 in
def newC (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) X0 Y) (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA) :
    ReadC (newR R lam err) (reFace F Dc Sp Zsc) X0 Y' where
  wU := (by with_unfolding_all exact (C₀.wU :))
  bij := (by with_unfolding_all exact (C₀.bij :))
  eNu := (by with_unfolding_all exact (C₀.eNu :))
  NuC := (by with_unfolding_all exact (C₀.NuC :))
  nu := (by with_unfolding_all exact (C₀.nu :))
  pt := by
    have h := dep_imp (β := fun tup : T → D.what₂.Tup =>
        ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tup t))
      (fun tup jA => ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc (zsOf R F)).a (C₀.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 (zsOf R F)).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc (zsOf R F)).Pt (C₀.wU u) t x f) =
          D.what₂.perCol u (tup t) (D.jN u (C₀.eNu u x)) (jA t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)))
      (b := Y.jA) (b' := (by with_unfolding_all exact (Y'.jA :))) ht ((by with_unfolding_all exact (hj :))) ((by with_unfolding_all exact (C₀.pt :)))
    with_unfolding_all exact (h :)


set_option maxHeartbeats 4000000 in
theorem rationalFormsComparison_baseLevel_indep_scalars {a0 : AmbForm D X0.s} (h : ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 Y.tup Y.jA0 J) (ht : Y'.tup = Y.tup)
    (hj : HEq Y'.jA0 Y.jA0) :
    ∃ J, AmbTie D A3.A X0.s a0 (reFace F Dc Sp Zsc).P0 (reFace F Dc Sp Zsc).ψ0 Y'.tup Y'.jA0 J := by
  have h' := dep_imp (β := fun tup : T → D.what₂.Tup =>
      ∀ t, (Fin (rDim D A3.A F.P0 F.ψ0 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] X0.s.Amb (tup t))
    (fun tup jA => ∃ J, AmbTie D A3.A X0.s a0 F.P0 F.ψ0 tup jA J) (b := Y.jA0) (b' := (by with_unfolding_all exact (Y'.jA0 :))) ht ((by with_unfolding_all exact (hj :))) h
  exact (by with_unfolding_all exact (h' :))


set_option maxHeartbeats 4000000 in
theorem mj_new {Z : ReadL R F X0 Y} {Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) X0 Y'} {Xd : DivX D} (h : MjAre Z Xd)
    (hj : HEq Z'.jW Z.jW) : MjAre Z' Xd := by
  obtain ⟨J, hJ⟩ := h
  have e : Z'.jW = (by with_unfolding_all exact (Z.jW :)) := eq_of_heq ((by with_unfolding_all exact (hj :)))
  refine ⟨⟨(by with_unfolding_all exact (J.eW :))⟩, ?_, (by with_unfolding_all exact (hJ.hlat :))⟩
  rewrite [e]
  exact (by with_unfolding_all exact (hJ.j_eq :))

end Field


set_option maxHeartbeats 4000000 in
def newGeo {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} (lam : type_of% R.lam3)
    (err : type_of% R.err0) (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) :
    GlobalTheory.RealGeo.GeoHalf C (GlobalTheory.RealGeo.Upd.upE C R.toRealDat R.kap R.lam err) fun _ => 1 :=
  ⟨g.κ, g.v₀, GlobalTheory.RealGeo.Upd.updFWT C R.toRealDat R.kap R.lam err g.fw, g.bar,
    fun i => GlobalTheory.RealGeo.Upd.updO C R.toRealDat R.kap R.lam err (g.O i),
    fun i => GlobalTheory.RealGeo.Upd.omPins_upE R.kap R.lam err g.O i (g.pins i), g.rhoGeo, g.equivAll, g.cTie, g.phase⟩


set_option maxHeartbeats 4000000 in
theorem inGeo_new {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} (lam : type_of% R.lam3)
    (err : type_of% R.err0) {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} (h : GlobalTheory.RealGeo.InGeo g) :
    GlobalTheory.RealGeo.InGeo (newGeo lam err g) :=
  ⟨h.jEvExists, h.jEvBar, h.evInj, h.jUnif, h.geoAct, h.latFull, h.dimMatch⟩

section Tw

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL]
  {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (lam : type_of% R.lam3) (err : type_of% R.err0)
  {Y : Read (A3 := A3) R.toRealDat F.lv2 ex.p0} {Z : ReadL R F ex.p0 Y}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)} {Sp₀ Sp : ∀ Zs, SPer (Dc Zs)}
  {Zsc₀ Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}
  {Y' : Read (A3 := A3) (newR R lam err).toRealDat (reFace F Dc Sp Zsc).lv2 ex.p0}


set_option maxHeartbeats 4000000 in
def newTw (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) ex.p0 Y')
    (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) ex.p0 Y) (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (Sp (zsOf R F)).HH)
    (hP : Pins (newR R lam err) (reFace F Dc Sp Zsc) cG) (hH : Holds (newR R lam err) (reFace F Dc Sp Zsc))
    (hE : ErrEq (newR R lam err) (reFace F Dc Sp Zsc))
    (hG : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG))
    (hA : ∃ J, AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 J) (hM : MjAre Z Yd)
    (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA) (hj0 : HEq Y'.jA0 Y.jA0) (hW : HEq Z'.jW Z.jW) : TwIn ex where
  G := G
  Pl0 := Pl0
  I0 := I0
  T := T
  A3 := A3
  core := C
  R := newR R lam err
  F := reFace F Dc Sp Zsc
  cG := cG
  geo := (by with_unfolding_all exact ((newGeo lam err g) :))
  pins := hP
  err := hE
  Y := Y'
  Z := Z'
  C := newC lam err C₀ ht hj
  sEE := (by with_unfolding_all exact (sEE :))
  div := (GlobalTheory.T.divisionCompatible_at_readIdentifications hC D G Pl0 I0 T A3 C.Q.c.F (newR R lam err) (reFace F Dc Sp Zsc) cG ex.p0 Y' Z' (newC lam err C₀ ht hj)
    (by with_unfolding_all exact (sEE :)) Yd (mj_new lam err hM hW).choose hP hH (fun _ _ => (by with_unfolding_all exact (hG :)))).1
  JA := (rationalFormsComparison_baseLevel_indep_scalars lam err hA ht hj0).choose
  amb0 := (rationalFormsComparison_baseLevel_indep_scalars lam err hA ht hj0).choose_spec
  JM := (mj_new lam err hM hW).choose
  mjH := (mj_new lam err hM hW).choose_spec

-- Check the dependent column projections before specializing the ambient data to a row.
set_option maxHeartbeats 4000000 in
private theorem newTw_preserves_columns
    (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧
      GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧
      GlobalTheory.Published.CuspRapidDecay)
    (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)
    (Z' : ReadL (newR R lam err) (reFace F Dc Sp Zsc) ex.p0 Y')
    (C₀ : ReadC R (reFace F Dc Sp₀ Zsc₀) ex.p0 Y)
    (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (Sp (zsOf R F)).HH)
    (hP : Pins (newR R lam err) (reFace F Dc Sp Zsc) cG)
    (hH : Holds (newR R lam err) (reFace F Dc Sp Zsc))
    (hE : ErrEq (newR R lam err) (reFace F Dc Sp Zsc))
    (hG : GrpTie D A3.A F.P0 F.ψ0 F.P1 F.ψ1 (R.eG.trans cG))
    (hA : ∃ J, AmbTie D A3.A ex.p0.s ex.amb0 F.P0 F.ψ0 Y.tup Y.jA0 J)
    (hM : MjAre Z Yd) (ht : Y'.tup = Y.tup) (hj : HEq Y'.jA Y.jA)
    (hj0 : HEq Y'.jA0 Y.jA0) (hW : HEq Z'.jW Z.jW) (hg : GlobalTheory.RealGeo.InGeo g) :
    let x := newTw (R := R) (F := F) (cG := cG) (Y := Y) (Z := Z) (Dc := Dc)
      (Sp₀ := Sp₀) (Sp := Sp) (Zsc₀ := Zsc₀) (Zsc := Zsc) (Y' := Y')
      lam err hC g Z' C₀ sEE hP hH hE hG hA hM ht hj hj0 hW
    HEq x.sEE sEE ∧ HEq x.C.wU C₀.wU ∧ HEq x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo x.geo := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · with_unfolding_all exact (HEq.refl sEE :)
  · with_unfolding_all exact (HEq.refl C₀.wU :)
  · with_unfolding_all exact (HEq.refl C₀.eNu :)
  · with_unfolding_all exact (inGeo_new lam err hg :)

end Tw

end GlobalTheory.Mem.R3.TwistedScalarIndependence

namespace GlobalTheory.Mem.R3

open TwistedScalarIndependence


set_option maxHeartbeats 8000000 in
theorem twArgs_exists : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0), AmbAre t.r.Z ex.amb ex.amb0 → MjAre t.r.Z Yd → GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG) → (∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v) → ∀ Dc Sp₀ Zsc₀ (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((t.r.Y))) (Sp : ∀ Zs, SPer (Dc Zs)) Zsc (sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] (Sp (zsOf t.r.z.R t.r.z.F)).HH), ∃ a : TwArgs ex t, a.Dc = Dc ∧ HEq a.Sp Sp ∧ a.Zsc = Zsc ∧ HEq a.x.sEE sEE ∧ HEq a.x.C.wU C₀.wU ∧ HEq a.x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo a.x.geo := by
  intro hC K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t hA hM hG hp Dc Sp₀ Zsc₀ C₀ Sp Zsc sEE
  obtain ⟨kap, lam, err, hP, hH, hE, rfl, hl, Y', Z', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ :=
    GlobalTheory.T.reFace_zero_part_conventions_chosen_again (w.st Z).toD7 _ _ _ _ (famT t) _ t.r.z.R t.r.z.F t.r.z.cG ex.p0 t.r.Y t.r.Z Dc Sp Zsc t.r.z.pins t.r.intersectionNumber_baseChange hp
  let x : TwIn ex := newTw (R := t.r.z.R) (F := t.r.z.F) (cG := t.r.z.cG) (Y := t.r.Y) (Z := t.r.Z) (Dc := Dc) (Sp₀ := Sp₀) (Sp := Sp)
    (Zsc₀ := Zsc₀) (Zsc := Zsc) (Y' := Y') lam err hC t.r.z.geo Z' C₀ sEE hP hH hE hG hA.2 hM h1 h3 h4 h13
  let a : TwArgs ex t :=
    { Dc := Dc, Sp := Sp, Zsc := Zsc, lam := lam, err := err, lam_eq := hl, x := x
      pack := rfl
      intersectionNumber_baseChange := (by with_unfolding_all exact (hH :))
      κ := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.κ) :))
      v₀ := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.v₀) :))
      fw := (by with_unfolding_all exact ((HEq.refl t.r.z.geo.fw.e) :))
      tup := (by with_unfolding_all exact ((heq_of_eq h1) :))
      tupT := (by with_unfolding_all exact ((heq_of_eq h2) :))
      jA := (by with_unfolding_all exact (h3 :))
      jA0 := (by with_unfolding_all exact (h4 :))
      eMt := (by with_unfolding_all exact (h5 :))
      PY := (by with_unfolding_all exact (h6 :))
      PW := (by with_unfolding_all exact (h9 :))
      eFT := (by with_unfolding_all exact (h7 :))
      IL := (by with_unfolding_all exact (h8 :))
      eE := (by with_unfolding_all exact (h10 :))
      eW := (by with_unfolding_all exact (h11 :))
      jW := (by with_unfolding_all exact (h13 :))
      eRR := (by with_unfolding_all exact (h12 :)) }
  have hCols := newTw_preserves_columns (R := t.r.z.R) (F := t.r.z.F) (cG := t.r.z.cG)
    (Y := t.r.Y) (Z := t.r.Z) (Dc := Dc) (Sp₀ := Sp₀) (Sp := Sp) (Zsc₀ := Zsc₀)
    (Zsc := Zsc) (Y' := Y') lam err hC t.r.z.geo Z' C₀ sEE hP hH hE hG hA.2 hM h1 h3 h4 h13 t.inGeo
  refine ⟨a, rfl, HEq.rfl, rfl, ?_⟩
  change HEq x.sEE sEE ∧ HEq x.C.wU C₀.wU ∧ HEq x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo x.geo
  exact hCols

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComparisonDataStepsNonReferenceTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_data_steps_non_reference_tuple : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  first | exact @GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne | exact GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne | (intros; apply GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseCoefficientSpacesIsometricMaps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mem.RsCoef

theorem glue {α β : Type} {a : α} {b c : β} (h2 : c = b) (h1 : HEq a b) : HEq a c := h2 ▸ h1

theorem coef_of_iso {D : D7} (V : HSp D) (c : CoefA V) {n : ℕ} (h : n = V.rank) (j : ℕ) (lam : D.what₂.Tau → DomWeight n)
    (hlam : ∀ τ a, (lam τ).w a = (Bridge.lamLdef (D := D) V.rank j τ).w (Fin.cast h a))
    (e : VV ℂ lam ≃ₗ[ℂ] c.W) (hinn : ∀ x y, inner ℂ (e x) (e y) = pairK lam (fun _ => 1) x y)
    (hie : ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g →
      ∀ x, e (rhoK lam (invTrK fun τ => Formalism.UG.bc (tauE D τ) g) x) = c.coef.ρ γ (e x))
    (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hJ : J = 1) :
    ∃ c0 : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ) →ₛₗ[D.what₂.embLL] c.W,
      Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) _) ∧
      (∀ x y, inner ℂ (c0 x) (c0 y) = D.what₂.embLL (pairVr (labLL D) _ J x y)) ∧
      ∀ (v' : VV D.what₂.LL (fun τ => Bridge.lamLdef (D := D) V.rank j τ)) (x : VV ℂ lam),
        HEq (MvPolynomial.map D.what₂.embLL v'.1) x.1 → c0 v' = e x := by
  subst h
  have hl : lam = fun τ => Bridge.lamLdef (D := D) V.rank j τ := by
    funext τ
    have h1 := hlam τ
    rcases hw : lam τ with ⟨w1, hw1⟩
    rcases hw' : Bridge.lamLdef (D := D) V.rank j τ with ⟨w2, hw2⟩
    rw [hw, hw'] at h1
    have : w1 = w2 := funext fun a => by simpa using h1 a
    subst this
    rfl
  subst hl
  refine ⟨e.toLinearMap.comp (GlobalTheory.CoefSpace.bcVV D.what₂.embLL _), ⟨fun γ γE hr v => ?_, ?_, ?_⟩, fun x y => ?_,
    fun v' x hx => ?_⟩
  · show e (GlobalTheory.CoefSpace.bcVV _ _ (rhoVr (labLL D) _ γE v)) = c.coef.ρ γ (e (GlobalTheory.CoefSpace.bcVV _ _ v))
    rw [GlobalTheory.Mem.CoefIso.bcVV_rhoVr]
    have ht : (fun τ => Formalism.UG.bc (D.what₂.embLL.comp (labLL D τ)) γE) = fun τ => Formalism.UG.bc (tauE D τ) γE :=
      funext fun τ => by rw [show D.what₂.embLL.comp (labLL D τ) = tauE D τ from GlobalTheory.ThetaFiresProbe.labE_fixed τ]
    rw [ht]
    exact hie γ γE γE hr ⟨rfl, fun a b a' b' ha hb => by rw [Fin.ext ha, Fin.ext hb]⟩ _
  · exact (GlobalTheory.CoefSpace.bcVV_indep D.what₂.embLL _).map' e.toLinearMap (LinearEquiv.ker e)
  · have hs := congrArg (Submodule.map e.toLinearMap)
      (GlobalTheory.CoefSpace.bcVV_span D.what₂.embLL (fun τ => Bridge.lamLdef (D := D) V.rank j τ))
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at hs
    exact hs
  · subst hJ
    show inner ℂ (e _) (e _) = _
    rw [hinn, pairVr, ← GlobalTheory.CoefModel.pairK_mapVV D.what₂.embLL _ D.starLL_cx]
    have h1 : (fun τ => (gramKd (labLL D) (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) τ).map D.what₂.embLL) =
        fun _ => (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
      funext τ
      simp [gramKd]
    rw [h1]
    rfl
  · show e (GlobalTheory.CoefSpace.bcVV _ _ v') = e x
    congr 1
    exact Subtype.ext (eq_of_heq hx)

theorem cast_one {A : Type} [CommRing A] {a b : ℕ} (h : a = b) (y : GL (Fin a) A) :
    LiftBrg.castGL h (y * 1) = (1 : GL (Fin b) A)⁻¹ * LiftBrg.castGL h y * 1 * 1 := by
  simp only [mul_one, inv_one, one_mul]

theorem scale_eq_one {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {s : ℝ} (hs : 0 < s) {x : W} (h0 : (s : ℂ) • x ≠ 0)
    (h : inner ℂ ((s : ℂ) • x) ((s : ℂ) • x) = inner ℂ x x) : s = 1 := by
  have hx : x ≠ 0 := fun e => h0 (by rw [e, smul_zero])
  have hne : inner ℂ x x ≠ 0 := fun e => hx (inner_self_eq_zero.1 e)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc] at h
  have h2 : ((s : ℂ) * s) = 1 := (mul_eq_right₀ hne).1 h
  have h3 : s * s = 1 := by exact_mod_cast h2
  nlinarith

theorem pair_bc {K E ι : Type} [Field K] [NumberField K] [StarRing K] [Field E] [NumberField E] [StarRing E] [Fintype ι] {n : ℕ} (σ : K →+* ℂ)
    (hσ : ∀ x, σ (star x) = star (σ x)) (emb : ι → (E →+* K)) (lam : ι → DomWeight n) (x y : VV K lam) :
    σ (pairVr emb lam 1 x y) = pairK lam (fun _ => 1) (GlobalTheory.CoefSpace.bcVV σ lam x) (GlobalTheory.CoefSpace.bcVV σ lam y) := by
  rw [pairVr, ← GlobalTheory.CoefModel.pairK_mapVV σ _ hσ]
  have h1 : (fun τ => (gramKd emb (1 : Matrix (Fin n) (Fin n) E) τ).map σ) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    simp [gramKd]
  rw [h1]
  rfl

theorem read_iso {K : Type} [Field K] [NumberField K] [StarRing K] (S : Formalism.L2.Col.GSD K) (ok : S.Ok) {G Γ W : Type} [Group G] [Group Γ]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Γ →* G} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι (S.toCSD ok) σ ρ J χ) (c : S.V →ₛₗ[σ] W) (d : G → S.D) (u : S.V → W) {s : ℝ} (hs : 0 < s)
    (hc : ∀ v, c v = (s : ℂ) • u v) (hu : ∀ v, inner ℂ (u v) (u v) = σ (S.pair v v))
    (hr : ∀ (φ : S.EqFun) (h : G), P.extL (S.res ok φ) h = c (φ.1 (d h))) (φ : S.EqFun) (h : G) :
    P.extL (S.res ok φ) h = u (φ.1 (d h)) := by
  by_cases hφ : φ = 0
  · have h0 : c (φ.1 (d h)) = 0 := by rw [hφ]; exact map_zero c
    have h1 := hc (φ.1 (d h))
    rw [h0] at h1
    rw [hr, h0]
    exact ((smul_eq_zero.1 h1.symm).resolve_left (by exact_mod_cast hs.ne')).symm
  · obtain ⟨v, hv0, hv⟩ := GlobalTheory.Mem.GsdIso.exists_isom_vec S ok ι σ ρ J χ P c d hr ⟨φ, hφ⟩
    rw [hc] at hv0 hv
    rw [hr, hc, scale_eq_one hs hv0 (hv.trans (hu v).symm), Complex.ofReal_one, one_smul]


set_option maxHeartbeats 2000000 in
theorem std_iso {X : Stages} {px : PreX X.B.toPre} {I : Col2.ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B} {Wt : Set X.B.places.Pl}
    (z : Dat X I hX T Wt) (hS : z.Std) (i : Fin X.toD7.R.m) (hg : (Vc X.toD7 i).gram = 1) :
    ∃ e : VV ℂ (X.B.wts.lamV ((i : ℕ) + 1)) ≃ₗ[ℂ] (z.R.cV i).W,
      (∀ x y, inner ℂ (e x) (e y) = pairK (X.B.wts.lamV ((i : ℕ) + 1)) (fun _ => 1) x y) ∧
      (∀ (γ : GQ (Vc X.toD7 i)) (γE : GL (Fin (Vc X.toD7 i).rank) X.toD7.host.E)
          (g : GL (Fin X.B.R.nV) X.toD7.host.E), Bridge.IsRatMat (Vc X.toD7 i) γ γE → MatEq γE g →
        ∀ x, e (rhoK (X.B.wts.lamV ((i : ℕ) + 1)) (invTrK fun τ => Formalism.UG.bc (tauE X.toD7 τ) g) x) =
          (z.R.cV i).coef.ρ γ (e x)) ∧
      ∀ (t : TupU I (usedOf I T Wt)) (ok : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)),
        z.R.B.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res ok φ :))) h =
          e (GlobalTheory.CoefSpace.bcVV X.B.embLL (X.B.wts.lamV ((i : ℕ) + 1)) (φ.1 (LiftBrg.ptL X I (usedOf I T Wt) i t 1 1 h))) := by
  have hh := hS.2 i
  unfold BrgStdV StdSide at hh
  refine hh.elim fun c hh => ?_
  have hint := hh.1
  have hread := hh.2.1
  have hli := hh.2.2.1
  refine hh.2.2.2.elim fun hcm hx => ?_
  have hlab : ∀ τ, X.B.embLL.comp (X.B.fields.emb τ) = tauE X.toD7 τ := fun τ =>
    GlobalTheory.ThetaFiresProbe.labE_fixed (D := X.toD7) τ
  refine (GlobalTheory.Mem.CoefIso.coef_iso X.toD7 (Vc X.toD7 i) X.B.R.nV
    (LiftBrg.rkEq X i).symm hg (z.R.cV i)
    (z.pins.char.base.models.cV i) (K := X.B.fields.K) X.B.embLL X.B.fields.emb
    (X.B.wts.lamV ((i : ℕ) + 1)) c (GlobalTheory.TestLat.SumLat.idx_nonempty _)
    (fun γ γE g h1 h2 v => hint γ γE g h1 h2 v) hli).elim fun e he => he.elim fun s he => ?_
  have hβ : z.R.toLevCh.βV i = 1 := z.lev.beta.1 i
  have hrd : ∀ (t : TupU I (usedOf I T Wt)) (ok : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun) (h : Bridge.Gf (Vc X.toD7 i)),
      z.R.B.jL i t ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res ok φ :))) h = c (φ.1 (LiftBrg.ptL X I (usedOf I T Wt) i t 1 1 h)) := by
    intro t ok φ h
    refine (hx h).elim fun x hm => ?_
    refine (hread hcm t ⟨⟨ok⟩, φ⟩ h x hm).trans (congrArg (fun d => c (φ.1 d)) ?_)
    have hm' := hm
    rw [hβ] at hm'
    have hx' := LiftBrg.castGL_of_matEq (LiftBrg.rkEq X i).symm _ _ hm'
    rw [Formalism.L2.Col.decoPt_mk]
    unfold LiftBrg.ptL
    refine congrArg (Formalism.L2.Col.decoOf ∅ _) (hx'.trans ?_)
    exact (by with_unfolding_all exact ((cast_one (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (h : GL (Fin (Vc X.toD7 i).rank) _))) :))
  refine ⟨e, he.2.2.1, fun γ γE g h1 h2 x => ?_, fun t ok φ h => ?_⟩
  · have h5 := he.2.2.2 γ γE g h1 h2 x
    have h3 : (fun τ => Formalism.UG.bc (X.B.embLL.comp (X.B.fields.emb τ)) g) = fun τ => Formalism.UG.bc (tauE X.toD7 τ) g :=
      funext fun τ => congrArg (fun a => Formalism.UG.bc a g) (hlab τ)
    have h4 := (congrArg (fun q => e (rhoK (X.B.wts.lamV ((i : ℕ) + 1)) (invTrK q) x)) h3).symm
    exact (by with_unfolding_all exact ((@Eq.trans _ _ _ ((z.R.cV i).coef.ρ γ (e x)) h4 ((by with_unfolding_all exact (h5 :)))) :))
  · exact (by with_unfolding_all exact ((read_iso (Formalism.L2.Col.mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)) ok (G := Bridge.Gf (Vc X.toD7 i)) (Γ := GQ (Vc X.toD7 i)) (W := (z.R.cV i).W)
      (ι := Bridge.ratF (Vc X.toD7 i)) (σ := X.B.embLL) (ρ := (z.R.cV i).coef.ρ) (J := (LiftBrg.envL X I hX (usedOf I T Wt) z.Xg z.tr z.R.toLevCh z.R.cV i t).lev.J) (χ := (LiftBrg.envL X I hX (usedOf I T Wt) z.Xg z.tr z.R.toLevCh z.R.cV i t).lev.χ) ((by with_unfolding_all exact ((z.R.B.L i t).pres :))) c (fun h => LiftBrg.ptL X I (usedOf I T Wt) i t 1 1 h)
      (fun v => e (GlobalTheory.CoefSpace.bcVV X.B.embLL (X.B.wts.lamV ((i : ℕ) + 1)) v)) he.1 he.2.1
      (fun v => (he.2.2.1 _ _).trans (pair_bc X.B.embLL X.B.starLL_cx X.B.fields.emb _ v v).symm) ((by with_unfolding_all exact ((hrd t ok) :))) φ h) :))


set_option maxHeartbeats 4000000 in
theorem rs_coef : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std → ∃ (cV' : ∀ i', CoefA (Vc (w'.st Z').toD7 i')) (c0L' : ∀ i' : Fin (w'.st Z').toD7.R.m, VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ) →ₛₗ[(w'.st Z').toD7.what₂.embLL] (cV' i').W),
    (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (cV' i').W (z.R.cV i).W ∧ HEq (cV' i').ρ (z.R.cV i).ρ ∧ HEq (cV' i').nW (z.R.cV i).nW ∧ HEq (cV' i').iW (z.R.cV i).iW) ∧ (∀ i', (cV' i').Is) ∧
    (∀ i', Bridge.CoefMapTie (Vc (w'.st Z').toD7 i') (cV' i').coef (c0L' i') (rhoVr (labLL (w'.st Z').toD7) _)) ∧
    (∀ i' x y, inner ℂ (c0L' i' x) (c0L' i' y) = (w'.st Z').toD7.what₂.embLL (pairVr (labLL (w'.st Z').toD7) _
      (if (w'.st Z').toD7.sp.Vneg ((i' : ℕ) + 1) then -(Vc (w'.st Z').toD7 i').gram else (Vc (w'.st Z').toD7 i').gram) x y)) ∧
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ (ok : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).Ok) (φ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).EqFun)
      (h : Bridge.Gf (Vc (w.st Z).toD7 i)) (v' : VV (w'.st Z').toD7.what₂.LL (fun τ => Bridge.lamLdef (Vc (w'.st Z').toD7 i').rank ((i' : ℕ) + 1) τ)),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (φ.1 (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h)).1) →
      HEq (c0L' i' v') (z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((by with_unfolding_all exact ((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((i : ℕ) + 1)).res ok φ :))) h) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS
  choose e he1 he2 he3 using fun i => std_iso z hS i (GlobalTheory.Mem.R3.BrgRead.gram_V (w.st Z) w.ok.spaces i)
  obtain ⟨hPre, -, -, -⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let cp : ∀ i' : Fin (w'.st Z').toD7.R.m, CoefA (Vc (w'.st Z').toD7 i') := fun i' =>
    @CoefA.mk (w'.st Z').toD7 (Vc (w'.st Z').toD7 i') (z.R.cV ((by with_unfolding_all exact (i' :)))).W (z.R.cV ((by with_unfolding_all exact (i' :)))).nW (z.R.cV ((by with_unfolding_all exact (i' :)))).iW (z.R.cV ((by with_unfolding_all exact (i' :)))).fW
      ((by with_unfolding_all exact ((z.R.cV ((by with_unfolding_all exact (i' :)))).ρ :)))
  have hG := fun i' : Fin (w'.st Z').toD7.R.m => coef_of_iso (D := (w'.st Z').toD7) (Vc (w'.st Z').toD7 i')
    (cp i') (n := B.R.nV) ((by with_unfolding_all exact ((LiftBrg.rkEq (w.st Z) ((by with_unfolding_all exact (i' :)))) :))) ((i' : ℕ) + 1)
    ((by with_unfolding_all exact ((B.wts.lamV ((i' : ℕ) + 1)) :))) ((by with_unfolding_all exact ((GlobalTheory.Mem.LiftWt.lamV_eq_lamLdef (w.st Z) ((by with_unfolding_all exact (i' :)))) :)))
    ((by with_unfolding_all exact ((e ((by with_unfolding_all exact (i' :)))) :))) ((by with_unfolding_all exact ((he1 ((by with_unfolding_all exact (i' :)))) :))) ((by with_unfolding_all exact ((he2 ((by with_unfolding_all exact (i' :)))) :)))
    (if (w'.st Z').toD7.sp.Vneg ((i' : ℕ) + 1) then -(Vc (w'.st Z').toD7 i').gram else (Vc (w'.st Z').toD7 i').gram)
    (by
      rw [GlobalTheory.StdFrame.neg_eq_false_of_posDef _ i' ((by with_unfolding_all exact ((B.V_posDef ((i' : ℕ) + 1) (by omega) ((by with_unfolding_all exact (i'.2 :)))) :)))]
      simp only [Bool.false_eq_true, if_false]
      exact GlobalTheory.Mem.R3.BrgRead.gram_V (w'.st Z') w'.ok.spaces i')
  choose c0 hc1 hc2 hc3 using hG
  refine ⟨cp, c0, ?_, fun i' => (by with_unfolding_all exact ((z.pins.char.base.models.cV ((by with_unfolding_all exact (i' :)))) :)), hc1, hc2, ?_⟩
  · rintro i ⟨i', hi'⟩ hi
    dsimp only at hi
    subst hi
    exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  · rintro i ⟨i', hi'⟩ hi
    dsimp only at hi
    subst hi
    intro ok φ h v' hv
    have h1 := hc3 ⟨i, hi'⟩ v' ((by with_unfolding_all exact ((GlobalTheory.CoefSpace.bcVV B.embLL (B.wts.lamV ((i : ℕ) + 1))
      (φ.1 (LiftBrg.ptL (w.st Z) w.I (usedOf w.I T Wt) i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) 1 1 h))) :))) ((by with_unfolding_all exact (hv :)))
    have h2 := he3 i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ok φ h
    exact (by with_unfolding_all exact ((glue (a := c0 ⟨i, hi'⟩ v') h2 ((by with_unfolding_all exact ((heq_of_eq h1) :)))) :))

end GlobalTheory.Mem.RsCoef

end
end

