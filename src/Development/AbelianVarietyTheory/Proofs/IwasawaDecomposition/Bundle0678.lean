module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

def sgTw (x : St P) (N : TwNew (Dof x)) : SameGrp (B := B) (C := w.C) x.o.Z (oTw x N).Z where
  e _ := Equiv.refl _
  pl _ _ := rfl
  e0 _ := rfl

def datTw (x : St P) (N : TwNew (Dof x)) : Dat (w.st (oTw x N).Z) w.I P.hX T P.Wt :=
  DatCopy.copy (a := x.o.Z) (oTw x N).Z (sgTw x N) x.m.z

def sideTw (x : St P) (N : TwNew (Dof x)) : Side0 (oTw x N) where
  cen := x.s.cen
  tie := x.s.tie
  is := x.s.is
  RR := x.s.RR
  frames := x.s.frames
  jEE := x.s.jEE
  basis := x.s.basis
  norm := x.s.norm

theorem fitsTw (x : St P) (N : TwNew (Dof x)) : (oTw x N).Fits := ⟨x.fits.div, x.fits.grp, ⟨(by with_unfolding_all exact (x.fits.grpAt.pl :)), (by with_unfolding_all exact (x.fits.grpAt.idem :)), (by with_unfolding_all exact (x.fits.grpAt.cen :))⟩,
  fun eR h => ⟨(by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).amb : _)), (by with_unfolding_all exact ((x.fits.cen ((eR)) ((h))).mt : _))⟩⟩

def stTw (x : St P) (N : TwNew (Dof x)) (m : Moved (oTw x N)) (hc : m.Copy) (hh : m.Coh) (r : ReadPk m (sideTw x N))
    (hp : r.Pin) : St P :=
  ⟨oTw x N, fitsTw x N, x.G_eq, x.etaF, x.bk, m, hc, hh, sideTw x N, r, hp⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
section
noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure CopyN (D : D7) {D' : D7} (N : TwNew D') (ι : D.what₂.LL →+* D'.what₂.LL) (e : ↥D'.LL0 ≃+* ↥D.LL0) : Prop where
  cp : GlobalTheory.TwInputs.Move.CopyTw D N.toD7 ι e
  ThetaPsi : HEq D.ntw.ThetaPsi N.tw.ThetaPsi
  topO : HEq D.ntw.topO N.tw.topO
  finLam : HEq D.ntw.finLam N.tw.finLam
  jL : HEq D.ntw.jL N.tw.jL
  s2 : HEq D.ntw.s2 N.tw.s2
  lamG : HEq D.ntw.lamG N.tw.lamG
  Xv : HEq D.ntw.Xv N.tw.Xv
  qs : HEq D.ntw.qs N.tw.qs
  res : HEq D.ntw.res N.tw.res
  eLL0 : ∀ g g', HEq g g' → e (N.ex.eLL0 g') = D.nexp.eLL0 g
  twPsi : HEq D.nexp.twPsi N.ex.twPsi
  twDel : HEq D.nexp.twDel N.ex.twDel
  eH : HEq D.nexp.eH N.ex.eH

theorem CopyN.carried {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0} (h : CopyN D N ι e) :
    Carried D N.toD7 := by
  refine ⟨h.cp.toSameExport, fun i i' hi x x' hx => ?_⟩
  have hx' : x = e x' := Subtype.ext (D.what₂.embLL.injective
    (hx.trans ((congrArg N.toD7.what₂.embLL (h.cp.LL0 x')).symm.trans (h.cp.embLL _))))
  subst hx'
  exact ⟨h.cp.emb0 i i' hi x', h.cp.emb0b i i' hi x'⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricCharacterGridListKeptLocalizedStage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

noncomputable section
namespace GlobalTheory.HeightCounting.Fin3

theorem listPin_datL : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (L : LocAll (lay0 (Dof x))) (cDep : ℝ), ListSt cDep x → ListPin (DL x L) (datL x L).R.toRealDat.toLevCh cDep K.s.b := by
  intro K B f T w P x L cDep h
  obtain ⟨G, hField, hTie⟩ := h
  exact ⟨by
      with_unfolding_all
        exact (GlobalTheory.Mem.GridMove.gdC (a := x.o.Z) (oL x L).Z G :),
    ⟨by with_unfolding_all exact (hField.values :),
      by with_unfolding_all exact (hField.roots :)⟩,
    by with_unfolding_all exact (hTie :)⟩

end GlobalTheory.HeightCounting.Fin3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsSymm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

theorem sameGalois_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂} (h : SameGalois N N') :
    SameGalois N' N := ⟨h.R.symm, h.host.symm, h.loc.symm, h.Om.symm, h.instOm.symm, h.algOm.symm, h.plOm.symm, h.PlG.symm⟩

theorem twistDataAgreeAcrossCoefficients_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'} (h : TwistDataAgreeAcrossCoefficients X X') : TwistDataAgreeAcrossCoefficients X' X :=
  ⟨h.cc.symm, h.Tw.symm, h.l.symm, h.O0.symm, h.crO0.symm, h.algO0.symm, h.topO0.symm, h.O.symm, h.crO.symm, h.algO.symm, h.Ok.symm, h.crOk.symm, h.algOk.symm, h.zk.symm, h.pD.symm, h.chi1.symm, h.Sig.symm, h.finSig.symm, h.jS.symm, h.side.symm, h.rhoS.symm, h.S0.symm, h.hEig.symm, h.abelian₂.symm, h.sideL.symm, h.RCG.symm, h.grpRCG.symm, h.finRCG.symm, h.art.symm, h.th.symm⟩

theorem sameForms_symm {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'} (h : SameForms Y Y') :
    SameForms Y' Y :=
  ⟨h.Fm.symm, h.acgFm.symm, h.modFmK.symm, h.modFmO.symm, h.actG.symm, h.U.symm, h.psiU.symm, h.eAlg.symm, h.Dat.symm, h.th.symm, h.lev.symm, h.thPsi.symm, h.MtV.symm, h.acgMt.symm, h.modMtK.symm, h.modMtO.symm, h.MtLat.symm, h.thP.symm, h.hkF.symm⟩

theorem heq_app {α α' β β' : Type} (hα : α = α') (hβ : β = β') {f : α → β} {f' : α' → β'} (hf : HEq f f') {x : α} {x' : α'}
    (hx : HEq x x') : HEq (f x) (f' x') := by
  subst hα; subst hβ
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hx
  rfl

theorem move_set {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂} (h1 : SameGalois N N')
    (B' : Finset (PlE D'.host)) : ∃ B : Finset (PlE D.host), HEq B B' ∧
      ∀ (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)), HEq Q Q' → Disjoint Q B → Disjoint Q' B' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2
  exact ⟨B', HEq.rfl, fun Q Q' hQ h => by obtain rfl := eq_of_heq hQ; exact h⟩


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem move_pack {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'} (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X')
    {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') {Q : Finset (PlE D.host)} {k : ℕ} (ψ : X.RCG i Q →* (X.Ok i k)ˣ) :
    ∃ (Q' : Finset (PlE D'.host)) (ψ' : X'.RCG i' Q' →* (X'.Ok i' k)ˣ), HEq Q Q' ∧ ∀ a : ℤ, HEq (ψ ^ a) (ψ' ^ a) := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  subst hi
  exact ⟨Q, ψ, HEq.rfl, fun _ => HEq.rfl⟩


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem move_xd {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : SameGalois N N') (h2 : TwistDataAgreeAcrossCoefficients X X') (h3 : SameForms Y Y') (m : ℕ)
    (x0 : ∀ i j b, Set (Y.Dat i j b))
    (hP : ∀ i j b, ∀ a ∈ x0 i j b, ∀ u : Y.U, Y.actG i j b u (Y.th i j b a) =
      ((Y.psiU i b u : (FractionRing (X.O i))ˣ) : FractionRing (X.O i)) • Y.th i j b a)
    (N0 : X.Tw → ℕ) (S : ∀ i j b, Finset (Y.Dat i j b)) :
    ∃ x0' : ∀ i j b, Set (Y'.Dat i j b), (∀ i j b, ∀ a ∈ x0' i j b, ∀ u : Y'.U, Y'.actG i j b u (Y'.th i j b a) =
      ((Y'.psiU i b u : (FractionRing (X'.O i))ˣ) : FractionRing (X'.O i)) • Y'.th i j b a) ∧ HEq x0 x0' ∧
      ((∀ i j b, 1 ≤ j → j ≤ m → x0 i j b = Set.univ) → ∀ i j b, 1 ≤ j → j ≤ m → x0' i j b = Set.univ) ∧
      (∃ N0' : X'.Tw → ℕ, HEq N0 N0') ∧ ∃ S' : ∀ i j b, Finset (Y'.Dat i j b), HEq S S' := by
  obtain ⟨a1, a2, a3, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  obtain ⟨xcc, xTw, xl, fixedFieldTransport_baseIntegerRing_heq, fixedFieldTransport_baseIntegerCommRing_heq, fixedFieldTransport_baseIntegerAlgebra_heq, fixedFieldTransport_baseIntegerTopology_heq, xO, xcrO, xalgO, xOk, xcrOk, xalgOk, xzk, xpD, xchi1, xSig, xfinSig, xjS, xside, xrhoS, fixedFieldTransport_initialPlaceSet_heq, xhEig, xLam, xsideL, xRCG, xgrpRCG, xfinRCG, xart, xth⟩ := h2
  obtain ⟨yFm, yacgFm, ymodFmK, ymodFmO, yactG, yU, ypsiU, yeAlg, yDat, yth, ylev, ythPsi, yMtV, yacgMt, ymodMtK, ymodMtO, yMtLat, ythP, yhkF⟩ := h3
  cases D; cases D'
  dsimp only at a1 a2 a3
  subst a1; subst a2; subst a3
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xcc xTw xl fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq fixedFieldTransport_baseIntegerAlgebra_heq fixedFieldTransport_baseIntegerTopology_heq xO xcrO xalgO xOk xcrOk xalgOk xzk xpD xchi1 xSig xfinSig xjS xside xrhoS fixedFieldTransport_initialPlaceSet_heq xhEig xLam xsideL xRCG xgrpRCG xfinRCG xart xth
  subst xcc; subst xTw; subst xl; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst fixedFieldTransport_baseIntegerAlgebra_heq; subst fixedFieldTransport_baseIntegerTopology_heq; subst xO; subst xcrO; subst xalgO; subst xOk; subst xcrOk; subst xalgOk; subst xzk; subst xpD; subst xchi1; subst xSig; subst xfinSig; subst xjS; subst xside; subst xrhoS; subst fixedFieldTransport_initialPlaceSet_heq; subst xhEig; subst xLam; subst xsideL; subst xRCG; subst xgrpRCG; subst xfinRCG; subst xart; subst xth
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yU ypsiU yeAlg yDat yth ylev ythPsi yMtV yacgMt ymodMtK ymodMtO yMtLat ythP yhkF
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yU; subst ypsiU; subst yeAlg; subst yDat; subst yth; subst ylev; subst ythPsi; subst yMtV; subst yacgMt; subst ymodMtK; subst ymodMtO; subst yMtLat; subst ythP; subst yhkF
  exact ⟨x0, hP, HEq.rfl, id, ⟨N0, HEq.rfl⟩, S, HEq.rfl⟩

end GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

namespace GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

theorem exists_disjoint_choice {α ι : Type} [DecidableEq α] {Z : ι → Type} (c : ∀ i, Z i → Finset α) (P : ∀ i, Z i → Prop)
    (h : ∀ i (B : Finset α), ∃ z, P i z ∧ Disjoint (c i z) B) (T : Finset ι) :
    ∃ f : ∀ i, Z i, (∀ i, P i (f i)) ∧ ∀ i ∈ T, ∀ i' ∈ T, i ≠ i' → Disjoint (c i (f i)) (c i' (f i')) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    choose f hf using fun i => h i ∅
    exact ⟨f, fun i => (hf i).1, by simp⟩
  | insert a T ha ih =>
    obtain ⟨f, hf, hf'⟩ := ih
    obtain ⟨z, hz, hz'⟩ := h a (T.biUnion fun i => c i (f i))
    have key : ∀ i ∈ T, Disjoint (c a (Function.update f a z a)) (c i (Function.update f a z i)) := fun i hi => by
      rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact ha hi)]
      exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem (fun i => c i (f i)) hi) hz'
    refine ⟨Function.update f a z, fun i => ?_, fun i hi i' hi' hne => ?_⟩
    · by_cases hi : i = a
      · subst hi; rwa [Function.update_self]
      · rw [Function.update_of_ne hi]; exact hf i
    · rcases Finset.mem_insert.1 hi with h1 | h1 <;> rcases Finset.mem_insert.1 hi' with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · subst h1; exact key i' h2
      · subst h2; exact (key i h1).symm
      · rw [Function.update_of_ne (by rintro rfl; exact ha h1), Function.update_of_ne (by rintro rfl; exact ha h2)]
        exact hf' i h1 i' h2 hne

theorem epsilon_congr {β : Type} {p q : β → Prop} (h1 h2 : Nonempty β) (h : p = q) :
    @Classical.epsilon _ h1 p = @Classical.epsilon _ h2 q := by
  subst h; rfl

end GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations

namespace GlobalTheory.HeightCounting.Up


open GlobalTheory.HeightCounting.Up.SymmetryOfAgreementRelations in
set_option maxHeartbeats 4000000 in
theorem nonempty_seed_of_kept : ∀ (D₁ D₀ : D7) (C₁ : NChoice D₁) (C₀ : NChoice D₀) (xd : ThData D₀), Kept C₁ C₀ → D₁.what₂.places.Pl = D₀.what₂.places.Pl → (∀ v v₀, HEq v v₀ → TwistedAt D₁ v → TwistedAt D₀ v₀) → NChTie D₁ C₁ → (∀ v, C₁.twI (D₁.what₂.places.conj v) = C₁.twI v) → {v | TwistedAt D₁ v}.Finite → IsGalois ℚ ↥D₁.LL0 → (∀ v, TwistedAt D₀ v → D₀.ntw.NonzeroIndexPlace (C₀.twI v)) → ExportAt D₀ C₀ xd → XdAll xd → ∀ A, Nonempty (Seed D₁ A) := by
  intro D₁ D₀ C₁ C₀ xd hK hPl htw hT hc hfin hG hW hE hX A
  classical
  have g1 := sameGalois_symm hK.gal
  have g2 := twistDataAgreeAcrossCoefficients_symm hK.set
  have g3 := sameForms_symm hK.forms
  obtain ⟨N0, S, hp, hs⟩ := hE
  obtain ⟨x1, hx1P, hxd, hxall, ⟨N1, hN⟩, S1, hS⟩ := move_xd g1 g2 g3 D₀.R.m xd.xd0 xd.thetaBase_invariant_action N0 S
  let xd₁ : ThData D₁ := ⟨x1, hx1P⟩
  have hm : D₁.R.m = D₀.R.m := by rw [hK.gal.R]
  have hall : XdAll xd₁ := fun i j b h1 h2 => hxall hX i j b h1 (hm ▸ h2)
  have hTw : D₀.ntw.Tw = D₁.ntw.Tw := eq_of_heq g2.Tw
  obtain ⟨-, -, -, -, hb⟩ := same_basic g1 g2 g3
  have key : ∀ r, TwistedAt D₁ r → TwIn.Ok (⟨twEOf xd₁, N1, S1⟩ : TwIn D₁) (C₁.twI r) ∧
      ∀ B : Finset (PlE D₁.host), ∃ (Q : Finset (PlE D₁.host)) (k : ℕ)
        (ψ : D₁.ntw.RCG (C₁.twI r) Q →* (D₁.ntw.Ok (C₁.twI r) k)ˣ), ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l (C₁.twI r)) →
          IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 (C₁.twI r) (twEps D₁ (C₁.twI r)) (S1 (C₁.twI r)) B Q k (ψ ^ a) := by
    intro r hr
    have hr₀ : TwistedAt D₀ (cast hPl r) := htw r (cast hPl r) (cast_heq hPl r).symm hr
    have hii : HEq (C₀.twI (cast hPl r)) (C₁.twI r) := heq_app hPl.symm hTw hK.twI.symm (cast_heq hPl r)
    obtain ⟨hl, hSS, -⟩ := hb _ _ hii
    obtain ⟨hSet, hOk⟩ := hs _ hr₀
    refine ⟨?_, fun B => ?_⟩
    · have h9 := fun j (hj : j ∈ Finset.Icc 1 D₁.R.m) b => fullRk_basisOf_transfer g1 g2 g3 (E := twEOf xd) (E' := twEOf xd₁)
        hxd hii j b ((hSS S S1 hS).2 j b) ⟨hOk.1 j (hm ▸ hj) b, hOk.2 j (hm ▸ hj) b⟩
      exact ⟨fun j hj b => (h9 j hj b).1, fun j hj b => (h9 j hj b).2⟩
    · obtain ⟨B₀, hB, -⟩ := move_set g1 B
      obtain ⟨Q₀, k, ψ₀, hG0⟩ := hp _ (hW _ hr₀) hSet _ (twEps_pos _ _) hOk.1 (S (C₀.twI (cast hPl r))) hOk.2 B₀
      obtain ⟨Q₁, ψ₁, hQ, hψ⟩ := move_pack g1 g2 hii ψ₀
      refine ⟨Q₁, k, ψ₁, fun a ha => ?_⟩
      have he : twEps D₁ (C₁.twI r) = twEps D₀ (C₀.twI (cast hPl r)) := by rw [twEps, twEps, hl]
      have ha' : IsCoprime a (D₀.ntw.l (C₀.twI (cast hPl r)) : ℤ) :=
        Int.isCoprime_iff_gcd_eq_one.2 (by rw [hl]; simpa [Int.gcd] using ha)
      rw [he]
      exact goodTw_transfer g1 g2 g3 (B := BlochKatoReduction.bk0 D₀) (B' := BlochKatoReduction.bk0 D₁) hK.br.symm rfl rfl hxd hN hii _
        (hSS S S1 hS).1 hB hQ k (hψ a) (hG0 a ha')
  let rep : D₁.what₂.places.Pl → D₁.what₂.places.Pl := fun v =>
    @Classical.epsilon _ ⟨v⟩ fun r => TwistedAt D₁ r ∧ OverOnePair D₁ v r
  have hrep : ∀ v, TwistedAt D₁ v → TwistedAt D₁ (rep v) ∧ OverOnePair D₁ v (rep v) := fun v hv =>
    Classical.epsilon_spec (p := fun r => TwistedAt D₁ r ∧ OverOnePair D₁ v r) ⟨v, hv, overOnePair_refl v⟩
  have hrep_eq : ∀ v v', OverOnePair D₁ v v' → rep v' = rep v := fun v v' h =>
    epsilon_congr _ _ (funext fun r => propext ⟨fun ⟨h1, h2⟩ => ⟨h1, h.trans hG h2⟩,
      fun ⟨h1, h2⟩ => ⟨h1, (h.symm hG).trans hG h2⟩⟩)
  let s : D₁.what₂.places.Pl → D₁.ntw.Tw := fun v => if TwistedAt D₁ v then C₁.twI (rep v) else C₁.twI v
  have hs_tw : ∀ v, TwistedAt D₁ v → s v = C₁.twI (rep v) := fun v hv => if_pos hv
  have hs_un : ∀ v, ¬ TwistedAt D₁ v → s v = C₁.twI v := fun v hv => if_neg hv
  let P : ∀ i : D₁.ntw.Tw, (Σ (Q : Finset (PlE D₁.host)) (k : ℕ), D₁.ntw.RCG i Q →* (D₁.ntw.Ok i k)ˣ) → Prop :=
    fun i z => ∀ r, TwistedAt D₁ r → C₁.twI r = i → ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l i) →
      IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 i (twEps D₁ i) (S1 i) (A i) z.1 z.2.1 (z.2.2 ^ a)
  have hch : ∀ i (B : Finset (PlE D₁.host)), ∃ z, P i z ∧ Disjoint z.1 B := by
    intro i B
    by_cases hex : ∃ r, TwistedAt D₁ r ∧ C₁.twI r = i
    · obtain ⟨r, hr, rfl⟩ := hex
      obtain ⟨Q, k, ψ, hq⟩ := (key r hr).2 (A (C₁.twI r) ∪ B)
      refine ⟨⟨Q, k, ψ⟩, fun r' _ _ a ha => (goodTw_union (hq a ha)).1, ?_⟩
      have h1 := (goodTw_union (hq 1 (by simp))).2
      exact h1
    · exact ⟨⟨∅, 0, 1⟩, fun r hr he => absurd ⟨r, hr, he⟩ hex, Finset.disjoint_empty_left _⟩
  obtain ⟨f, hf, hf'⟩ := exists_disjoint_choice (Z := fun i => Σ (Q : Finset (PlE D₁.host)) (k : ℕ),
    D₁.ntw.RCG i Q →* (D₁.ntw.Ok i k)ˣ) (fun _ z => z.1) P hch (hfin.toFinset.image s)
  have goodAt : ∀ i, (∃ r, TwistedAt D₁ r ∧ C₁.twI r = i) → TwIn.Ok (⟨twEOf xd₁, N1, S1⟩ : TwIn D₁) i ∧
      ∀ a : ℤ, Nat.Coprime a.natAbs (D₁.ntw.l i) →
        IntegralHeckeForms.GoodTw D₁.nexp (BlochKatoReduction.bk0 D₁) (twEOf xd₁) N1 i (twEps D₁ i) (S1 i) (A i) (f i).1 (f i).2.1 ((f i).2.2 ^ a) := by
    rintro i ⟨r, hr, rfl⟩
    exact ⟨(key r hr).1, hf _ r hr rfl⟩
  have hmem : ∀ v, TwistedAt D₁ v → s v ∈ hfin.toFinset.image s := fun v hv =>
    Finset.mem_image_of_mem s (hfin.mem_toFinset.2 hv)
  refine ⟨⟨s, fun v => ?_, fun v => ?_, fun v v' hv hv' ho => ?_, xd₁, hall, N1, S1, fun i => (f i).1, fun i => (f i).2.1,
    fun i => (f i).2.2, fun v hv => goodAt (s v) ⟨rep v, (hrep v hv).1, (hs_tw v hv).symm⟩,
    fun v v' hv hv' hne => hf' _ (hmem v hv) _ (hmem v' hv') hne⟩⟩
  · by_cases hv : TwistedAt D₁ v
    · rw [hs_tw v hv]
      exact ReadsAt.of_pair hG (readsAt_of_tie hT (rep v)) ((hrep v hv).2.symm hG)
    · exact ⟨C₁.sd v, by rw [hs_un v hv]; exact readsAt_of_tie hT v⟩
  · by_cases hv : TwistedAt D₁ v
    · rw [hs_tw v hv, hs_tw _ ((twistedAt_conj D₁ v).2 hv), hrep_eq v _ (overOnePair_conj v)]
    · rw [hs_un v hv, hs_un _ (fun h => hv ((twistedAt_conj D₁ v).1 h)), hc v]
  · rw [hs_tw v hv, hs_tw v' hv', hrep_eq v v' (Or.inl ho)]

end GlobalTheory.HeightCounting.Up
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPosIffMemExample
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar

theorem addValuation_pos_iff_valuation_lt_one {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    0 < Examples₂.PlacesToy.valW w x ↔ w.valuation K x < 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [Examples₂.PlacesToy.valW_of_ne w hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.log_exp]
  norm_cast
  exact neg_pos

theorem addValuation_pos_iff_mem_asIdeal {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    0 < Examples₂.PlacesToy.valW w (x : K) ↔ x ∈ w.asIdeal := by
  rw [addValuation_pos_iff_valuation_lt_one, ← w.valuation_lt_one_iff_mem (K := K)]

theorem addVal_pos_iff {K : Type} [Field K] (v : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) :
    0 < v x ↔ ¬ 0 ≤ v x⁻¹ := by
  have h : v x + v x⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  generalize v x = a at h
  generalize v x⁻¹ = b at h
  cases a with
  | top => simp at h
  | coe a =>
    cases b with
    | top => simp at h
    | coe b =>
      norm_cast at h ⊢
      omega

theorem overOne_plUnder (X : Stages) {B' : Base} (h : Enl X.B B') (v v' : B'.places.Pl)
    (hv : ∀ x ∈ B'.LL0, 0 ≤ B'.places.val v x ↔ 0 ≤ B'.places.val v' x) :
    OverOne X.toD7 (plUnder h v) (plUnder h v') := by
  intro x
  let y : 𝓞 X.B.LL := algebraMap (𝓞 ↥X.B.LL0) (𝓞 X.B.LL) x
  have key : ∀ u : B'.places.Pl, 0 < Examples₂.PlacesToy.valW (K := X.B.LL) (plUnder h u) (y : X.B.LL) ↔
      0 < Examples₂.PlacesToy.valW (K := B'.LL) u (incl h (y : X.B.LL)) := fun u =>
    (addValuation_pos_iff_mem_asIdeal _ y).trans ((mem_plUnder h u y).trans
      (addValuation_pos_iff_mem_asIdeal (K := B'.LL) u (RingOfIntegers.mapRingHom (incl h) y)).symm)
  have hm : incl h (y : X.B.LL) ∈ B'.LL0 := by
    have h1 : X.B.embLL (y : X.B.LL) ∈ B'.embLL '' ↑B'.LL0 := h.2.2.1 ▸ ⟨_, (x : ↥X.toD7.LL0).2, rfl⟩
    obtain ⟨z, hz, e⟩ := h1
    rw [← B'.embLL.injective (e.trans (embLL_incl h _).symm)]
    exact hz
  refine (key v).trans (Iff.trans ?_ (key v').symm)
  by_cases h0 : incl h (y : X.B.LL) = 0
  · rw [h0, AddValuation.map_zero, AddValuation.map_zero]
  · rw [addVal_pos_iff _ h0, addVal_pos_iff _ h0]
    exact not_congr (hv _ (B'.LL0.inv_mem hm))

theorem Seed.psiOk {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) {v : D.what₂.places.Pl} (hv : TwistedAt D v) :
    BlochKatoReduction.Gen.PsiOk (σ.s v) (A (σ.s v)) (σ.Q (σ.s v)) (σ.k (σ.s v)) (σ.ψ (σ.s v)) := by
  classical
  have h := ((σ.good v hv).2 1 (by simp)).1
  rw [zpow_one] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.2⟩, h3⟩

end GlobalTheory.HeightCounting.Up

end
end

