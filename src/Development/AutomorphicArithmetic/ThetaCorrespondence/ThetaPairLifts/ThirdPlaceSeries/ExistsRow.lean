module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MMvDmvAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0251
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0132
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowLocPin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0258
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTiedRowLoc
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

macro "kc%" t:term:max : term => `(by with_unfolding_all exact ($t :))

open Lean Elab Tactic in
local elab "row_exact " term:term : tactic =>
  closeMainGoalUsing `row_exact fun target _ => do
    let value ← elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    let actual ← instantiateMVars (← Meta.inferType value)
    let target ← instantiateMVars target
    let lctx ← instantiateLCtxMVars (← getLCtx)
    match Kernel.isDefEq (← getEnv) lctx actual target with
    | .ok true => pure value
    | .ok false => throwError "expected{indentExpr target}\nbut the term has type{indentExpr actual}"
    | .error e => throwKernelException e

local macro "row_cast%" t:term:max : term => `(by row_exact $t)

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr
noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D)
theorem Mv.rowLoc_alt {D : D7} (m : Mv D) {C : NChoice D} (a : _root_.GlobalTheory.HeightCounting.NAllCAlt D C) (F : Formalism.L2.RowFrame D) (F' : Formalism.L2.RowFrame m.D)
    (hF : HEq F'.rep F.rep) (x : _root_.Formalism.L2.RowLocTiedAlt D a.gal.lp F) : _root_.Formalism.L2.RowLocTiedAlt m.D ((_root_.UpperTheory.One.M.mvAll_alt trivial) m a).gal.lp F' := by
  obtain ⟨rep, inj⟩ := F
  obtain ⟨rep', inj'⟩ := F'
  have e : rep' = row_cast% rep := eq_of_heq (row_cast% hF)
  subst e
  exact (@_root_.Formalism.L2.RowLocTiedAlt.mk (_) (_) (_)
    (sat := row_cast% x.sat)
    )

set_option maxHeartbeats 16000000 in
theorem exists_nonempty_nMore_upL (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (nch : NChoice (w.D Z)) (xd : ThData (w.D Z))
    (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (p0' : BaseLevelRowSide (w.D (upL Z S' N h))) (t' : RowsT K w (upL Z S' N h) Wt p0')
    (hs : RowsSame t t')
    (hg : HEq t'.r.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo))
    (hj : ∀ (μ : (w.D Z).what₂.Tup) (hμ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ) (hμ' : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ) (i : Fin (w.D Z).R.m) (x : (w.D Z).what₂.Mt μ ((i : ℕ) + 1)), HEq (t'.r.Y.IL.jMt μ hμ' i x).1 (t.r.Y.IL.jMt μ hμ i x).1)
    (hser : ∀ (kKs : ↥t.r.z.core.Q.c.F →+* ↥(w.st Z).toD7.LL0) (hk : ∀ x, ((kKs x : ↥(w.st Z).toD7.LL0) : (w.st Z).toD7.what₂.LL) = algebraMap _ (w.st Z).toD7.what₂.LL x) (YS : Formalism.IndefR.NX.NExpRealS t.r.z.R t.r.z.cG (Formalism.IndefR.NX.ratDatR t.r.z.R t.r.z.cG kKs hk)) (kKs' : ↥t'.r.z.core.Q.c.F →+* ↥(w.st (upL Z S' N h)).toD7.LL0) (hk' : ∀ x, ((kKs' x : ↥(w.st (upL Z S' N h)).toD7.LL0) : (w.st (upL Z S' N h)).toD7.what₂.LL) = algebraMap _ (w.st (upL Z S' N h)).toD7.what₂.LL x) (YS' : Formalism.IndefR.NX.NExpRealS t'.r.z.R t'.r.z.cG (Formalism.IndefR.NX.ratDatR t'.r.z.R t'.r.z.cG kKs' hk')), HEq kKs' kKs → HEq YS'.fi YS.fi → HEq YS'.eF YS.eF → ∀ (a : _root_.GlobalTheory.HeightCounting.NAllCAlt (w.D Z) nch) (X' : Formalism.L2.NExpTied (w.st (upL Z S' N h)).toD7), HEq X' ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a).exp → ∀ (PV : ∀ i : Fin (w.st Z).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (w.st Z).toD7.R.nV) (PV' : ∀ i : Fin (w.st (upL Z S' N h)).toD7.R.m, Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc (w.st (upL Z S' N h)).toD7 i) (w.st (upL Z S' N h)).toD7.R.nV), HEq (fun i => (PV' i).ψ) (fun i => (PV i).ψ) → ∀ Pq Pq', HEq Pq' Pq → SerAt (D := (w.st Z).toD7) YS t.r.z.geo.v₀ a.exp PV (TC.cf w.I w.l Z) Pq → Nonempty (SerAt (D := (w.st (upL Z S' N h)).toD7) YS' t'.r.z.geo.v₀ X' PV' (TC.cf w.I w.l (upL Z S' N h)) Pq'))
    {tp : TupTied (w.D Z) (TC.cf w.I w.l Z) nch} {tp' : TupTied (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch)}
    (a : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D Z) (TC.cf w.I w.l Z) nch tp)
    (a' : _root_.GlobalTheory.Mem.Top.Bl.NAtData hL (w.D (upL Z S' N h)) (TC.cf w.I w.l (upL Z S' N h)) (nchUp S' N h nch) tp') (hA : _root_.GlobalTheory.LayerMove.AtSameAltAlt (mvOf w Z S' N h) a a')
    (r : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st Z).toD7) a t.r.z.R t.r.z.F t.r.z.cG t.r.Y) (e : _root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st Z).toD7) r t.r.z.geo xd) :
    ∃ r' : _root_.GlobalTheory.Mem.Top.Bl.NormRealisationData (D := (w.st (upL Z S' N h)).toD7) a' t'.r.z.R t'.r.z.F t'.r.z.cG t'.r.Y,
      Nonempty (_root_.GlobalTheory.HeightCounting.RealExpansionExtraData (D := (w.st (upL Z S' N h)).toD7) r' t'.r.z.geo (xdUp S' N h xd)) := by
  cases t' with | mk hX' r' exAt' inGeo' grpAt' grp' mu' exact' untw' emt0' emt' etaF' rowInt' idx' => ?_
  cases r' with | mk z' holds' Y' ZZ' tupix' => ?_
  cases z' with | mk Xg' tr' core' alg_eq' R' cG' geo' pins' lev' idG' good' muz' le' ks' => ?_
  rename_i alg'
  have e1 : Xg' = t.r.z.Xg := hs.Xg
  have e2 : tr' = t.r.z.tr := hs.tr
  subst e1 e2
  have e3 : core' = R3.Tr.coreJ (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) t.r.z.core := eq_of_heq hs.core
  subst e3
  have e4 : alg' = t.r.z.alg := by
    apply Algebra.algebra_ext
    intro y
    apply (w.D Z).what₂.embLL.injective
    exact (alg_eq' y).trans (t.r.z.alg_eq y).symm
  subst e4
  have e5 : R' = R3.Tr.real3 (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (upL Z S' N h) (iK := t.r.z.alg) t.r.z.R := eq_of_heq hs.R
  subst e5
  have e6 : cG' = t.r.z.cG := eq_of_heq hs.cG
  subst e6
  have e7 : geo' = row_cast% (GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      (upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) := eq_of_heq (row_cast% hg)
  subst e7
  obtain ⟨nt', all', chr_eq', host', frameN', chrN', chrGal', Pq', Pq_over', pq', jE_eq', mt_eq', Pq_eq', hlow', split', ratIn',
    r1', r2', r3', depth'⟩ := a'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hA
  have e8 : all' = row_cast% ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all) := eq_of_heq (row_cast% s1)
  have e9 : Pq' = row_cast% a.Pq := eq_of_heq (row_cast% s2)
  subst e8 e9
  obtain ⟨kKs, hk, nexp, hecke, grp, rowLoc, S_eq, hL_eq, rep_eq⟩ := r
  obtain ⟨ad, fi, hrow, cHk, eig, ser, tau, geo, ok, th, xda, large, labc, zeta, pht⟩ := e
  obtain ⟨geo⟩ := geo
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, IL', _, _, _, eFT', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨eW', _⟩, _⟩ := Y'
  have e10 : eW' = row_cast% t.r.Y.mj.eW := eq_of_heq (row_cast% hs.eW)
  subst e10
  obtain ⟨Sb, ev, hSb, hev, hE⟩ := eig
  obtain ⟨i1, i2, i3⟩ := s7 ⟨labc, zeta, pht⟩
  obtain ⟨l1, l2, l3, l4, l5, lv⟩ := grp.lvl
  refine Nonempty.elim (hser kKs hk nexp (row_cast% kKs) (row_cast% hk) (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := row_cast% nexp.fi)
    (geq := row_cast% nexp.geq)
    (rho := row_cast% nexp.rho)
    (chi := row_cast% nexp.chi)
    (eF := row_cast% nexp.eF)
    (bsup := row_cast% nexp.bsup)
    (act := row_cast% nexp.act)
    )
    (row_cast% (HEq.refl kKs)) (row_cast% (HEq.refl nexp.fi)) (row_cast% (HEq.refl nexp.eF)) a.all (row_cast% ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all).exp)
    (row_cast% (HEq.refl ((_root_.UpperTheory.One.M.mvAll_alt trivial) (mvOf w Z S' N h) a.all).exp)) ad.PV (@fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := row_cast% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (row_cast% x1)).ψ)
      (inj := row_cast% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (row_cast% x1)).inj)
      (into := row_cast% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (row_cast% x1)).into)
      (onto := row_cast% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (row_cast% x1)).onto))
    (row_cast% (HEq.refl fun i => (ad.PV i).ψ)) a.Pq (row_cast% a.Pq) (row_cast% (HEq.refl a.Pq)) ser) fun ser' => ?_
  let oldRead := ad.read
  refine ⟨@_root_.GlobalTheory.Mem.Top.Bl.NormRealisationData.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (row_cast% kKs) (row_cast% hk)
    (@_root_.Formalism.IndefR.NX.NExpRealS.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (fi := row_cast% nexp.fi)
    (geq := row_cast% nexp.geq)
    (rho := row_cast% nexp.rho)
    (chi := row_cast% nexp.chi)
    (eF := row_cast% nexp.eF)
    (bsup := row_cast% nexp.bsup)
    (act := row_cast% nexp.act)
    )
    (@_root_.Formalism.IndefR.NX.NExpRealH.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (hL := row_cast% hecke.hL)
    (hs := row_cast% hecke.hs)
    (cHk := row_cast% hecke.cHk)
    (cHk_zero := row_cast% hecke.cHk_zero)
    (cHk_unit := row_cast% hecke.cHk_unit)
    (cHk_pow := row_cast% hecke.cHk_pow)
    (hkEq := row_cast% hecke.hkEq)
    )
    (@_root_.Formalism.L2.DIV.GrpTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (card := row_cast% grp.card)
    (e0 := row_cast% grp.e0)
    (lvl0 := row_cast% grp.lvl0)
    (psi0 := row_cast% grp.psi0)
    (idxSharp := row_cast% grp.idxSharp)
    (lvl := ⟨row_cast% l1, row_cast% l2, row_cast% l3, row_cast% l4, row_cast% l5,
      ⟨row_cast% lv.place, row_cast% lv.comp, row_cast% lv.gen, row_cast% lv.p0, row_cast% lv.chi0, row_cast% lv.ps, row_cast% lv.chis⟩⟩)
    )
    (row_cast% ((mvOf w Z S' N h).rowLoc_alt a.all _ (row_cast% (Formalism.L2.Col.rowFrameOf (w.D (upL Z S' N h)) _ eFT')) (row_cast% hs.rep) rowLoc))
    (row_cast% (s3.trans S_eq)) (row_cast% (s4.trans hL_eq)) (row_cast% ((s5.trans rep_eq).trans hs.rep.symm)), ⟨@_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (@_root_.GlobalTheory.HeightCounting.MtAd.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (PV := @fun x1 => @_root_.Formalism.IndefR.principalLevelFrame.RowPsi.mk (_) (_) (_)
      (ψ := row_cast% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (row_cast% x1)).ψ)
      (inj := row_cast% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (row_cast% x1)).inj)
      (into := row_cast% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (row_cast% x1)).into)
      (onto := row_cast% (@_root_.GlobalTheory.HeightCounting.MtAd.PV (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) ad (row_cast% x1)).onto))
    (std := row_cast% ad.std)
    (eW := row_cast% ad.eW)
    (read := by
      intro μ hμ i x g
      let μ₀ : (w.D Z).what₂.Tup := row_cast% μ
      have hμ₀ : Formalism.IndefR.RecTie.Used0 (w.D Z) μ₀ := row_cast% hμ
      have hμ₁ : Formalism.IndefR.RecTie.Used0 (w.D (upL Z S' N h)) μ₀ := row_cast% hμ
      let i₀ : Fin (w.D Z).R.m := row_cast% i
      let x₀ : (w.D Z).what₂.Mt μ₀ ((i₀ : ℕ) + 1) := row_cast% x
      let g₀ : Formalism.AUTREP.GAf (w.D Z).host.E (w.D Z).R.nV := row_cast% g
      let oldMap := (t.r.Y.IL.jMt μ₀ hμ₀ i₀ x₀).1
      let newMap := (IL'.jMt μ hμ i x).1
      have hmaps : oldMap = row_cast% newMap := by
        refine eq_of_heq ?_
        row_exact ((hj μ₀ hμ₀ hμ₁ i₀ x₀).symm)
      row_exact ((oldRead μ₀ hμ₀ i₀ x₀ g₀).trans (congrFun hmaps ((ad.PV i₀).ψ g₀))))
    (rat := row_cast% ad.rat)
    (wt := row_cast% ad.wt)
    (id := row_cast% ad.id)
    )
    (row_cast% fi)
    (@Formalism.IndefR.NX.NExpHeckeRowX.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (row_cast% hrow.tie))
    (row_cast% cHk)
    ⟨row_cast% Sb, row_cast% ev, row_cast% hSb, row_cast% (s6.trans hev), fun i σ k P α Rr hd => row_cast% (hE (row_cast% i) (row_cast% σ) k (row_cast% P) (row_cast% α) (row_cast% Rr)
      ⟨row_cast% (@HkDat.split (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), row_cast% (@HkDat.offS (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        row_cast% (@HkDat.odd (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), row_cast% (@HkDat.le (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd),
        row_cast% (@HkDat.elt (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd), row_cast% (@HkDat.reps (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) hd)⟩)⟩
    (row_cast% ser'
    )
    ?_
    ⟨@_root_.GlobalTheory.GeoTie.ThetaTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
    (side := @fun x1 => @fun x2 => @fun x3 => @_root_.GlobalTheory.GeoTie.SideTie.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_)
      (pt := row_cast% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (row_cast% x1) (row_cast% x2) (row_cast% x3)).pt)
      (cover := row_cast% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (row_cast% x1) (row_cast% x2) (row_cast% x3)).cover)
      (ev_eq := row_cast% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (row_cast% x1) (row_cast% x2) (row_cast% x3)).ev_eq)
      (fmUr := row_cast% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (row_cast% x1) (row_cast% x2) (row_cast% x3)).fmUr)
      (hk := row_cast% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (row_cast% x1) (row_cast% x2) (row_cast% x3)).hk)
      (hk_none := row_cast% (@_root_.GlobalTheory.GeoTie.ThetaTie.side (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) geo (row_cast% x1) (row_cast% x2) (row_cast% x3)).hk_none))
    (isUnramified₂ := row_cast% geo.isUnramified₂)
    ⟩
    (row_cast% ok) (row_cast% th) (row_cast% xda) (row_cast% ((mvOf w Z S' N h).large large)) (row_cast% i1) (row_cast% i2) (row_cast% i3)⟩⟩
  row_exact ((mvOf w Z S' N h).tauTrue_alt (a := a.all) tau)
end GlobalTheory.LayerMove
end
end
