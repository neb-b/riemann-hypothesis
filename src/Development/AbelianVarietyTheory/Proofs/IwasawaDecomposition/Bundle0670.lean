module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealDatumPrerequisitesUpdateModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1110
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqCjOneSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef

namespace GlobalTheory.Mem.R3.Rw.WeilExt

section Defs

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL]
  {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}

def LevSame (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    HEq (R'.toLevCh.mu (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) ((i' : ℕ) + 1)) (z.R.toLevCh.mu (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) ((i : ℕ) + 1)) ∧
    ∀ PP' PP, HEq PP' PP → PP ∈ z.R.Pg → HEq (R'.chi ((i' : ℕ) + 1) PP') (z.R.chi ((i : ℕ) + 1) PP)) ∧
  HEq R'.eta z.R.eta ∧ R'.Q (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) = ∅ ∧ z.R.Q (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) = ∅

def IdemSame (z : Dat (w.st Z) w.I hX T Wt) (Xg : Finset (Gc B' w'.px → B'.LL)) : Prop :=
  ∀ (g' : Gc B' w'.px) (g : Gc B w.px), HEq g' g → B'.embLL ((idemOf Xg).coeff g') = B.embLL ((idemOf z.Xg).coeff g)


set_option maxHeartbeats 1000000 in
def JSpan (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks) : Prop :=
  ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ x' : (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.fam.amb.FL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))),
      ∃ (n : ℕ) (a : Fin n → (w'.st Z').toD7.what₂.LL)
        (x : Fin n → (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))),
        HEq (R'.B.jL i' (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) x') (∑ k, (w'.st Z').toD7.what₂.embLL (a k) • z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))) (x k))

end Defs

theorem ratAt_of_geo {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] (R : RealDat3 D A3 C.Q.c.F)
    (F : Face3 D A3) (hch : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (hI : GlobalTheory.RealGeo.InGeo geo) (hU : R.toRealDat.LUnif) :
    RatAt R.toRealDat A3.A.μ0 := by
  intro i x v hv
  have hio := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A3.A _ R.toRealDat hch.base.lev hch.base.fam hch.base.models
    (RealDat.thP_of_weak hch.base.thP hEx)
  have hM := GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation _ _ _ _ _ _ C R F geo.κ geo.v₀ geo.O (fun _ => 1) hn hch hEx ⟨geo.fw⟩ hio i
    (geo.pins i) (geo.phase i hU)
  have e : v = R.jV i A3.A.μ0 x := (hch.base.models.HV i _).1 (hv.trans (hch.base.models.jV i _ x).symm)
  subst e
  obtain ⟨y, hy⟩ := (Formalism.IndefR.FWT.phase_of_oneMap geo.fw hU
    (hI.evInj i _ (Formalism.IndefR.FWT.base_embedding_good C R.toRealDat geo.fw.alg_eq geo.fw.laws.pins.2.2.1)) (geo.O i) (geo.phase i hU hM.1)).2 x
  exact ⟨y, hy.trans (one_smul ℂ _)⟩

theorem eq_cj_one_smul {H : Type} [AddCommGroup H] [Module ℂ H] (s : Bool) (v : H) : v = Formalism.IndefR.Links.cj s (1 : ℂ) • v := by
  rw [map_one, one_smul]


set_option maxHeartbeats 8000000 in
theorem charW_keep (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks X.toD7.what₂.LL]
    (R₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd) (hI : Inputs X.toD7)
    (hXi : IdemClass (D := X.toD7) (famR X I hX U Xg tr₀).A)
    (hEx : ∀ R : RealDat X.toD7 (famR X I hX U Xg tr₀).A Ks, R.Pre1 (face0 X I hX U Xg tr₀).lv2 → R.IsChainW → R.IsThPW → R.ExAt)
    (S : RealDat X.toD7 (famR X I hX U Xg tr₀).A Ks → Prop)
    (hSM : ∀ R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG, S R →
      S (updM R HX HV HE gE jX jV νY fdY ν0 fd0 νX fdX νV fdV ωP vP thF thG))
    (hS3 : ∀ R ωY ωX vac vacX vY vX ItY ItX ioY ioX Th, S R → S (R.upd3 ωY ωX vac vacX vY vX ItY ItX ioY ioX Th))
    (hS6 : ∀ R kap lam, S R → S (R.upd6 kap lam)) (s0 : S R₀.toRealDat)
    (p0 : R₀.toRealDat.Pre0 (face0 X I hX U Xg tr₀).lv2) (i0 : R₀.IsInert) (t0 : R₀.IsTup) (a0 : R₀.AllPlaces)
    (k0 : Keep R₀.toRealDat (face0 X I hX U Xg tr₀).lv2 cG) (b0 : BrgStd X I hX U Xg tr₀ R₀.toRealDat) (x0 : R₀.toRealDat.grp_chiW)
    (hW : ModW R₀.toRealDat) (hω : WeilAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) (hV : ModVAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0)
    (hl : LiftAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) (hr : RatAt R₀.toRealDat (famR X I hX U Xg tr₀).A.μ0) :
    ∃ (tr : TrI X.B px) (R : RealDat3 X.toD7 (famR X I hX U Xg tr) Ks) (cG' : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      Pins R (face0 X I hX U Xg tr) cG' ∧ R.toRealDat.ExAt ∧ R.toRealDat.toLevCh = R₀.toRealDat.toLevCh ∧ HEq R.eG R₀.eG ∧ HEq cG' cG ∧
      R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧ BrgStd X I hX U Xg tr R.toRealDat ∧ S R.toRealDat ∧
      SameAt (A := (famR X I hX U Xg tr₀).A) R₀.toRealDat R.toRealDat (famR X I hX U Xg tr₀).A.μ0 := by
  classical
  obtain ⟨hL, hF⟩ := GlobalTheory.HeckeCharacterRestriction.liftsAt_and_seedFacts X.toD7 _ _ _ (famR X I hX U Xg tr₀).A Ks (face0 X I hX U Xg tr₀).lv2
  obtain ⟨R1, p1, c1, t1, f1, g1, ⟨q1, s1⟩, m1, hrat⟩ := exists_weak_keep hI hXi hL hF
    (fun R => (RealDat3.IsInert (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      RealDat3.IsTup (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      RealDat3.AllPlaces (⟨R, R₀.plI, R₀.SF, R₀.phs, R₀.lam3⟩ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks) ∧
      R.toLevCh = R₀.toLevCh ∧ HEq R.eG R₀.eG ∧ R.mu = R₀.mu ∧ R.twPl = R₀.twPl ∧
      BrgStd X I hX U Xg tr₀ R ∧ R.grp_chiW ∧
      ∀ c : G0 R.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG → Keep (A3 := (famR X I hX U Xg tr₀)) R (face0 X I hX U Xg tr₀).lv2 c) ∧ S R)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 ⟨h, s⟩ => ⟨by
      obtain ⟨hi, ht, ha, hl, he, hm, hw, hb, hg, hk⟩ := h
      exact ⟨⟨hi.tie, hi.onto, hi.hR, hi.hL, hi.SF⟩, ⟨ht.mu_off, ht.mu_used, ht.mu_ne, ht.mu_conj, ht.mu_on⟩, ha, hl, he, hm, hw, hb, hg, fun c hc => by
        have k := hk c hc
        exact ⟨k.std, k.signs, k.frames, k.beta, k.prX, k.grp, k.psi, k.guard, k.valKs, k.frameKs, k.levKs⟩⟩, hSM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s⟩)
    (fun R a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 ⟨h, s⟩ => ⟨by
      obtain ⟨hi, ht, ha, hl, he, hm, hw, hb, hg, hk⟩ := h
      exact ⟨⟨hi.tie, hi.onto, hi.hR, hi.hL, hi.SF⟩, ⟨ht.mu_off, ht.mu_used, ht.mu_ne, ht.mu_conj, ht.mu_on⟩, ha, hl, he, hm, hw, hb, hg, fun c hc => by
        have k := hk c hc
        exact ⟨k.std, k.signs, k.frames, k.beta, k.prX, k.grp, k.psi, k.guard, k.valKs, k.frameKs, k.levKs⟩⟩, hS3 _ _ _ _ _ _ _ _ _ _ _ _ s⟩)
    R₀.toRealDat p0 ⟨⟨⟨i0.tie, i0.onto, i0.hR, i0.hL, i0.SF⟩, ⟨t0.mu_off, t0.mu_used, t0.mu_ne, t0.mu_conj, t0.mu_on⟩, a0, rfl, HEq.rfl,
      rfl, rfl, b0, x0, fun c hc => by cases eq_of_heq hc; exact k0⟩, s0⟩ hW hω hV hl hr
  obtain ⟨i1, u1, a1, l1, e1, mu1, w1, b1, x1, k1⟩ := q1
  have hc : ∃ c : G0 R1.Pg X.toD7.R.r ≃* G0g X.toD7.nd, HEq c cG := by
    rw [show R1.Pg = R₀.Pg from congrArg (fun L => L.Pg) l1]
    exact ⟨cG, HEq.rfl⟩
  obtain ⟨cutoffDeriv, hcG1⟩ := hc
  let R2₀ : RealDat3 X.toD7 (famR X I hX U Xg tr₀) Ks := ⟨R1, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  have htr : ∃ tr : TrI X.B px, (∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t') →
      R2₀.TrISem (face0 X I hX U Xg tr₀) tr ∧ SepWith (famR X I hX U Xg tr₀) tr := by
    by_cases h : ∃ t', R2₀.TrISem (face0 X I hX U Xg tr₀) t' ∧ SepWith (famR X I hX U Xg tr₀) t'
    · obtain ⟨t', h'⟩ := h
      exact ⟨t', fun _ => h'⟩
    · exact ⟨tr₀, fun h' => absurd h' h⟩
  obtain ⟨tr, htr⟩ := htr
  let R2 : RealDat3 X.toD7 (famR X I hX U Xg tr) Ks := ⟨R1, R₀.plI, R₀.SF, fun _ => 1, R₀.lam3⟩
  obtain ⟨kap, lam, hs⟩ := scalars_exist (F := face0 X I hX U Xg tr) R2
  have p6 := RealDat.preliminary_of_scalar_update p1 kap R2.lam
  have f6 := RealDat.full_Y_of_scalar_update f1 kap R2.lam
  have c6 := RealDat.weak_chain_of_scalar_update c1 kap R2.lam
  have t6 := RealDat.weak_theta_props_of_scalar_update t1 kap R2.lam
  have g6 := RealDat.full_P_of_scalar_update g1 kap R2.lam
  have hphs : (R2.updS kap lam).phase := by
    intro i
    refine ⟨show ‖(1 : ℂ)‖ = 1 from norm_one, fun _ x => ?_⟩
    obtain ⟨y, hy⟩ := hrat i x
    refine ⟨y, ?_⟩
    exact (by with_unfolding_all exact (hy.trans (eq_cj_one_smul (twAt X.toD7.what₂.embLL (famR X I hX U Xg tr₀).A.v0) _) :))
  have kv := k1 cutoffDeriv hcG1
  exact ⟨tr, R2.updS kap lam, cutoffDeriv, ⟨⟨⟨p6.1.lev, ⟨p6.1.red_R, p6.1.red_L, p6.1.levels, p6.1.record, x1⟩,
      p6.1.fam, p6.2, c6, t6⟩, ⟨⟨i1.tie.plI_inj, i1.tie.okI⟩, i1.onto, i1.hR, i1.hL, i1.SF⟩, f6.1, f6.2, g6, hs,
      ⟨u1.mu_off, u1.mu_used, u1.mu_ne, u1.mu_conj, u1.mu_on⟩, hphs, a1⟩,
    ⟨kv.std, kv.signs, kv.frames, kv.beta, kv.prX, kv.grp, kv.psi, kv.guard, kv.valKs, kv.frameKs, kv.levKs⟩,
    fun _ => rfl, fun h => htr h⟩, hEx _ p6 c6 t6, l1, e1, hcG1, mu1, w1, b1, hS6 _ kap R2.lam s1, m1⟩

end GlobalTheory.Mem.R3.Rw.WeilExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationGoodRowsToConjugateGoodRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

variable {D : D7} {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type} {A : FamIn D.what₂.LL G' Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eC_conj_of_match {R : RealDat D A Ks} {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) (g k : G') :
    RealDat.eC (A := A) D.what₂.embLL (g * k * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL k := by
  have e : ∀ x : G', RealDat.eC (A := A) D.what₂.embLL x = star (D.ntypes.e0.coeff (σ.symm x)) := fun x => by
    rw [hC, MulEquiv.apply_symm_apply]
  rw [e, e, show σ.symm (g * k * g⁻¹) = σ.symm g * σ.symm k * (σ.symm g)⁻¹ by simp, GlobalTheory.ProjComm.goodProjector_coeff_classFunction]

theorem eC_conv_of_match {R : RealDat D A Ks} {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) (g : G') :
    ∑ a, RealDat.eC (A := A) D.what₂.embLL a * RealDat.eC (A := A) D.what₂.embLL (a⁻¹ * g) =
      RealDat.eC (A := A) D.what₂.embLL g := by
  have e : ∀ x : G', RealDat.eC (A := A) D.what₂.embLL x = star (D.ntypes.e0.coeff (σ.symm x)) := fun x => by
    rw [hC, MulEquiv.apply_symm_apply]
  simp only [e]
  rw [← GlobalTheory.ProjectedLift.conv_of_idem _ (GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent D).2 (σ.symm g), star_sum]
  refine Fintype.sum_equiv σ.symm.toEquiv _ _ fun a => ?_
  show _ = star (D.ntypes.e0.coeff (σ.symm a) * D.ntypes.e0.coeff ((σ.symm a)⁻¹ * σ.symm g))
  rw [star_mul', map_mul, map_inv]

theorem goodProjector_maps_rows_into_goodRows {R : RealDat D A Ks} {F : Face D A} (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf)
    {σ : G0g D.nd ≃* G'} (hC : LevelMatchC R σ) {S : MMap (MP R)} (hS : S ∈ MultR R F) :
    postOn (MP R) R.e0 S ∈ EP R F := by
  have hX : S ∈ GlobalTheory.Mem.Th.multAt R (R.levR F true) A.μ0 0 := by
    rw [GlobalTheory.Mem.Th.multAt_zero]; exact hS
  have h0 := GlobalTheory.Mem.Th.multAt_le R _ A.μ0 0 hX
  rw [GlobalTheory.Mem.Th.multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 S ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (eC_conv_of_match hC) h0
  refine ⟨GlobalTheory.KeepLevel.mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (S v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 h0).lev v
  refine GlobalTheory.KeepLevel.hasType_of_comm (L := R.dat0 R.triv) (P := R.levR F true) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 hX).lev v)
    fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact GlobalTheory.ProjComm.gaL_comm (L := R.dat0 R.triv) R.eG _ (eC_conj_of_match hC) g a0


set_option maxHeartbeats 1000000 in
theorem evalOn_good : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ), R.toLevCh.Is A.μ0 → R.models_inf → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → SeeAt R F X h t → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R F X h G t v₀ c hl hi hv hsee hJe
  obtain ⟨σ, red, hA, hB, hC⟩ := hsee.mat
  obtain ⟨J, hJ⟩ := hJe
  have hle : EP R F ≤ MultR R F := inf_le_left
  have hmult : ∀ S ∈ MultR R F, IsMultMap R.θ (MP R) (JR R F) (chiR R F) S := fun S hS =>
    (GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ S).1 hS
  have hGQ : ∀ S ∈ MultR R F, ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g := fun S hS =>
    ((hmult S hS).aut v₀).left
  choose s0 hs0 using hB.1.2.2.1
  have hs0' : ∀ γ, s0 γ ∈ X.B.I.Kset ∧ red (s0 γ) = γ := hs0

  have hinv : ∀ S : MultR R F, ∀ k ∈ X.B.I.Kg X.B.g,
      X.B.R (1, k) (star ((J S : conjRows X) : L2X X)) = star ((J S : conjRows X) : L2X X) := by
    intro S k hk
    classical
    have hkK : k ∈ X.B.I.Kset := hk.1
    have hrk : red k = 1 := (hB.1.2.2.2 k hkK).2 hk
    let a : G0g D.nd → ℂ := fun γ => if γ = 1 then 1 else 0
    let s : G0g D.nd → X.B.I.Gf := fun γ => if γ = 1 then k else s0 γ
    have hs : ∀ γ, s γ ∈ X.B.I.Kset ∧ red (s γ) = γ := by
      intro γ
      by_cases hγ : γ = 1
      · subst hγ
        simp only [s, if_pos rfl]
        exact ⟨hkK, hrk⟩
      · simp only [s, if_neg hγ]
        exact hs0' γ
    have hI := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB (S : MMap (MP R)) S.2
      ((J S : conjRows X) : L2X X) (hJ S).1 (hGQ _ S.2) a s hs
    have e1 : (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star ((J S : conjRows X) : L2X X))) : L2X X) =
        star (X.B.R (1, k) (star ((J S : conjRows X) : L2X X))) := by
      rw [Finset.sum_eq_single (1 : G0g D.nd)]
      · simp [a, s]
      · intro b _ hb
        simp [a, hb]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have hsum : (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (a (σ.symm g))) =
        actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG 1) := by
      unfold gaL
      rw [Finset.sum_eq_single (1 : G')]
      · have ha1 : a (σ.symm 1) = 1 := by simp [a]
        simp only [ha1, star_one, one_smul]
        rfl
      · intro b _ hb
        have hb' : σ.symm b ≠ 1 := by
          intro h1
          apply hb
          simpa using congrArg σ h1
        have ha0 : a (σ.symm b) = 0 := by simp [a, hb']
        simp only [ha0, star_zero, zero_smul]
      · intro h1
        exact absurd (Finset.mem_univ _) h1
    have e2 : ∀ y : GA D (D.sp.Y 0),
        (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (a (σ.symm g))) ((S : MMap (MP R)) v₀) y =
          (S : MMap (MP R)) v₀ y := by
      intro y
      rw [hsum]
      have hB2 := hB.2 k hkK (S : MMap (MP R)) S.2 v₀ y
      rw [hrk, map_one σ] at hB2
      refine hB2.symm.trans ?_
      have hK2 := (Formalism.L2.SG.Closed.level_subgroup_properties X).1 k hk
      obtain ⟨hkJ, hkχ⟩ := hA k hK2.1
      have hχ1 : chiR R F (kap X h t k) = 1 := hkχ.trans (by rw [hK2.2, star_one])
      refine ((hmult _ S.2).lev v₀ _ hkJ y).trans ?_
      rw [hχ1, one_mul]
    have e3 : ((star (X.B.R (1, k) (star ((J S : conjRows X) : L2X X))) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X]
        (((J S : conjRows X) : L2X X) : X.B.I.GA → ℂ) := by
      rw [← e1]
      exact hI.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => e2 _) (hJ S).1.symm)
    have e4 := congrArg star (Lp.ext e3)
    rwa [star_star] at e4

  have key : ∀ S : MultR R F,
      ((J ⟨postOn (MP R) R.e0 S, hle (goodProjector_maps_rows_into_goodRows hl hi hC S.2)⟩ : conjRows X) : L2X X) =
        star (G.Rg (star ((J S : conjRows X) : L2X X))) := by
    intro S
    have hexp := GlobalTheory.Mem.GoodExpand.rg_expand D X G red s0 hB.1 hs0' _ (hinv S)
    have hI := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB (S : MMap (MP R)) S.2
      ((J S : conjRows X) : L2X X) (hJ S).1 (hGQ _ S.2) (fun γ => D.ntypes.e0.coeff γ) s0 hs0'
    have e1 : star (G.Rg (star ((J S : conjRows X) : L2X X))) = ∑ γ, star (D.ntypes.e0.coeff γ) •
        star (X.B.R (1, s0 γ) (star ((J S : conjRows X) : L2X X))) := by
      rw [hexp]
      change conjL (muX X) _ = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun γ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply, starRingEnd_apply]
    have e2 : (gaL (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG fun g => star (D.ntypes.e0.coeff (σ.symm g))) = R.e0 := by
      unfold RealDat.e0
      congr 1
      funext g
      rw [hC, MulEquiv.apply_symm_apply]
    rw [e1]
    apply Lp.ext
    refine (hJ _).1.trans (Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun x => ?_) hI.symm)
    rw [e2]
    rfl
  have hEPS : ∀ S : MultR R F, (S : MMap (MP R)) ∈ EP R F ↔ postOn (MP R) R.e0 S = S := by
    intro S
    constructor
    · intro hS
      exact sub_eq_zero.1 (LinearMap.mem_ker.1 hS.2)
    · intro e
      exact ⟨S.2, LinearMap.mem_ker.2 (sub_eq_zero.2 e)⟩
  have hconj : ∀ Fx : L2X X, Fx ∈ EEC X G → Fx ∈ conjRows X := fun Fx hF => (Submodule.mem_inf.1 hF).1
  let L0 : EP R F →ₗ[ℂ] L2X X :=
    (conjRows X).subtype ∘ₗ (J : MultR R F →ₗ[ℂ] conjRows X) ∘ₗ Submodule.inclusion hle
  have hL0 : ∀ S : EP R F, L0 S ∈ EEC X G := by
    intro S
    have hS1 : postOn (MP R) R.e0 (Submodule.inclusion hle S : MultR R F) = (Submodule.inclusion hle S : MultR R F) :=
      (hEPS _).1 S.2
    have k1 := key (Submodule.inclusion hle S)
    have e : (⟨postOn (MP R) R.e0 (Submodule.inclusion hle S : MultR R F),
        hle (goodProjector_maps_rows_into_goodRows hl hi hC (Submodule.inclusion hle S).2)⟩ : MultR R F) = Submodule.inclusion hle S :=
      Subtype.ext hS1
    rw [e] at k1
    have k2 : G.Rg (star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X)) =
        star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) := by
      have k3 := congrArg star k1
      rw [star_star] at k3
      exact k3.symm
    refine Submodule.mem_inf.2 ⟨(J (Submodule.inclusion hle S)).2, LinearMap.mem_ker.2 ?_⟩
    change G.Rg (star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X)) -
      star ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) = 0
    rw [k2, sub_self]
  let L : EP R F →ₗ[ℂ] EEC X G := L0.codRestrict (EEC X G) hL0
  have hLv : ∀ S : EP R F, ((L S : EEC X G) : L2X X) = ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) :=
    fun S => rfl
  have hinj : Function.Injective L := by
    intro x y hxy
    have e1 : ((L x : EEC X G) : L2X X) = ((L y : EEC X G) : L2X X) := by rw [hxy]
    rw [hLv, hLv] at e1
    exact Submodule.inclusion_injective hle (J.injective (Subtype.ext e1))
  have hsurj : Function.Surjective L := by
    intro Fx
    let F' : conjRows X := ⟨(Fx : L2X X), hconj _ Fx.2⟩
    let S : MultR R F := J.symm F'
    have hJS : ((J S : conjRows X) : L2X X) = (Fx : L2X X) := by
      show ((J (J.symm F') : conjRows X) : L2X X) = _
      rw [LinearEquiv.apply_symm_apply]
    have hRg : G.Rg (star (Fx : L2X X)) = star (Fx : L2X X) := by
      have := LinearMap.mem_ker.1 (Submodule.mem_inf.1 Fx.2).2
      exact sub_eq_zero.1 this
    have k1 := key S
    rw [hJS, hRg, star_star, ← hJS] at k1
    have hfix : postOn (MP R) R.e0 S = S := congrArg Subtype.val (J.injective (Subtype.ext k1))
    refine ⟨⟨(S : MMap (MP R)), (hEPS S).2 hfix⟩, Subtype.ext ?_⟩
    rw [hLv]
    exact hJS
  let j : EP R F ≃ₗ[ℂ] EEC X G := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have hj : ∀ S : EP R F, ((j S : EEC X G) : L2X X) = ((J (Submodule.inclusion hle S) : conjRows X) : L2X X) :=
    fun S => rfl
  refine ⟨⟨j, fun S => ?_⟩, ⟨v₀, hv, j, fun S => ?_⟩⟩
  · rw [hj]
    exact hJ _
  · rw [hj]
    exact hJ _

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniform
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.GridField

open GlobalTheory.ChiGrid GlobalTheory.BigTop.Fun

def vPre (s : Stages) (v : HeightOneSpectrum (𝓞 s.toD7.host.F)) : HeightOneSpectrum (𝓞 s.B.toPre.host.F) := v

def toPl {P Q : Pre} (h : P = Q) (v : HeightOneSpectrum (𝓞 P.host.F)) : HeightOneSpectrum (𝓞 Q.host.F) := by
  subst h
  exact v

theorem leastSplitAuxiliaryPrime_congr_preData {s s' : Stages} (h : s.B.toPre = s'.B.toPre) : GlobalTheory.ChiGrid.q0 s.toD7 = GlobalTheory.ChiGrid.q0 s'.toD7 := by
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at h
  subst h
  rfl

theorem exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq {s s' : Stages} {B₀ : Pre} (hs : s.B.toPre = B₀) (hs' : s'.B.toPre = B₀) {T T' : Type}
    {L : Formalism.IndefR.Links.LevCh s.toD7 T} {L' : Formalism.IndefR.Links.LevCh s'.toD7 T'} {sc : Consts} (G : GridData L sc)
    (G' : GridData L' sc) (hv : toPl hs' (vPre s' G'.pl.v0) = toPl hs (vPre s G.pl.v0)) {K : Type} [Field K]
    (e : K →+* ℂ) (hF : FieldHas G' e) : ∃ G'' : GridData L sc, G''.pl = G.pl ∧ FieldHas G'' e := by
  subst hs
  obtain ⟨B, C, W, V, S, N, Gj⟩ := s
  obtain ⟨B', C', W', V', S', N', Gj'⟩ := s'
  cases B
  cases B'
  dsimp only at hs'
  subst hs'
  have hv0 : G'.pl.v0 = G.pl.v0 := hv
  refine ⟨⟨G.pl, ⟨G'.ch.chiH, G'.ch.chi, G'.ch.chi_eq, G'.ch.triv, G'.ch.inf,
      fun i h1 h2 PP hPP => G'.ch.unr i h1 h2 PP ?_, G'.ch.lev1, G'.ch.wild,
      fun i h1 h2 PP hPP => G'.ch.lev0 i h1 h2 PP (hPP.trans hv0.symm)⟩, G.sp⟩, rfl, ?_⟩
  · intro h
    apply hPP
    rcases G'.pl.mem_S0_of_sum_eq.1 h with h | h
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0))
    · exact G.pl.mem_S0_of_sum_eq.2 (Or.inr h)
  · refine ⟨hF.values, fun v hv => ?_⟩
    have hd : G.pl.depth sc v = G'.pl.depth sc v := by
      unfold Places.depth
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (h1.trans hv0.symm) h2
      · exact absurd (h2.trans hv0) h1
      · rfl
    rw [hd]
    refine hF.roots v ?_
    rcases G.pl.mem_S0_of_sum_eq.1 hv with h | h
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inl (h.trans hv0.symm))
    · exact G'.pl.mem_S0_of_sum_eq.2 (Or.inr h)

theorem exists_field_uniform : ∀ (cDep b : ℝ) (B₀ : Pre), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ (s : Stages), s.B.toPre = B₀ → 0 < GlobalTheory.ChiGrid.q0 s.toD7 → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
      (_G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩), ∃ G' : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩,
        GlobalTheory.BigTop.Fun.FieldHas G' M.val.toRingHom := by
  intro cDep b B₀
  classical

  let Wit : Set (HeightOneSpectrum (𝓞 B₀.host.F)) := {v | ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type)
    (L : Formalism.IndefR.Links.LevCh s.toD7 T) (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v}
  have hfin : Wit.Finite := by
    rcases Wit.eq_empty_or_nonempty with h | ⟨v₁, s₁, hs₁, T₁, L₁, G₁, -⟩
    · rw [h]
      exact Set.finite_empty
    · have hn : ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F) ≠ 0 := by
        subst hs₁
        exact_mod_cast (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec s₁.toD7).1.ne_zero
      refine (Formalism.L2.DIV.primesOf ((GlobalTheory.ChiGrid.q0 s₁.toD7 : ℕ) : 𝓞 B₀.host.F)).finite_toSet.subset ?_
      rintro _ ⟨s, hs, T, L, G, rfl⟩
      refine Formalism.L2.DIV.mem_primesOf.2 ⟨hn, ?_⟩
      subst hs
      rw [leastSplitAuxiliaryPrime_congr_preData hs₁]
      exact G.pl.basePlace_over_qZero
  have hex : ∀ v : Wit, ∃ Mv : IntermediateField ℚ ℂ, FiniteDimensional ℚ Mv ∧
      ∃ (s : Stages) (hs : s.B.toPre = B₀) (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T)
        (G : GridData L ⟨1, cDep, b⟩), toPl hs (vPre s G.pl.v0) = v ∧ FieldHas G Mv.val.toRingHom := by
    rintro ⟨v, s, hs, T, L, G, hv⟩
    obtain ⟨Mv, h1, h2⟩ := exists_fieldHas G
    exact ⟨Mv, h1, s, hs, T, L, G, hv, h2⟩
  choose Mv hMv hW using hex
  haveI := hfin.to_subtype
  haveI : ∀ v, FiniteDimensional ℚ (Mv v) := hMv
  refine ⟨⨆ v, Mv v, IntermediateField.finiteDimensional_iSup_of_finite, ?_⟩
  intro s hs _ T L G
  obtain ⟨s', hs', T', L', G', hv', hF⟩ := hW ⟨toPl hs (vPre s G.pl.v0), s, hs, T, L, G, rfl⟩
  have hF' : FieldHas G' (⨆ v, Mv v).val.toRingHom :=
    FieldHas.map (IntermediateField.inclusion (le_iSup Mv _)).toRingHom hF
  obtain ⟨G'', -, h⟩ := exists_gridData_pl_eq_and_fieldHas_of_basePlace_eq hs hs' G G' hv' _ hF'
  exact ⟨G'', h⟩

end GlobalTheory.GridField

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeastSplitAuxiliaryPrimePosAllStates
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.PositiveBaseCharge

theorem q0_pos_allSt : AllSt fun _ _ _ _ _ _ x => 0 < GlobalTheory.ChiGrid.q0 (Dof x) :=
  StepW.of_all fun _ _ _ _ _ _ _ _ _ x => (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec (Dof x)).1.pos

end GlobalTheory.HeightCounting.Up.PositiveBaseCharge
end

