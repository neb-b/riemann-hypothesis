module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0558
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O.CompModel

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}

theorem stalkPt_genStr (C : FlagCpt Z e) (z : C.Y.X) (φ : c.F →+* C.Y.X.presheaf.stalk z)
    (hφ : constF e C.Y = (algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField).comp φ) :
    stalkPt C.Y z ≫ C.π ≫ genStr Z = spMap φ := by
  let ρ : c.F →+* C.Y.X.presheaf.stalk z := (Spec.preimage (stalkPt C.Y z ≫ C.π ≫ genStr Z)).hom
  have h0 : spMap ρ = stalkPt C.Y z ≫ C.π ≫ genStr Z := Spec.map_preimage _
  let j := algebraMap (C.Y.X.presheaf.stalk z) C.Y.X.functionField
  letI := (constF e C.Y).toAlgebra
  have hgen : spMap j ≫ stalkPt C.Y z = genericPt C.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.Y.X).specializes trivial)
  have h1 : spMap (j.comp ρ) = spMap (constF e C.Y) := by
    rw [← sp_comp, h0, ← Category.assoc, ← Category.assoc, hgen]
    exact (congrArg (· ≫ genStr Z) C.y0_x.symm).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) Z.jQ_over).trans (pullback.lift_snd _ _ _)))
  have h2 : j.comp ρ = constF e C.Y := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  have h3 : ρ = φ := RingHom.ext fun r => IsFractionRing.injective (C.Y.X.presheaf.stalk z) C.Y.X.functionField
      ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun hφ r))
  rw [← h0, h3]

theorem exists_flagPt (C : FlagCpt Z e) {K : Type} [Field K] (p : Sp K ⟶ C.Y.X) :
    ∃ y : FlagPt Z K, p ≫ C.π = y.y ∧ C.Carries p y.frame := by
  obtain ⟨φ, f, t, hT, -⟩ := C.gr_spec (below p)
  let ψ : C.Y.X.presheaf.stalk (below p) →+* K := (Scheme.stalkClosedPointTo p).hom
  have hp : p = spMap ψ ≫ stalkPt C.Y (below p) := (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
  have hx : spMap ψ ≫ stalkPt C.Y (below p) ≫ C.π ≫ genι Z = (p ≫ C.π) ≫ genι Z := by
    rw [← Category.assoc, ← hp, Category.assoc]
  obtain ⟨g, hg⟩ : ∃ g : EigFrame Z (ψ.comp φ) ((p ≫ C.π) ≫ genι Z), ∀ τ i, g.v τ i = spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ i := by
    rw [← hx]
    exact EigFrame.exists_baseChange E H Dw l Xo c O β Z _ _ φ _ f ψ
  have ho : (p ≫ C.π) ≫ genStr Z = spMap (ψ.comp φ) := by
    rw [← sp_comp, ← stalkPt_genStr C _ φ hT.2.1, ← Category.assoc (spMap ψ), ← hp, Category.assoc]
  refine ⟨⟨ψ.comp φ, p ≫ C.π, ho, g.v, g.tan, g.eig, g.basis⟩, rfl, below p, ψ, φ, f, t, 1, hp, hT, hx.symm, rfl,
    fun τ i => ⟨Pi.single i 1, by simp, fun k hk => Pi.single_eq_of_ne hk.ne' _, ?_⟩⟩
  change IsCombAtG Z.t ((p ≫ C.π) ≫ genι Z)
    (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) (Pi.single i 1) (g.v τ i)
  rw [show (fun k => spMap (Formalism.L2.Pj.dualMap ψ) ≫ f.v τ k) = g.v τ from funext fun k => (hg τ k).symm]
  exact isCombAtG_single Z.t _ (g.tan τ) i

end Free

section Model

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (M : TrueGeo.Model Y)

end Model

end GlobalTheory.Mean4O.CompModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerMatrixFirstOrderDeformation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
open GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlagTan

open TensorProduct GlobalTheory.Frames GlobalTheory.Published

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem IsKSR.baseChangeForKSFamily (P : AbelianDeRham) {Φ : Finset (E →+* ℂ)} {S S' : Type} [CommRing S] [Algebra c.F S]
    [CommRing S'] [Algebra c.F S'] {ψ : S →ₐ[c.F] S'} {y : FrPt Xo c S} {y' : FrPt Xo c S'} (h : FrMap ψ y y')
    {x : Sp (DualNumber S) ⟶ Xo.X} {M : HIx Dw Φ → S}
    (hM : IsKSR Φ y x M) : IsKSR Φ y' (spMap (dualMap ψ.toRingHom) ≫ x) (ψ ∘ M) := by
  obtain ⟨A, _, A', _, π, π', i, hi, b, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hM
  let : Algebra S S' := ψ.toRingHom.toAlgebra
  obtain ⟨B, _, φ, hφ⟩ := exists_isGrpPullback A (spMap (algebraMap S S'))
  obtain ⟨B', _, φ', hφ'⟩ := exists_isGrpPullback A' (spMap (dualMap (algebraMap S S')))
  have e₀ : spMap (algebraMap S S') ≫ GlobalTheory.DeRham.epsRed S = GlobalTheory.DeRham.epsRed S' ≫ spMap (dualMap (algebraMap S S')) := by
    rw [← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (φ ≫ i) ≫ A'.hom = (B.hom ≫ GlobalTheory.DeRham.epsRed S') ≫ spMap (dualMap (algebraMap S S')) := by
    rw [(hφ.comp hi).1.w, e₀, Category.assoc]
  have sq : hφ'.1.lift _ _ w ≫ φ' = φ ≫ i := hφ'.1.lift_fst _ _ _
  have hj : IsGrpPullback B B' (GlobalTheory.DeRham.epsRed S') (hφ'.1.lift _ _ w) :=
    hφ'.cancel ((hφ.comp hi).congr e₀ sq.symm) (hφ'.1.lift_snd _ _ _)
  have hU := ObjDim.isAbelianScheme Xo.univ
  have hg := ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  obtain ⟨bc, hF⟩ := P.2.2.1 S A _ hA gA S' B φ hφ
  have hL := (P.2.1 S' B _ (PolPull.isAbelianScheme_of_isGrpPullback hA hφ)
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hφ.1 gA)).1
  obtain ⟨b', hpol', eb⟩ := hpol.pull_comp (AbelianDeRham.bcMor hφ) (UnivPol.pol Xo).isLB
  choose tv htv using ArcQ.NormalForm.exists_baseChange hφ
  choose th hth using bc.exists
  refine ⟨B, _, B', _, φ ≫ π, φ' ≫ π', _, hj, b', fun σ k => tv (ub σ k), fun k => th (hb k),
    (hφ.comp hπ).congr h.1.symm rfl, hφ'.comp hπ', by rw [← Category.assoc, sq, Category.assoc, e], hpol',
    fun σ k => ?_, fun σ k => (hl σ k).baseChange (hφ := hφ) hF hL (hth _) (htv _), fun τ a => ?_⟩
  · rw [← Category.assoc, htv, Category.assoc, hu, h.2.1] <;> rfl
  · obtain ⟨w, hw, f, hf, hd, hv⟩ := hM τ a
    refine ⟨tv w, ArcQ.NormalForm.isLieComb_baseChange hφ (fun _ => htv _) (htv w) hw, th f,
      mem_Fil_of_corr (hφ := hφ) hF (hth f) hf, fun k => ?_,
      hv.baseChange (hφ := hφ) P hA' gA' hj hφ' sq (hth f) (htv w)⟩
    rw [eb _ _ _ _ (hth f) (hth _), hd]
    split_ifs <;> simp


end GlobalTheory.FlagTan

namespace GlobalTheory.KSFam

theorem conj_embK' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (τ : E →+* ℂ) (z : 𝓞 E) : embK c (conjEmb τ) (H.bar z) = embK c τ z := by
  apply Subtype.ext
  rw [embK_coe, embK_coe]
  show starRingEnd ℂ (τ ((H.bar z : 𝓞 E) : E)) = τ (z : E)
  rw [H.9 z, NumberField.IsCMField.complexEmbedding_complexConj, Complex.conj_conj]

theorem ksFamily : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hP : GlobalTheory.Published.AbelianDeRham) {S : Type} [CommRing S] [Algebra c.F S]
    (y : FrPt Xo c S) (x' : Sp (DualNumber S) ⟶ Xo.X) (h1 : x' ≫ Xo.s = sOf c (DualNumber S))
    (h2 : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ x' = y.x), ∃ Mx : HIx Dw (psiSet H) → S, ∀ (K : Type) [Field K] [Algebra c.F K] (ψ : S →ₐ[c.F] K) (y' : FrPt Xo c K),
      FrMap ψ y y' → GlobalTheory.FlagTan.IsKS (psiSet H) y' (spMap (Formalism.L2.Pj.dualMap ψ.toRingHom) ≫ x') (ψ ∘ Mx) := by
  intro E _ _ _ H Dw l Xo c hP S _ _ y x' h1 h2
  suffices hM : ∃ M, GlobalTheory.FlagTan.IsKSR (psiSet H) y x' M by
    obtain ⟨M, hM⟩ := hM
    refine ⟨M, fun K _ _ ψ y' hy => GlobalTheory.FlagTan.isKSR_iff_isKS.mp ?_⟩
    exact GlobalTheory.FlagTan.IsKSR.baseChangeForKSFamily hP hy hM

  let : GrpObj ((Over.pullback x').obj Xo.univ.t.G) := Functor.grpObjObj (F := Over.pullback x')
  let : GrpObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    Functor.grpObjObj (F := Over.pullback (GlobalTheory.DeRham.epsRed S))
  have hA' := isGrpPullback_pullback Xo.univ.t.G x'
  have hi := isGrpPullback_pullback ((Over.pullback x').obj Xo.univ.t.G) (GlobalTheory.DeRham.epsRed S)
  have hA : IsGrpPullback ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G))
      Xo.univ.t.G y.x (pullback.fst _ _ ≫ pullback.fst _ _) := (hi.comp hA').congr h2 rfl
  have : IsCommMonObj ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) :=
    GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hA
  have hab := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hsm := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hab' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA'
  have hab0 := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hab hA
  have hsm' : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback x').obj Xo.univ.t.G).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm
  have hsm0 : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))
      ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)).hom := by
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := Module.finrank ℚ E / 2 * (Dw.p + Dw.q))).of_isPullback
      (IsPullback.of_hasPullback _ _) hsm'

  obtain ⟨ψ, hpol, hiso, hperf, hmax⟩ := _root_.GlobalTheory.PolExistsRing.polForm_exists hP Xo hA

  obtain ⟨a', ha'⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback Xo.univ.t.act hA'
  obtain ⟨a, ha⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a' hi
  have haπ : ∀ z, (a.act z).left ≫ (pullback.fst _ _ ≫ pullback.fst _ _) =
      (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (Xo.univ.t.act.act z).left := by
    intro z
    rw [← Category.assoc, ha z, Category.assoc, ha' z, Category.assoc]
  have hadj := _root_.GlobalTheory.PolAdjointRing.polForm_adjoint hP Xo hA a haπ hpol

  obtain ⟨ub, hub1, hubT, hubE, hubS⟩ := GlobalTheory.T.exists_tangent_frame_of_framedPoint_commRing y hA a haπ
  have hex : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), ∃ h, IsLieImage h (ub k.1 k.2) := fun k =>
    (hP.2.1 S _ _ hab0 hsm0).1.2 _ (hubT k.1 k.2)
  choose hb hhb using hex
  obtain ⟨hspan, hlin⟩ := _root_.GlobalTheory.LieBasisRing.lifts_basis_mod_fil hP y hA ub hub1 hb hhb
  have hreg := GlobalTheory.T.kodairaSpencerUniqueValue_abelianScheme_commRing hP hi hab' hsm'
  have hcomp := fun z f w (e : IsKSValue hi f w) => _root_.GlobalTheory.KSExist.isKSValue_act hi a a' ha z e
  have heig : ∀ (k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ))) (z : 𝓞 E),
      act (dp0 S) (𝟙 _) a z (hb k) - (algebraMap c.F S).comp (embK c k.1) z • hb k ∈
        Fil ((Over.pullback (GlobalTheory.DeRham.epsRed S)).obj ((Over.pullback x').obj Xo.univ.t.G)) := by
    intro k z
    have := a.hom z
    have e1 := (hhb k).push (a.act z)
    rw [hubE] at e1
    rw [act_apply]
    exact e1.sub_mem ((hhb k).smul _)
  have key : ∀ (τ : psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))), ∃ cf : Fin (Dw.mult τ.1) → S, ∃ w,
      IsLieComb cf (ub τ.1) w ∧ GlobalTheory.FlagTan.IsKSRow hi ψ hb ⟨conjEmb τ.1, j⟩ w := fun τ j =>
    _root_.GlobalTheory.KSRing.ksRow_exists_lieComb_ring hi a (fun z => H.bar z) ψ hiso hmax hperf hadj hreg hcomp
      (fun σ => (algebraMap c.F S).comp (embK c σ)) ub hb hspan hlin heig hubS τ.1 (conjEmb τ.1)
      (fun z => by simp only [RingHom.comp_apply, conj_embK']) j
  choose cf hcf using key
  exact ⟨fun k => cf k.1 k.2.1 k.2.2, _, inferInstance, _, inferInstance, _, _, _, hi, ψ, ub, hb, hA, hA', rfl, hpol,
    hub1, fun σ k => hhb ⟨σ, k⟩, fun τ j => hcf τ j⟩

end GlobalTheory.KSFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLaurentArcDegeneratingOnModelConvergence
section
noncomputable section

namespace GlobalTheory.ArcQZ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem hasSum_evR_of_chart_natural (hL : GlobalTheory.Reg.EvLaws Xo c) (σ : c.F →+* ℂ) [Algebra c.F ℂ⸨X⸩]
    (hK : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    {v : ℂ} (hv : v ≠ 0) {R : Type} [CommRing R] [Algebra c.F R] (φ : R →ₐ[c.F] ℂ⸨X⸩) (ψ : R →ₐ[c.F] CAt σ)
    (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ⸨X⸩) (s : ℂ⸨X⸩)
    (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ)
    {y₀ : FrPt Xo c R} {y₁ y : FrPt Xo c ℂ⸨X⸩} {yw₁ yw : FrPt Xo c (CAt σ)}
    (h₁ : FrMap φ y₀ y₁) (hy : FrChg G s y₁ y) (hw₁ : FrMap ψ y₀ yw₁) (hyw : FrChg Gw sw yw₁ yw)
    (hφ : ∀ f, HasSum (fun n : ℤ => (φ f).coeff n * v ^ n) (toC (ψ f)))
    (hG : ∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * v ^ n) (toC (Gw τ i k)))
    (hs : HasSum (fun n : ℤ => s.coeff n * v ^ n) (toC sw))
    (hG' : ∀ τ, Summable fun n : ℤ => ((G τ).det⁻¹).coeff n * v ^ n)
    (hs' : Summable fun n : ℤ => (s⁻¹).coeff n * v ^ n) (F : Rul Xo c)
    (hF : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F) :
    HasSum (fun m : ℤ => (evR Xo c F y).coeff m * v ^ m) (toC (evR Xo c F yw)) := by
  let A := ptRing σ hK hv
  let φA : R →ₐ[c.F] A := φ.codRestrict A fun f => (hφ f).summable
  let GA : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A :=
    fun τ i k => ⟨G τ i k, (hG τ i k).summable⟩
  let sA : A := ⟨s, hs.summable⟩
  obtain ⟨hu1, hu2⟩ := (frChg_exists_unique_units E H Dw l Xo c _ G s y₁).2.2.1 y hy
  have hdet : ∀ τ, ((GA τ).det : ℂ⸨X⸩) = (G τ).det := fun τ => A.val.map_det (GA τ)
  obtain ⟨u₁, hu₁⟩ := hL.bc _ _ φA y₀
  obtain ⟨u, hu⟩ := (frChg_exists_unique_units E H Dw l Xo c A GA sA u₁).1
    (fun τ => isUnit_ptRing σ hK hv _ (by rw [hdet]; exact (hu1 τ).ne_zero) (by rw [hdet]; exact hG' τ))
    (isUnit_ptRing σ hK hv sA hu2.ne_zero hs')
  have e₁ : FrMap A.val u y := frMap_of_frChg_map φA A.val GA sA hu₁ hu h₁ hy
  have eψ : (ptEv σ hK hv).comp φA = ψ := AlgHom.ext fun f => ptEv_eq σ hK hv _ (hφ f)
  have eG : (fun τ => (GA τ).map (ptEv σ hK hv)) = Gw := by
    funext τ
    ext i k
    exact ptEv_eq σ hK hv _ (hG τ i k)
  have es : ptEv σ hK hv sA = sw := ptEv_eq σ hK hv _ hs
  have e₂ : FrMap (ptEv σ hK hv) u yw :=
    frMap_of_frChg_map φA (ptEv σ hK hv) GA sA hu₁ hu (by rw [eψ]; exact hw₁) (by rw [eG, es]; exact hyw)
  rw [GlobalTheory.FlagMod.FlagCover.evR_frMap_of_isReduced hF e₁, GlobalTheory.FlagMod.FlagCover.evR_frMap_of_isReduced hF e₂]
  exact hasSum_ptEv σ hK hv _

theorem hasSum_evR_arc_natural : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) [Algebra c.F ℂ⸨X⸩] (y : FrPt Xo c ℂ⸨X⸩) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR ℂ)) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin g → ℂ)), GlobalTheory.Reg.EvLaws Xo c → (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp β) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ThNZ th → IsArcFr W e th (HahnSeries.ofPowerSeries ℤ ℂ) y → (∀ τ k, AnVec Ha (e τ k) (z τ k)) → ∃ T : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ∀ F : Rul Xo c, IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) F → HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (toC (evR Xo c F yw)) := by
  intro hL1 hL2 E _ _ _ H Dw l Xo c σ _ _ O _ β Y a χ W g ty Fu Ha _ y e th Θ z hL hK hχ hβ hP hth hy hz
  obtain ⟨pt, -, -, -, -, hpt1, hpt2, -⟩ := id hy
  have hpt3 : pt ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ⸨X⸩) := by
    rw [← cancel_mono (spMap β), Category.assoc, ← Y.jQ_over, Category.assoc, ← pullback.condition,
      ← Category.assoc Y.jQ, ← Category.assoc]
    show (pt ≫ Y.j) ≫ Y.s = _
    rw [hpt1, Category.assoc, hχ]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x => (hK (β x)).symm
  obtain ⟨p, j, y₀, hch, hmem⟩ := _root_.GlobalTheory.Frames.exists_openChart_testRing hL1.secBaseChange E H Dw l Xo c (pt (IsLocalRing.closedPoint ℂ⸨X⸩))
  haveI := hch.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.ArcQ.exists_algHom_of_mem_range j hch.2.2 pt hpt3 hmem
  obtain ⟨y₁, hy₁⟩ := hL.bc _ _ φ y₀
  obtain ⟨G, s, hGs⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 y₁).2.2.2 y
    (by rw [hy₁.1, ← hch.2.1, ← Category.assoc, hφ, hpt2])
  obtain ⟨T₁, h₁⟩ := GlobalTheory.T.holArc_chart_coordinates_hasSum E H Dw l Xo c σ O β Y a χ W g ty Fu Ha p j φ hK hχ hβ hch.1 hch.2.2
    (by rw [← Category.assoc, hφ, hpt1])
  obtain ⟨T₂, h₂⟩ := GlobalTheory.T.frame_matrix_hasSum_alt hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th z p j y₀ φ y₁ G s
    hK hχ hβ hy hz hch hy₁ hGs
  obtain ⟨T₃, h₃⟩ := GlobalTheory.T.hasSum_thetaGenerator_chart_ratio hL1 hL2 E H Dw l Xo c σ O β Y a χ W g ty Fu Ha y e th Θ p j y₀ φ y₁ G s
    hK hχ hβ hP hth hy hch hy₁ hGs
  have key : ∀ w : ℂ, max T₁ (max T₂ T₃) < w.im → ∀ yw, AnFr Ha Θ z w yw →
      ∃ (ψ : p.R →ₐ[c.F] CAt σ) (yw₁ : FrPt Xo c (CAt σ))
        (Gw : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (sw : CAt σ),
        FrMap ψ y₀ yw₁ ∧ FrChg Gw sw yw₁ yw ∧
        (∀ f, HasSum (fun n : ℤ => (φ f).coeff n * eTwoPi w ^ n) (toC (ψ f))) ∧
        (∀ τ i k, HasSum (fun n : ℤ => (G τ i k).coeff n * eTwoPi w ^ n) (toC (Gw τ i k))) ∧
        HasSum (fun n : ℤ => s.coeff n * eTwoPi w ^ n) (toC sw) := by
    intro w hw yw hyw
    rw [max_lt_iff, max_lt_iff] at hw
    obtain ⟨ψ, hψ1, hψ2⟩ := h₁ w hw.1
    obtain ⟨yw₁, hyw₁⟩ := hL.bc _ _ ψ y₀
    obtain ⟨Gw, sw, hw'⟩ := (frChg_exists_unique_units E H Dw l Xo c _ (fun _ => 1) 1 yw₁).2.2.2 yw
      (by rw [hyw₁.1, ← hch.2.1, hψ1]; exact hyw.1.1)
    exact ⟨ψ, yw₁, Gw, sw, hyw₁, hw', hψ2, h₂ w hw.2.1 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1 hw',
      h₃ w hw.2.2 ψ yw₁ yw Gw sw hψ2 hyw₁ hyw.1.1 hyw.2 hw'⟩
  by_cases hex : ∃ w : ℂ, max T₁ (max T₂ T₃) < w.im ∧ ∃ yw, AnFr Ha Θ z w yw
  · obtain ⟨w₀, hw₀, yw₀, hyw₀⟩ := hex
    obtain ⟨-, -, Gw₀, sw₀, -, -, -, hG₀, hs₀⟩ := key w₀ hw₀ yw₀ hyw₀
    have hv₀ := GlobalTheory.Conv.eTwoPi_ne_zero w₀
    have cs : s⁻¹ ∈ GlobalTheory.Conv.convLaurent :=
      inv_mem (GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ hs₀.summable)
    have cG : ∀ τ, (G τ).det⁻¹ ∈ GlobalTheory.Conv.convLaurent := fun τ => by
      refine inv_mem ?_
      rw [Matrix.det_apply']
      exact sum_mem fun π _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ =>
        GlobalTheory.Conv.mem_convLaurent_of_summable hv₀ (hG₀ τ _ _).summable)
    obtain ⟨T₄, h₄⟩ := GlobalTheory.Conv.exists_forall_mem_halfRing
      (S := insert s⁻¹ (Set.range fun τ => (G τ).det⁻¹)) ((Set.finite_range _).insert _)
      (by rintro _ (rfl | ⟨τ, rfl⟩); exacts [cs, cG τ])
    refine ⟨max T₄ (max T₁ (max T₂ T₃)), fun w hw yw hyw F hF => ?_⟩
    rw [max_lt_iff] at hw
    obtain ⟨ψ, yw₁, Gw, sw, k₁, k₂, k₃, k₄, k₅⟩ := key w hw.2 yw hyw
    exact hasSum_evR_of_chart_natural hL σ hK (GlobalTheory.Conv.eTwoPi_ne_zero w) φ ψ G s Gw sw hy₁ hGs k₁ k₂ k₃ k₄ k₅
      (fun τ => h₄ _ (Or.inr ⟨τ, rfl⟩) w hw.1) (h₄ _ (Or.inl rfl) w hw.1) F hF
  · exact ⟨_, fun w hw yw hyw => absurd ⟨w, hw, yw, hyw⟩ hex⟩

end GlobalTheory.ArcQZ

namespace GlobalTheory.CuspFrom

section SecZ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.Frames
open scoped LaurentSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r}

theorem evR_frChg_one_secZ {S : Type} [CommRing S] [Algebra c.F S] [IsLocalRing S] {ex : Ix Dw → ℤ}
    (hex : ex none = 0) {F : Rul Xo c} (hF : F ∈ GlobalTheory.AllWt.secZ Xo c ex) {s : S} {y y' : FrPt Xo c S}
    (h : FrChg (fun _ => 1) s y y') : evR Xo c F y' = evR Xo c F y := by
  obtain ⟨u, rfl⟩ := ((_root_.GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c S _ s y).2.2.1 y' h).2
  let t : Ix Dw → Sˣ := fun i => i.elim u fun _ => 1
  have hb : FrBor t y y' :=
    ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.2 t y y').2
      ⟨fun _ => 1, fun τ i => by simp [t], fun τ i j hij => Matrix.one_apply_ne hij.ne, h⟩
  rw [GlobalTheory.FlagTan.evR_frBor hF hb]
  simp [t, Fintype.prod_option, hex]

theorem exists_arc_secZ' [Algebra c.F ℂ⸨X⸩]
    (halg : ∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x)))
    (hσ : Formalism.L2.PjFree.GoodEmb c σ) (hU : Formalism.L2.PjFree.IsUnf U) {k : U.Comp} {ξ' : Fin r → E}
    (hξ : (U.X k).IsIso ξ') {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom)
    {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) :
    ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ),
      BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im →
        (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex,
          HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m)
            (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  letI := FractionRing.liftAlgebra ℂ ℂ
  haveI := FractionRing.isScalarTower_liftAlgebra ℂ ℂ
  have hK := GlobalTheory.ArcCM.known_holds
  have h1 := hK.laws
  have h2 := hK.laws2
  have hev := hK.ev E H Dw l Xo c
  obtain ⟨hp, hq⟩ := GlobalTheory.ArcCM.Exist.one_le_of_isIso hU hξ
  obtain ⟨Uw⟩ := GlobalTheory.ArcQ.nonempty_unfWit_of_isUnf E H Dw l Xo c σ r U hU
  obtain ⟨aC, htie⟩ := GlobalTheory.CuspFrom.exists_input Uw hσ hU hξ hx
  obtain ⟨Wp, Y, h4, hpush⟩ := GlobalTheory.CuspFrom.exists_model Xo c (by omega)
  have hmono := mono_spMap_subtype (c.V Wp)
  obtain ⟨χ, hχ, -⟩ := h4 ℂ _ 1 (aC.restrict (c.V Wp).subtype) (Or.inl ⟨Field.toIsField ℂ, rfl⟩)
  obtain ⟨hover, hab, hj, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ _).1 hW
  have hty := (GlobalTheory.Relab.relab_good E H l c _ hσ).2.2.2 Dw Uw.g Uw.e
  obtain ⟨Ha⟩ := hK.n5 E H Dw l Xo c _ _ Y σ _ χ W Uw.g _ Uw.F hσ hty (GlobalTheory.ArcInTest.exists_values c Wp) hover
    (fun q hq => hj q (by simpa using hq))
  obtain ⟨T, s, d, z, hd, hz, hflow⟩ := htie _ _ Y χ W Ha
  obtain ⟨-, v₂, -, -⟩ := GlobalTheory.ExpTan.anVec_bijective h1.globalFns E H Dw l Xo c _ _ _ Y _ _ W _ _ Uw.F Ha
  choose e he using fun τ i => (v₂ (z τ i)).exists
  have hB := _root_.GlobalTheory.CuspFromBasis.main E H Dw l Xo c σ r U Uw _ _ Y _ χ W Ha e z hσ hz he
  obtain ⟨-, -, th, hth⟩ := GlobalTheory.ThetaOverField.nonzero_generates h1 h2 ℂ (aC.restrict (c.V Wp).subtype).D₀
    DVR.SecOps.secZero
  obtain ⟨Θ⟩ := GlobalTheory.ArcTheta.nonempty_thetaDat h1 h2 E H Dw l Xo c σ _ _ Y _ χ W _ _ Uw.F Ha hty th hth
  have hc : (spMap (HahnSeries.ofPowerSeries ℤ ℂ) ≫ χ) ≫ Y.s = spMap (algebraMap c.F ℂ⸨X⸩) ≫ spMap (c.V Wp).subtype := by
    rw [Category.assoc, hover, GlobalTheory.ArcId.sp_comp, GlobalTheory.ArcId.sp_comp, GlobalTheory.ArcId.sp_comp]
    congr 1
    exact RingHom.ext fun t => (halg _).symm
  haveI := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ hc : Sp ℂ⸨X⸩ ⟶ gen Y) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hab]
    intro hq
    have h0 : HahnSeries.ofPowerSeries ℤ ℂ PowerSeries.X ∈ q.asIdeal := hq
    rw [@Ideal.eq_bot_of_prime _ _ q.asIdeal q.isPrime, Ideal.mem_bot] at h0
    exact PowerSeries.X_ne_zero (HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm))
  let z₀ := IsOpenImmersion.lift Y.jQ _ hr
  have hz₀ : z₀ ≫ Y.jQ = _ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨y, -, hy⟩ := GlobalTheory.ArcQ.exists_isArcFr h1 h2 E H Dw l Xo c _ _ Y ℂ _ _ χ W _ e th hB hth (Or.inr hpush) ℂ⸨X⸩
    (HahnSeries.ofPowerSeries ℤ ℂ) z₀ (by unfold RingHom.Flat; infer_instance)
    (by rw [Model.j, ← Category.assoc, hz₀, pullback.lift_fst])
    (by
      rw [pullback.condition, ← Category.assoc, ← Y.jQ_over, ← Category.assoc, hz₀, pullback.lift_snd,
        GlobalTheory.ArcId.sp_comp]
      rfl)
    (fun τ t => halg _)
  have hbd := GlobalTheory.T.arc_framed_point_extends_to_model_boundary E H Dw l Xo c σ _ _ Y _ χ W e th y halg hover hmono hB hy (fun h =>
    (hab _).1 h (by
      change _ ∈ IsLocalRing.maximalIdeal _
      rw [PowerSeries.maximalIdeal_eq_span_X]
      exact Ideal.mem_span_singleton_self _))
  obtain ⟨T', hT'⟩ := GlobalTheory.ArcQZ.hasSum_evR_arc_natural h1 h2 E H Dw l Xo c σ _ _ Y _ χ W _ _ Uw.F Ha y e th Θ z hev halg hover
    hmono hpush hth hy he
  refine ⟨y, max T (max T' Ha.T), s, d, _root_.GlobalTheory.CuspFrom.bdExt_of_bdExt E H Dw l Xo c _ _ Z _ _ Y _ _ _ y
    (RingHom.ext fun t => (halg t).symm) hbd, hd, fun w hw => ?_⟩
  simp only [max_lt_iff] at hw
  obtain ⟨hxw, hlie⟩ := hflow w hw.1
  refine ⟨hxw, fun ex hex0 F hF => ?_⟩
  obtain ⟨yw, hyw, -⟩ := GlobalTheory.ArcQ.AnFrEx.existsUnique_anFr h1 h2 E H Dw l Xo c σ r U Uw _ _ Y _ χ W Ha th Θ z hσ hz w
    hw.2.2
  obtain ⟨t, ht⟩ := GlobalTheory.ArcCoeff.frChg_of_anLie Uw.F Ha.i _ (Ha.period w hw.2.2) _ _ z hlie hyw.1
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have e1 := evR_frChg_one_secZ hex0 hF ht
  have := hT' w hw.2.1 yw hyw F hF.1
  rw [e1] at this
  convert this using 1
  exact dif_pos hxw

end SecZ

end GlobalTheory.CuspFrom

section Final

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open scoped LaurentSeries

theorem GlobalTheory.CuspFrom.exists_arc_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r) [Algebra c.F ℂ⸨X⸩], (∀ x : c.F, algebraMap c.F ℂ⸨X⸩ x = HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.C (R := ℂ) (σ x))) → Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (ξ' : Fin r → E), (U.X k).IsIso ξ' → ∀ x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r, x ∈ (U.X k).dom → ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β), ∃ (y : FrPt Xo c ℂ⸨X⸩) (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ), GlobalTheory.CuspFrom.BdExt Z ((PowerSeries.C (R := ℂ)).comp σ) y ∧ (∀ τ, 0 < d τ) ∧ ∀ w : ℂ, T < w.im → (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom ∧ ∀ ex : Ix Dw → ℤ, ex none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c ex, HasSum (fun m : ℤ => (evR Xo c F y).coeff m * eTwoPi w ^ m) (Formalism.L2.PjFree.rdU U F k ((U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x)) := by
  intro E _ _ _ H Dw l Xo c σ r U _ halg hσ hU k ξ' hξ x hx O _ β Z
  exact GlobalTheory.CuspFrom.exists_arc_secZ' halg hσ hU hξ hx Z

end Final
end
end

