module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2903
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BalancedSymmetricLieTensorsFiniteProjectiveRank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLift
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon.Assemble

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U Y : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : Y ⟶ U) :
    Fam A (ev M (fst A Y) (snd A Y ≫ u)) := by
  have hN : (ev M (fst A Y) (snd A Y ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hN, (isAdditive_iff hN).2 fun Z a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Z a a' _


omit [GrpObj A] in
theorem same_comp {T U Y Z : Over S} {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left} (hN : N.IsLB) (hM : M.IsLB)
    {y : Y ⟶ T} {u : Y ⟶ U} (h : Same A N M y u) (z : Z ⟶ Y) :
    evc hN (fst A Z) (snd A Z ≫ z ≫ y) = evc hM (fst A Z) (snd A Z ≫ z ≫ u) := by
  have e := congrArg (CechPic.pull (lift (fst A Z) (snd A Z ≫ z)).left) ((same_iff hN hM y u).1 h)
  simpa only [pull_evc, lift_fst, lift_snd_assoc, Category.assoc] using e

theorem exists_lift {S' : Over S} [IsFinite S'.hom] [Surjective S'.hom] {K : Type} [Field K] [IsAlgClosed K]
    (s : Sp K ⟶ S) : Nonempty (Over.mk s ⟶ S') := by
  obtain ⟨t, ht⟩ := exists_lift_pt S'.hom s
  exact ⟨Over.homMk t ht⟩

theorem fibInj {B S' U : Over S} [IsFinite S'.hom] [Surjective S'.hom] {b : B ⟶ S'} {P : LB (A ⊗ B).left}
    (hP : Rep A b P) {M : LB (A ⊗ U).left} (hM : Fam A M) {j : U ⊗ S' ⟶ B} (hj : j ≫ b = snd U S')
    [IsOpenImmersion j.left] (h : Same A M P (fst U S') j) : FibInj A M := by
  intro K _ _ s Y y u u' huu
  obtain ⟨t⟩ := exists_lift (S' := S') s
  have : Mono j := (Over.forget S).mono_of_mono_map (show Mono j.left from inferInstance)
  have k : ∀ v : Y ⟶ U, evc hM.isLB (fst A Y) (snd A Y ≫ v) =
      evc hP.fam.isLB (fst A Y) (snd A Y ≫ lift v (y ≫ t) ≫ j) := fun v ↦ by
    simpa only [lift_fst] using same_comp hM.isLB hP.fam.isLB h (lift v (y ≫ t))
  have hN := fam_ev hM u
  have e : lift u (y ≫ t) ≫ j = lift u' (y ≫ t) ≫ j := by
    refine (hP.univ Y (y ≫ t) _ hN).unique ⟨by rw [Category.assoc, hj, lift_snd], ?_⟩
      ⟨by rw [Category.assoc, hj, lift_snd], ?_⟩
    · exact (cls_eq_iff hN.isLB (pull_isLB hP.fam.isLB _)).1 (k u)
    · exact (cls_eq_iff hN.isLB (pull_isLB hP.fam.isLB _)).1
        (((same_iff hM.isLB hM.isLB u u').1 huu).trans (k u'))
  have e' := congrArg (· ≫ fst U S') ((cancel_mono j).1 e)
  simpa only [lift_fst] using e'

theorem exists_point {B S' U : Over S} {P : LB (A ⊗ B).left} (hP : P.IsLB) {M : LB (A ⊗ U).left} (hM : M.IsLB)
    {j : U ⊗ S' ⟶ B} [IsOpenImmersion j.left] (h : Same A M P (fst U S') j) {K : Type} [Field K]
    {s : Sp K ⟶ S} {N : LB (A ⊗ Over.mk s).left} (hN : N.IsLB) (x : Over.mk s ⟶ B)
    (hx : LBIso N (ev P (fst A _) (snd A _ ≫ x))) (hr : x.left (default : PrimeSpectrum K) ∈ Set.range j.left) :
    ∃ u : Over.mk s ⟶ U, Same A N M (𝟙 _) u := by
  have hr' : Set.range x.left ⊆ Set.range j.left := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum K) z default]
  have fac := IsOpenImmersion.lift_fac j.left x.left hr'
  let v : Over.mk s ⟶ U ⊗ S' := Over.homMk (IsOpenImmersion.lift j.left x.left hr') (by
    rw [← Over.w j, ← Category.assoc, fac]; exact Over.w x)
  have hv : v ≫ j = x := Over.OverMorphism.ext fac
  refine ⟨v ≫ fst U S', (same_id_iff hN hM _).2 ((cls_eq_iff hN (pull_isLB hM _)).1 ?_)⟩
  rw [(cls_eq_iff hN (pull_isLB hP _)).2 hx, cls_ev hP, cls_ev hM, same_comp hM hP h v, hv]

theorem isPullback_prod (X Y : Over S) : IsPullback (fst X Y) (snd X Y) (toUnit X) (toUnit Y) :=
  ⟨⟨toUnit_unique _ _⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst c.snd) (fun _ ↦ lift_fst _ _)
    (fun _ ↦ lift_snd _ _) fun c m h₁ h₂ ↦ by ext <;> simp [h₁, h₂]⟩⟩

theorem toUnit_left (X : Over S) : (toUnit X).left = X.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit X))

end GlobalTheory.DualCon.Assemble

namespace GlobalTheory.DualCon
open Assemble

theorem hasRep_of_liftAt (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (B S' : Over (Sp R)) (b : B ⟶ S')
    (P : LB (A ⊗ B).left) (hf : IsFinite S'.hom) (hs : Surjective S'.hom) (hP : Rep A b P)
    (hb : GlobalTheory.DualCon.Good g b.left) (hl : ∀ x : B.left, LiftAt A g b P x) : HasRep A g (𝟙_ _) := by
  choose U M j hM hU hj ho hx h using hl
  have hc : ∀ x, IsChart A (M x) := fun x ↦
    _root_.GlobalTheory.ChartCrit.openChart R A g hA hg (U x) (M x) (hU x) (hM x) (fibInj hP (hM x) (hj x) (h x))
  obtain ⟨B₀, P₀, i, hP₀, hi, hcov, -⟩ := _root_.GlobalTheory.PicGlue.glue (Sp R) A hA B.left U M hc (by
    intro K _ _ s N hN
    obtain ⟨t⟩ := exists_lift (S' := S') s
    obtain ⟨x, ⟨-, hxN⟩, -⟩ := hP.univ _ t N hN
    exact ⟨_, exists_point hP.fam.isLB (hM _).isLB (h _) hN.isLB x hxN (hx _)⟩)
  have hsm : SmoothOfRelativeDimension g B₀.hom := by
    have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension g)
      (Scheme.Cover.mkOfCovers B.left (fun x ↦ (U x).left) (fun x ↦ (i x).left) hcov hi) fun x ↦ ?_
    have e : (i x).left ≫ B₀.hom = (U x).hom := Over.w _
    exact (congrArg (@SmoothOfRelativeDimension g _ _) e).mpr (hU x)
  have hpb := isPullback_prod B₀ S'
  obtain ⟨e, he, -⟩ := rep_unique (Sp R) A B (B₀ ⊗ S') S' b P _ _ hP
    (GlobalTheory.T.rep_ev_of_isPullback (Sp R) A B₀ _ S' _ _ P₀ _ _ _ hP₀ hpb)
  have hpb' : IsPullback (e.hom ≫ fst B₀ S') b (toUnit B₀) (toUnit S') :=
    hpb.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp [← he]) (by simp) (by simp)
  refine ⟨B₀, toUnit B₀, P₀, hP₀, _root_.GlobalTheory.DualCon.good_of_isPullback_finite_surjective _ _ _ _ _ _ _ _ g (hpb'.map (Over.forget _)) ?_ ?_ ?_ hb⟩
  · exact (congrArg (@IsFinite _ _) (toUnit_left S')).mpr hf
  · exact (congrArg (@Surjective _ _) (toUnit_left S')).mpr hs
  · exact (congrArg (@SmoothOfRelativeDimension g _ _) (toUnit_left B₀)).mpr hsm

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleHypothesesOfStandingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareThetaTripleHypotheses_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T)
    (i j : Fin D.R.m), SquareStanding G t → SquareTriple W t i j := by
  first | exact @GlobalTheory.FunObj.squareTriple_of_standing | exact GlobalTheory.FunObj.squareTriple_of_standing | (intros; apply GlobalTheory.FunObj.squareTriple_of_standing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1FiniteAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFinGen

theorem finite_piece (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (f : R) (hf : IsIdempotentElem f) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - f}))))) :
    Module.Finite (R ⧸ Ideal.span {1 - f}) ((R ⧸ Ideal.span {1 - f}) ⊗[R] HO1 A.hom) := by
  haveI : IsLocalization.Away f (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem hf
  haveI : Module.Flat R (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.flat (R ⧸ Ideal.span {1 - f}) (Submonoid.powers f)
  let B : Over (Sp (R ⧸ Ideal.span {1 - f})) :=
    (Over.pullback (spMap (algebraMap R (R ⧸ Ideal.span {1 - f})))).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj _ A hA
  have hBg : SmoothOfRelativeDimension g B.hom := hg
  obtain ⟨hfp, -, -, -⟩ := hO _ B g hB hBg
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (R ⧸ Ideal.span {1 - f}) A.left B.left A.hom B.hom
    (pullback.fst _ _) (IsPullback.of_hasPullback _ _) inferInstance inferInstance
  haveI := hfp.1
  exact Module.Finite.equiv e.symm

theorem finite_HO1 (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) : Module.Finite R (HO1 A.hom) := by
  obtain ⟨n, e, he, hsm⟩ := GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension R A hA
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff, ← he.complete]
    exact Ideal.sum_mem _ (fun k _ ↦ Ideal.subset_span ⟨k, rfl⟩)
  have hidem : ∀ g : Set.range e, IsIdempotentElem g.val := by
    rintro ⟨_, k, rfl⟩; exact he.idem k
  haveI : ∀ g : Set.range e, IsLocalization.Away g.val (R ⧸ Ideal.span {1 - g.val}) := fun g ↦
    IsLocalization.Away.quotient_of_isIdempotentElem (hidem g)
  haveI : ∀ g : Set.range e, IsLocalizedModule.Away g.val
      (TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) := fun g ↦
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.val) (R ⧸ Ideal.span {1 - g.val}) _).2
      (TensorProduct.isBaseChange R (HO1 A.hom) (R ⧸ Ideal.span {1 - g.val}))
  refine Module.Finite.of_localizationSpan' (Set.range e) hspan
    (Rₚ := fun g ↦ R ⧸ Ideal.span {1 - g.val})
    (Mₚ := fun g ↦ (R ⧸ Ideal.span {1 - g.val}) ⊗[R] HO1 A.hom)
    (fun g ↦ TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) (fun g ↦ ?_)
  obtain ⟨_, k, rfl⟩ := g
  obtain ⟨d, hd⟩ := hsm k
  exact finite_piece hO A hA (e k) (he.idem k) d hd

end GlobalTheory.CechFinGen

theorem GlobalTheory.CechFinGen.finite_HO1_onAff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ U : X.affineOpens,
    Module.Finite Γ(X, U.1) (HO1 (GlobalTheory.DeRhamSheaf.onAff t.G U.2).hom) := by
  intro E _ _ _ H X t hp U
  letI : GrpObj (GlobalTheory.DeRhamSheaf.onAff t.G U.2) := Functor.grpObjObj
  have hA : IsAbelianScheme t.G := GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hp
  exact GlobalTheory.CechFinGen.finite_HO1 GlobalTheory.AbCoh.oStr (GlobalTheory.DeRhamSheaf.onAff t.G U.2) (GlobalTheory.DeRhamSheaf.isAbelianScheme_onAff hA U.2)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOfScaledSectionValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatSym
open GlobalTheory.HeatMod

theorem VS.sub : ∀ {R Ω : Type} [CommRing R] [IsDomain R] [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) {Y : Scheme.{0}} (p : Y ⟶ Sp R) (L : LB Y) (x : Sp Ω ⟶ Y) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 Y)), x ≫ p = spMap φ → ∀ (k : ℕ) (s s' : FractionRing Ω), GlobalTheory.HeatSym.VS φ L x g k s → GlobalTheory.HeatSym.VS φ L x g k s' → GlobalTheory.HeatSym.VS φ L x g k (s - s') := by
  intro R Ω _ _ _ _ φ Y p L x g hxp k s s' ⟨r, σ, ω, hr, hv, he⟩ ⟨r', σ', ω', hr', hv', he'⟩
  refine ⟨r * r', constFn p ⊤ r' • σ - constFn p ⊤ r • σ', φ r' * ω - φ r * ω', mul_ne_zero hr hr', ?_, ?_⟩
  · intro Z t z J hJ
    have e : ∀ a : R, ((spMap φ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) =
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a) := by
      intro a
      have := congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
      exact this.symm
    have key : ∀ a : R, germConstHom ((t ≫ x) ≫ p) z a =
        gs t z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (φ a)) := by
      intro a
      rw [Category.assoc, hxp, gs_eq t z ⊤ trivial, ← e]; rfl
    have hm := hJ.mem (fun _ : Fin 1 => 𝟙 Y) (t ≫ x)
    have h2 : ∀ (a : R) (τ : SecM (𝟙 Y) L k), sval (constFn p ⊤ a • τ) (t ≫ x) z J =
        germConstHom ((t ≫ x) ≫ p) z a * sval τ (t ≫ x) z J := fun a τ =>
      (gs_mul _ z _ hm _ _).trans (congrArg₂ (· * ·)
        ((gs_res _ z le_top hm _).trans (gs_constFn_eq_germConstHom p _ z a)) rfl)
    rw [sval_sub_constFn_smul p _ _ r (t ≫ x) z hJ, h2, hv Z t z J hJ, hv' Z t z J hJ, key, key]
    simp only [gs_eq t z ⊤ trivial, map_sub, map_mul]
    ring
  · rw [map_sub, map_mul, map_mul, he, he', map_mul, map_mul]
    ring

end GlobalTheory.HeatSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBalancedTensorsFiniteProjectiveRankDim
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.BalProj

theorem balanced_finite_projective_rank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  intro E _ _ _ H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA
  obtain ⟨h1A, haddA, hmulA⟩ := _root_.GlobalTheory.BalProj.actMat_ringHom H Y.t Γ(Y.X, U.1) (chart U) n v A hv hb hA
  obtain ⟨hfin, hproj, hrk⟩ := _root_.GlobalTheory.BalProj.Alg.balanced_finite_projective_rank H c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA
  refine ⟨hfin, hproj, fun m hm => ?_⟩
  have key : ∀ τ : E →+* ℂ, GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) m.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ) = if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q := by
    intro τ
    set e : ℕ := if τ (H.rt : E) = H.rt0 then Dw.p else Dw.q with he
    let f : PrimeSpectrum Γ(Y.X, U.1) → ℕ := fun 𝔭 => GlobalTheory.BalProj.eigRank (algebraMap Γ(Y.X, U.1) 𝔭.asIdeal.ResidueField) A
      (GlobalTheory.BalProj.embR c.F c.conj (GlobalTheory.BalProj.fnHom Y.s U.1) τ)
    have hop : ∀ N, IsOpen {𝔭 | f 𝔭 = N} := fun N =>
      _root_.GlobalTheory.BalProjOpen.isOpen_eigRank_eq c.F c.conj Γ(Y.X, U.1) (GlobalTheory.BalProj.fnHom Y.s U.1) n A h1A haddA hmulA τ N
    have hcl : IsClosed {𝔭 | f 𝔭 = e} := by
      rw [← isOpen_compl_iff]
      have : {𝔭 | f 𝔭 = e}ᶜ = ⋃ N ∈ {N : ℕ | N ≠ e}, {𝔭 | f 𝔭 = N} := by
        ext 𝔭; simp
      rw [this]
      exact isOpen_biUnion fun N _ => hop N
    have hsub : (chart U).base ⁻¹' (interior Y : Set Y.X) ⊆ {𝔭 | f 𝔭 = e} := fun 𝔭 h𝔭 =>
      _root_.GlobalTheory.BalProjInt.eigRank_interior E H Dw l Xo c Y h1 hsm hsnc U n v A hv hb hA 𝔭 h𝔭 τ
    have hall : {𝔭 | f 𝔭 = e} = Set.univ :=
      Set.eq_univ_of_univ_subset ((_root_.GlobalTheory.BalProj.chart_dense_interior E H Dw l Xo c Y U).closure_eq ▸ (closure_mono hsub).trans hcl.closure_subset)
    have := hall ▸ Set.mem_univ (⟨m, hm.isPrime⟩ : PrimeSpectrum Γ(Y.X, U.1))
    exact this
  have h2 := hrk m
  simp_rw [key] at h2
  rw [_root_.GlobalTheory.BalProj.signature_count E H Dw.p Dw.q] at h2
  unfold Datum.dim
  omega

end GlobalTheory.BalProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisUniformisedGroupOfRaynaudExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentBasis_uniformisedGroup_of_raynaudExtension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ⇑b = v' := by
  first | exact @GlobalTheory.TanRayBasis.vBasis_of_isPointOf | exact GlobalTheory.TanRayBasis.vBasis_of_isPointOf | (intros; apply GlobalTheory.TanRayBasis.vBasis_of_isPointOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoLogDetGramChangeSemiPositiveMetric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HSAmpDet

theorem chInt_smul {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (D : ℕ) (c : ℝ) (u : SmFn p) :
    chInt L D (u.smul c).u = c * chInt L D u.u := by
  simp only [chInt, SmFn.smul, Weight.chernInt_const_mul, mul_finsum]

section
variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem vals_smul (P : Pair p) (u : SmFn p) (t : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul t)) a b g = fun σ y i => vals P a b g σ y i * (Real.exp (-(a * (t * u.u σ y)) / 2) : ℝ) := by
  funext σ y i
  exact ((_root_.GlobalTheory.HSAmp.upAtPrime_groups_values_norms k X p P (u.smul t) a b).2.2 σ y (g i)).1

theorem vals_zero (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 0)) a b g = vals P a b g := by
  rw [vals_smul]
  funext σ y i
  simp

theorem vals_one (P : Pair p) (u : SmFn p) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic P (u.smul 1)) a b g = vals (upperParabolic P u) a b g := by
  rw [vals_smul]
  funext σ y i
  rw [one_mul]
  exact ((_root_.GlobalTheory.HSAmp.upAtPrime_groups_values_norms k X p P u a b).2.2 σ y (g i)).1.symm

theorem vals_two (P : Pair p) (u : SmFn p) (t t' : ℝ) (a b : ℤ) {ι : Type} (g : ι → X.functionField) :
    vals (upperParabolic (upperParabolic P (u.smul t)) (u.smul (t' - t))) a b g = vals (upperParabolic P (u.smul t')) a b g := by
  rw [vals_smul, vals_smul, vals_smul]
  funext σ y i
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

end

theorem tendsto_logDet_gram_sub : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ (u : SmFn p) (a a' : ℝ), (up P.L u).SemiPos D → P.L.IsSelfInter a → (up P.L u).IsSelfInter a' → Tendsto (fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1)) atTop (𝓝 (2 * (a' - a) / (D + 1).factorial)) := by
  intro hA k _ X _ p D hX hG P hP ω r f hf hli hr u a a' hsp ha ha'
  obtain ⟨s, hs0, hs1, hsd⟩ := _root_.GlobalTheory.HSAmp.SelfPoly.selfInter_poly hA k X p D hX P.L u a a' ha ha'
  set c : ℝ := 2 / ((D + 1).factorial : ℝ) with hc
  let ℓ : ℚ → ℕ → ℝ := fun t m =>
    Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P (u.smul (t : ℝ))) m 1 (f m))).det.re / (m : ℝ) ^ (D + 1)
  have hR := _root_.GlobalTheory.riemann_sum_of_one_sided_increments (Polynomial.C c * s) ℓ ?_
  · have hfun : (fun m => ℓ 0 m - ℓ 1 m) = fun m : ℕ => (Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re - Real.log (gram (fun σ => (ω σ).meas) (vals (upperParabolic P u) m 1 (f m))).det.re) / (m : ℝ) ^ (D + 1) := by
      funext m
      simp only [ℓ, Rat.cast_zero, Rat.cast_one, vals_zero, vals_one, sub_div]
    have hval : (Polynomial.C c * s).eval 1 - (Polynomial.C c * s).eval 0 = 2 * (a' - a) / (D + 1).factorial := by
      simp only [Polynomial.eval_mul, Polynomial.eval_C, hs0, hs1, hc]
      ring
    rw [hfun, hval] at hR
    exact hR
  · intro t t' ht0 ht1 ht0' ht1' ε hε
    have hsemi : (upperParabolic P (u.smul (t : ℝ))).L.SemiPos D :=
      _root_.GlobalTheory.HSAmp.semiPos_up_smul k X p D P.L u t (by exact_mod_cast ht0) (by exact_mod_cast ht1) hP hsp
    have hH : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P (u.smul (t : ℝ))).H m 1 := fun m i => by
      rw [(_root_.GlobalTheory.HSAmp.upAtPrime_groups_values_norms k X p P (u.smul (t : ℝ)) m 1).1]
      exact hf m i
    have hrk : Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
        (𝓝 (gdeg (upperParabolic P (u.smul (t : ℝ))).L D / D.factorial)) := by
      rw [show (upperParabolic P (u.smul (t : ℝ))).L = up P.L (u.smul (t : ℝ)) from rfl,
        _root_.GlobalTheory.GdegMetric.gdeg_up hA k X p D hX P.L (u.smul (t : ℝ))]
      exact hr
    have hstep := _root_.GlobalTheory.HSAmp.gram_det_up_le k X p D hX hG (upperParabolic P (u.smul (t : ℝ))) hsemi ω r f hH hli hrk
      (u.smul ((t' : ℝ) - t)) ε hε
    have hch : chInt (upperParabolic P (u.smul (t : ℝ))).L D (u.smul ((t' : ℝ) - t)).u / D.factorial =
        ((t' : ℝ) - t) * (Polynomial.C c * s).derivative.eval (t : ℝ) := by
      rw [chInt_smul, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, ← hsd t, hc,
        Nat.factorial_succ]
      have hf0 : (D.factorial : ℝ) ≠ 0 := by positivity
      show ((t' : ℝ) - t) * chInt (up P.L (u.smul (t : ℝ))) D u.u / D.factorial = _
      push_cast
      field_simp
    filter_upwards [hstep, eventually_ge_atTop 1] with m hm hm1
    have hpos : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      positivity
    rw [vals_two, hch] at hm
    simp only [ℓ]
    rw [← sub_div, div_le_iff₀ hpos]
    linarith

end GlobalTheory.HSAmpDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatiosStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_eq_of_generic_section_ratios : (∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) → ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g = φ → ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e) := by
  first | exact @GlobalTheory.Mum.thick_eq_of_ratios | exact GlobalTheory.Mum.thick_eq_of_ratios | (intros; apply GlobalTheory.Mum.thick_eq_of_ratios <;> assumption)
end

