module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgOverHomSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.ArcInf

section General
variable {k : Type} [CommRing k] {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing C] [Algebra k C]

theorem algOverHom_left (ψ : A →ₐ[k] B) : (algOverHom ψ).left = spMap (ψ : A →+* B) := rfl

theorem algOverHom_comp (ψ : A →ₐ[k] B) (χ : B →ₐ[k] C) :
    algOverHom (χ.comp ψ) = algOverHom χ ≫ algOverHom ψ := by
  ext1
  rw [Over.comp_left, algOverHom_left, algOverHom_left, algOverHom_left]
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem algOverHom_id : algOverHom (AlgHom.id k A) = 𝟙 _ := by
  ext1
  rw [algOverHom_left]
  exact Spec.map_id _

theorem algOverHom_injective : Function.Injective (algOverHom : (A →ₐ[k] B) → _) := by
  intro a b h
  have h1 : spMap (a : A →+* B) = spMap (b : A →+* B) := congrArg (fun x => x.left) h
  have h2 := Spec.map_injective h1
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h2)

theorem algOverHom_surjective : Function.Surjective (algOverHom : (A →ₐ[k] B) → _) := by
  intro φ
  obtain ⟨g, hg⟩ := Spec.map_surjective φ.left
  have hw : φ.left ≫ spMap (algebraMap k A) = spMap (algebraMap k B) := Over.w φ
  rw [← hg, ← Spec.map_comp] at hw
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  refine ⟨⟨g.hom, fun c => congrArg (fun f : k →+* B => f c) h2⟩, ?_⟩
  ext1
  exact hg

theorem eq_of_comp_eq {G : Over (Sp k)} {j : algOver k A ⟶ G} (hj : IsOpenImmersion j.left) {a b : A →ₐ[k] B}
    (h : algOverHom a ≫ j = algOverHom b ≫ j) : a = b := by
  apply algOverHom_injective
  ext1
  have := congrArg (fun x => x.left) h
  simp only [Over.comp_left] at this
  exact (cancel_mono j.left).1 this

end General

variable {k : Type} [Field k]

theorem exists_lift {F : Type} [CommRing F] [Algebra k F] (ρ : PowerSeries k →ₐ[k] F)
    (h : IsUnit (ρ PowerSeries.X)) :
    ∃ σ : FractionRing (PowerSeries k) →ₐ[k] F, ∀ x, σ (algebraMap (PowerSeries k) _ x) = ρ x := by
  have hu : ∀ y : nonZeroDivisors (PowerSeries k), IsUnit (ρ y) := by
    rintro ⟨y, hy⟩
    have h0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    obtain ⟨u, hu⟩ := hn.symm
    show IsUnit (ρ y)
    rw [← hu, map_mul, map_pow]
    exact (h.pow n).mul (u.isUnit.map ρ)
  exact ⟨IsLocalization.liftAlgHom (S := FractionRing (PowerSeries k)) hu, fun x => by simp⟩

def IsChart (G : Over (Sp k)) [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    (ε : A →ₐ[k] k) {r : ℕ} (f : Fin r → A) : Prop :=
  IsOpenImmersion j.left ∧ algOverHom ε ≫ j = 1 ∧ Algebra.adjoin k (Set.range f) = ⊤ ∧ ∀ i, ε (f i) = 0

def TwoVar {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] (j : algOver k A ⟶ G)
    {r : ℕ} (f : Fin r → A) (a : algOver k (FractionRing (PowerSeries k)) ⟶ G)
    (h : Fin r → MvPowerSeries (Fin 2) k) (d : MvPowerSeries (Fin 2) k) : Prop :=
  ∀ (F : Type) [Field F] [Algebra k F] (τ : MvPowerSeries (Fin 2) k →ₐ[k] F)
    (σ₀ σ₁ : FractionRing (PowerSeries k) →ₐ[k] F), τ d ≠ 0 →
    (∀ x : PowerSeries k, σ₀ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k))) →
    (∀ x : PowerSeries k, σ₁ (algebraMap _ _ x) = τ (x.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k))) →
    ∃ χ : A →ₐ[k] F, (∀ i, χ (f i) * τ d = τ (h i)) ∧
      algOverHom σ₁ ≫ a = (algOverHom χ ≫ j) * (algOverHom σ₀ ≫ a)

theorem IsChart.hom_ext {G : Over (Sp k)} [GrpObj G] {A : Type} [CommRing A] [Algebra k A] {j : algOver k A ⟶ G}
    {ε : A →ₐ[k] k} {r : ℕ} {f : Fin r → A} (hc : IsChart G j ε f) {B : Type} [CommRing B] [Algebra k B]
    {a b : A →ₐ[k] B} (h : ∀ i, a (f i) = b (f i)) : a = b :=
  AlgHom.ext_of_adjoin_eq_top hc.2.2.1 (by rintro _ ⟨i, rfl⟩; exact h i)

end GlobalTheory.SS.ArcInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DefectBounded
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem exists_pow_factor_free {B S M M' : Type} [CommRing B] [CommRing S] [Algebra B S] (b : B)
    [IsLocalization (Submonoid.powers b) S] [AddCommGroup M] [Module B M] [Module.FinitePresentation B M]
    [AddCommGroup M'] [Module B M'] [Module S M'] [IsScalarTower B S M'] [Module.Projective S M']
    (f : M →ₗ[B] M') [IsLocalizedModule (Submonoid.powers b) f] :
    ∃ (c n : ℕ) (s : M →ₗ[B] (Fin n → B)) (t : (Fin n → B) →ₗ[B] M), t ∘ₗ s = b ^ c • LinearMap.id := by
  classical
  have : Module.FinitePresentation S M' := _root_.FinitePresentation.of_isBaseChange f
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers b) S f).mp inferInstance)
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S M'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property p LinearMap.id hp
  let eS := Finsupp.linearEquivFunOnFinite S S (Fin n)
  let eB := Finsupp.linearEquivFunOnFinite B B (Fin n)
  let ℓ : (Fin n →₀ B) →ₗ[B] (Fin n →₀ S) := Finsupp.mapRange.linearMap (Algebra.linearMap B S)
  let p' : (Fin n →₀ S) →ₗ[S] M' := p ∘ₗ eS.toLinearMap
  let σ' : M' →ₗ[S] (Fin n →₀ S) := eS.symm.toLinearMap ∘ₗ σ
  have hpσ : ∀ x, p' (σ' x) = x := fun x => by
    simpa [p', σ'] using LinearMap.congr_fun hσ x
  obtain ⟨h, s₁, hh⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers b) ℓ ((σ'.restrictScalars B) ∘ₗ f)
  obtain ⟨t, s₂, ht⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    (Submonoid.powers b) f ((p'.restrictScalars B) ∘ₗ ℓ)
  have key : f ∘ₗ (t ∘ₗ h) = f ∘ₗ ((s₂ * s₁) • LinearMap.id) := by
    refine LinearMap.ext fun m => ?_
    have e1 : f (t (h m)) = (s₂ : B) • p' (ℓ (h m)) := by
      simpa [Submonoid.smul_def] using LinearMap.congr_fun ht (h m)
    have e2 : ℓ (h m) = (s₁ : B) • σ' (f m) := by
      simpa [Submonoid.smul_def] using LinearMap.congr_fun hh m
    have e3 : p' ((s₁ : B) • σ' (f m)) = (s₁ : B) • f m := by
      have := (p'.restrictScalars B).map_smul (s₁ : B) (σ' (f m))
      rw [LinearMap.coe_restrictScalars] at this
      rw [this, hpσ]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e1, e2, e3, LinearMap.comp_apply,
      LinearMap.smul_apply, LinearMap.id_apply, Submonoid.smul_def, map_smul, Submonoid.coe_mul,
      mul_smul]
  obtain ⟨s₃, hs₃⟩ :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule (Submonoid.powers b) f _ _ key
  obtain ⟨k₁, hk₁⟩ := s₁.2
  obtain ⟨k₂, hk₂⟩ := s₂.2
  obtain ⟨k₃, hk₃⟩ := s₃.2
  dsimp only at hk₁ hk₂ hk₃
  refine ⟨k₃ + (k₂ + k₁), n, eB.toLinearMap ∘ₗ h, ((s₃ : B) • t) ∘ₗ eB.symm.toLinearMap, ?_⟩
  refine LinearMap.ext fun m => ?_
  have hm := LinearMap.congr_fun hs₃ m
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Submonoid.smul_def, Submonoid.smul_def, Submonoid.smul_def,
    Submonoid.coe_mul] at hm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, hm,
    ← hk₁, ← hk₂, ← hk₃, pow_add, pow_add, mul_smul, mul_smul, mul_smul]

theorem defect_bounded : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∃ c : ℕ, ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (a : B →ₐ[R] R'), Defect a π c := by
  intro R _ _ _ π _ B _ _ _ hsm
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  have : Algebra.FinitePresentation R B := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨c, n, s, t, hts⟩ := exists_pow_factor_free (S := Localization.Away (algebraMap R B π))
    (M' := Ω[Localization.Away (algebraMap R B π)⁄R]) (algebraMap R B π)
    (KaehlerDifferential.map R R B (Localization.Away (algebraMap R B π)))
  refine ⟨c, fun R' _ _ _ a => ?_⟩
  letI := a.toRingHom.toAlgebra
  intro w hw
  obtain ⟨⟨r, hr⟩, hrw⟩ := hw
  have hsw : s.baseChange R' w = 0 := by
    have h0 : r • s.baseChange R' w = 0 := by
      have hrw' : r • w = 0 := hrw
      rw [← LinearMap.map_smul, hrw', map_zero]
    exact (smul_eq_zero.mp h0).resolve_left (nonZeroDivisors.ne_zero hr)
  have hcomp : (t.baseChange R') (s.baseChange R' w) = (algebraMap R B π ^ c) • w := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hts, LinearMap.baseChange_smul,
      LinearMap.baseChange_id, LinearMap.smul_apply, LinearMap.id_apply]
  rw [hsw, map_zero] at hcomp
  have hπ : algebraMap R R' π = algebraMap B R' (algebraMap R B π) := (a.commutes π).symm
  rw [hπ, ← map_pow, algebraMap_smul, ← hcomp]

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValHomEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ImmSep
open GlobalTheory.ZH.CrdCalc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem eq_of_valHom_eq (x x' : Sp R ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ x' ⁻¹ᵁ U) (e : valHom x U h = valHom x' U h') : x = x' := by
  have e₁ : x.appLE U ⊤ h = x'.appLE U ⊤ h' := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of R)).hom]
    exact CommRingCat.hom_ext e
  have a := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top (Sp R)) h
  have a' := IsAffineOpen.SpecMap_appLE_fromSpec x' hU (isAffineOpen_top (Sp R)) h'
  rw [e₁, a', IsAffineOpen.fromSpec_top] at a
  exact ((cancel_epi _).1 a).symm

theorem valHom_constFn {k : Type} [CommRing k] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) :
    valHom x U h (constFn p U a) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (((x ≫ p).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a)) := by
  rw [← Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ le_top h]
  rfl

theorem eq_of_crd_eq : (∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (H : LB X) (J : Type) (s : J → H.Sec) (J₀ : Set J), H.IsLB → ImmBy p H s J₀ → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x x' : Sp R ⟶ X) (v : J → R), x ≫ p = x' ≫ p → Crd H s x v → Crd H s x' v → x = x') := by
  intro k _ X p H J s J₀ _ hI R _ _ x x' v hp hx hx'
  have hm : x (IsLocalRing.closedPoint R) ∈ ⨆ i ∈ J₀, Out.nonzeroLocus (s i) := by
    rw [hI.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨hi₀, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have h := (top_le_iff x _).2 hi
  have hu : IsUnit (v i) := (crd_isUnit_iff i hx).2 h
  have h' := (crd_isUnit_iff i hx').1 hu
  obtain ⟨hA, r, hr, hc⟩ := hI.2 i hi₀
  refine eq_of_valHom_eq x x' _ hA h h' (RingHom.eq_of_eqOn_set_dense hc ?_)
  rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
  · rw [valHom_constFn, valHom_constFn]
    simp only [hp]
  · have e := (crd_ratio hx (hr j) h).symm.trans (crd_ratio hx' (hr j) h')
    rw [valR_eq x _ h, valR_eq x' _ h'] at e
    exact hu.mul_right_cancel e

end GlobalTheory.ZH.ImmSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOneOfPowOfClosedPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.RedPts

variable {S : Scheme.{0}}

def precomp (G : Over S) [GrpObj G] {T T' : Over S} (u : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) where
  toFun x := u ≫ x
  map_one' := MonObj.comp_one u
  map_mul' x y := MonObj.comp_mul u x y

def diagSec {T : Scheme.{0}} (p : T ⟶ S) : 𝟙_ (Over T) ⟶ (Over.pullback p).obj (Over.mk p) :=
  Over.homMk (pullback.lift (𝟙 T) (𝟙 T) rfl) (pullback.lift_snd _ _ _)

def toSec (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    (Over.mk p ⟶ G) →* (𝟙_ (Over T) ⟶ (Over.pullback p).obj G) :=
  (precomp _ (diagSec p)).comp (Over.pullback p).homMonoidHom

theorem toSec_left_fst (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) (x : Over.mk p ⟶ G) :
    (toSec G p x).left ≫ pullback.fst G.hom p = x.left := by
  have h₁ : ((Over.pullback p).map x).left ≫ pullback.fst G.hom p = pullback.fst p p ≫ x.left :=
    pullback.lift_fst _ _ _
  have h₂ : (diagSec p).left ≫ pullback.fst p p = 𝟙 T := pullback.lift_fst _ _ _
  change ((diagSec p).left ≫ ((Over.pullback p).map x).left) ≫ _ = _
  rw [Category.assoc, h₁]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ x.left) h₂)).trans (Category.id_comp _)

theorem toSec_injective (G : Over S) [GrpObj G] {T : Scheme.{0}} (p : T ⟶ S) :
    Function.Injective (toSec G p) := fun x y h =>
  Over.OverMorphism.ext (by rw [← toSec_left_fst, h, toSec_left_fst])

theorem eq_one_of_pow_of_closedPoint (G : Over S) [GrpObj G] [IsCommMonObj G]
    [LocallyOfFiniteType G.hom] {R : Type} [CommRing R] [IsLocalRing R] (p : Sp R ⟶ S) {n : ℕ}
    (hn : IsUnit (n : R)) (x : Over.mk p ⟶ G) (hx : x ^ n = 1) {Z : Over S} (j : Z ⟶ Over.mk p)
    (hj : IsLocalRing.closedPoint R ∈ Set.range (show Z.left ⟶ Sp R from j.left)) (h : j ≫ x = 1) :
    x = 1 := by
  apply toSec_injective G p
  have hn' : IsUnit (n : Γ(Sp R, ⊤)) := by simpa using hn.map (Scheme.ΓSpecIso (.of R)).inv.hom
  let G' := (Over.pullback p).obj G
  have : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom p))
  have := GlobalTheory.GrpTangent.formallyUnramified_mulN G' hn'
  have : LocallyOfFiniteType ((mulN G' n).left ≫ G'.hom) := by rw [Over.w]; infer_instance
  have := locallyOfFiniteType_of_comp (mulN G' n).left G'.hom
  refine Over.OverMorphism.ext (GlobalTheory.eq_of_isLocalRing_of_unramified (R := .of R) (mulN G' n).left
    (a := (toSec G p x).left) (b := (toSec G p 1).left) ?_ (show Z.left ⟶ Sp R from j.left) hj ?_)
  · have e : toSec G p x ≫ mulN G' n = toSec G p 1 ≫ mulN G' n := by
      rw [GlobalTheory.GrpTangent.comp_mulN, GlobalTheory.GrpTangent.comp_mulN, ← map_pow, ← map_pow, hx, one_pow]
    exact congrArg Over.Hom.left e
  · refine pullback.hom_ext ?_ ?_
    · have e : j ≫ x = j ≫ 1 := by rw [h, MonObj.comp_one]
      exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p x))).trans
        ((congrArg Over.Hom.left e).trans
          ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·) (toSec_left_fst G p 1))).symm)
    · exact ((Category.assoc _ _ _).trans (congrArg (j.left ≫ ·)
        ((Over.w (toSec G p x)).trans (Over.w (toSec G p 1)).symm))).trans (Category.assoc _ _ _).symm

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_reduction : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∃ (H : Subgroup (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (r : H →* (𝟙_ (Over (Sp (IsLocalRing.ResidueField R))) ⟶ (Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G)), (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = x.left) ∧ (∀ (x : H) (s : Sp R ⟶ G.left), s ≫ G.hom = spMap (algebraMap W R) → spMap (algebraMap R Ω) ≫ s = x.1.left → (r x).left ≫ pullback.fst G.hom _ = spMap (IsLocalRing.residue R) ≫ s) ∧ ∀ (n : ℕ) (x : H), IsUnit (n : R) → x ^ n = 1 → r x = 1 → x = 1 := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hj G _ hG
  obtain ⟨hc, hsm, hsep, -, -⟩ := hG
  let u : Over.mk (spMap (algebraMap W Ω)) ⟶ Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (algebraMap R Ω))
      ((spMap_comp _ _).trans (congrArg spMap (IsScalarTower.algebraMap_eq W R Ω).symm))
  let v : Over.mk (spMap ((IsLocalRing.residue R).comp (algebraMap W R))) ⟶
      Over.mk (spMap (algebraMap W R)) :=
    Over.homMk (spMap (IsLocalRing.residue R)) (spMap_comp _ _)
  have hdom : IsDominant (spMap (algebraMap R Ω)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R Ω) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hj]; exact bot_le)⟩
  have hu : Function.Injective (precomp G u) := fun a b h => Over.OverMorphism.ext
    (ext_of_isDominant_of_isSeparated (X := Sp R) G.hom ((Over.w a).trans (Over.w b).symm)
      (spMap (algebraMap R Ω)) (congrArg Over.Hom.left h))
  let e := MonoidHom.ofInjective hu
  refine ⟨(precomp G u).range, ((toSec G _).comp (precomp G v)).comp e.symm.toMonoidHom,
    fun x => ⟨?_, ?_⟩, fun x s hs hx => ?_, fun n x hn hx hr => ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.left, Over.w s, rfl⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨Over.homMk s hs, Over.OverMorphism.ext hx⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    obtain rfl : y = Over.homMk s hs := hu (Over.OverMorphism.ext hx.symm)
    change (toSec G _ (precomp G v (e.symm (e _)))).left ≫ _ = _
    rw [e.symm_apply_apply, toSec_left_fst]
    rfl
  · obtain ⟨y, rfl⟩ := e.surjective x
    change toSec G _ (precomp G v (e.symm (e _))) = _ at hr
    rw [e.symm_apply_apply, map_eq_one_iff _ (toSec_injective G _)] at hr
    rw [← map_pow, map_eq_one_iff _ e.injective] at hx
    rw [eq_one_of_pow_of_closedPoint G _ hn y hx v
      ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩ hr, map_one]

end GlobalTheory.RedPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem residue_embedding_unique {X : Scheme.{0}} {Ω : CommRingCat.{0}} [Nonempty (Spec Ω)]
    {p q : X} (φ : X.residueField p ⟶ Ω) (ψ : X.residueField q ⟶ Ω)
    (h : Spec.map φ ≫ X.fromSpecResidueField p = Spec.map ψ ≫ X.fromSpecResidueField q) :
    ∃ e : p = q, φ = (X.residueFieldCongr e).hom ≫ ψ := by
  obtain ⟨t⟩ := ‹Nonempty (Spec Ω)›
  have e : p = q := by
    have := congrArg (fun f => f t) h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using this
  subst e
  refine ⟨rfl, ?_⟩
  rw [cancel_mono, Spec.map_inj] at h
  simpa using h

theorem essFiniteType_residueField_of_locallyOfFiniteType {X : Scheme.{0}} {R : CommRingCat.{0}}
    (s : X ⟶ Spec R) [LocallyOfFiniteType s] (p : X) (ψ : R ⟶ X.residueField p)
    (h : Spec.map ψ = X.fromSpecResidueField p ≫ s) : ψ.hom.EssFiniteType := by
  haveI : (s p).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  have e : ψ = CommRingCat.ofHom (algebraMap R (s p).asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R (s p)).inv ≫ s.residueFieldMap p := by
    rw [← Spec.map_inj, h, Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [e]
  refine .comp (RingHom.essFiniteType_algebraMap.mpr inferInstance) (.comp
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.Spec.residueFieldIso R (s p)).inv).2).essFiniteType
    (RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap s p)))

theorem exists_fieldOfValues : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (x : Sp Ω ⟶ X), ∃ E : Subfield Ω, (∀ τ τ' : Ω →+* Ω, spMap τ ≫ x = spMap τ' ≫ x ↔ ∀ c ∈ E, τ c = τ' c) ∧ (∀ (K' : Type) [Field K'] (j : K' →+* Ω), E ≤ j.fieldRange ↔ ∃ y : Sp K' ⟶ X, spMap j ≫ y = x) ∧ ∀ (K : Type) [Field K] [Algebra K Ω] (s : X ⟶ Sp K), LocallyOfFiniteType s → x ≫ s = spMap (algebraMap K Ω) → Algebra.IsAlgebraic K Ω → ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ L.toSubfield = E := by
  intro X Ω _ x
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω X).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  subst hx
  let f : X.residueField p →+* Ω := φ.hom
  refine ⟨f.fieldRange, fun τ τ' => ?_, fun K' _ j => ⟨fun h => ?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp,
      Spec.map_inj]
    constructor
    · rintro h _ ⟨c, rfl⟩
      exact congrArg (fun g => g.hom c) h
    · intro h
      ext c
      exact h _ ⟨c, rfl⟩
  · let e : K' ≃+* j.fieldRange := j.rangeRestrictFieldEquiv
    let g : X.residueField p →+* K' :=
      e.symm.toRingHom.comp (f.codRestrict j.fieldRange fun c => h ⟨c, rfl⟩)
    refine ⟨Spec.map (CommRingCat.ofHom g) ≫ X.fromSpecResidueField p, ?_⟩
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f c, h ⟨c, rfl⟩⟩)
  · rintro ⟨y, hy⟩
    obtain ⟨⟨q, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K' X).symm.surjective y
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hy
    rw [← Category.assoc, ← Spec.map_comp] at hy
    obtain ⟨e, he⟩ := residue_embedding_unique _ _ hy.symm
    rintro _ ⟨c, rfl⟩
    exact ⟨ψ.hom ((X.residueFieldCongr e).hom.hom c), (congrArg (fun g => g.hom c) he).symm⟩
  · intro K _ _ s hs hxs halg
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.fromSpecResidueField p ≫ s)
    have hess := essFiniteType_residueField_of_locallyOfFiniteType s p ψ hψ
    rw [Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
    letI : Algebra K (X.residueField p) := ψ.hom.toAlgebra
    let fa : X.residueField p →ₐ[K] Ω :=
      { f with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
    haveI : Algebra.EssFiniteType K (X.residueField p) := hess
    haveI : Algebra.IsAlgebraic K (X.residueField p) :=
      Algebra.IsAlgebraic.of_injective fa f.injective
    haveI : Module.Finite K (X.residueField p) := Algebra.finite_of_essFiniteType_of_isAlgebraic
    refine ⟨fa.fieldRange, ?_, rfl⟩
    exact Module.Finite.equiv (AlgEquiv.ofInjectiveField fa).toLinearEquiv

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralExtIsAlgClosedResidueFieldStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_ext_isAlgClosed_residueField' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by
  first | exact @GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField | exact GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField | (intros; apply GlobalTheory.ClosedResidueExt.exists_integral_ext_isAlgClosed_residueField <;> assumption)
end

