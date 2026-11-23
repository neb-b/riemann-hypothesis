module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0136
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsDualBaseChange
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.DualBaseChange

theorem dual_isBaseChange {R : Type} [CommRing R] {A : Type} [Field A] [Algebra R A]
    [IsFractionRing R A] {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Projective R V] {W : Type} [AddCommGroup W] [Module R W] [Module A W]
    [IsScalarTower R A W] {j : V →ₗ[R] W} (hb : IsBaseChange A j) :
    IsBaseChange A hb.toDual := by
  have : Module.FinitePresentation R V := Module.finitePresentation_of_projective R V
  rw [← isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) A]
  refine ⟨(isLocalizedModule_id (nonZeroDivisors R) (Module.Dual A W) A).map_units, ?_, ?_⟩
  · intro φ
    obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
      (nonZeroDivisors R) (Algebra.linearMap R A) ((φ.restrictScalars R) ∘ₗ j)
    refine ⟨(h, s), ?_⟩
    apply hb.algHom_ext
    intro v
    have := LinearMap.congr_fun hs v
    rw [hb.toDual_comp_apply]
    exact this.symm
  · intro u₁ u₂ h
    refine ⟨1, ?_⟩
    congr 1
    ext v
    apply IsFractionRing.injective R A
    rw [← hb.toDual_comp_apply, ← hb.toDual_comp_apply, h]

end PositivityTheory.Xgn.DualBaseChange

theorem PositivityTheory.Xgn.exists_dual_base_change : ∀ (Ω : Type) [Field Ω] (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsFractionRing R Ω] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (Li : Type) [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li), IsBaseChange Ω toLi → ∃ j : Module.Dual R L →ₗ[R] Module.Dual Ω Li, IsBaseChange Ω j ∧ ∀ u v, j u (toLi v) = algebraMap R Ω (u v) := by
  intro Ω _ O _ _ R _ L _ _ _ _ Li _ _ toLi hb
  exact ⟨hb.toDual, PositivityTheory.Xgn.DualBaseChange.dual_isBaseChange hb,
    fun u v => hb.toDual_comp_apply u v⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsTorsionGroupExtension
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.TorsionGroupExtension

theorem epi_spec {K k : Type} [Field K] [Field k] (i : K →+* k) :
    Epi (Spec.map (CommRingCat.ofHom i)) := by
  have h1 : Flat (Spec.map (CommRingCat.ofHom i)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := i.toAlgebra
    exact (inferInstance : Module.Flat K k)
  have h2 : Surjective (Spec.map (CommRingCat.ofHom i)) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint k, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

noncomputable def pre {X : Scheme.{0}} {A B : Over X} (u : A ⟶ B) (G : Over X) [GrpObj G] :
    (B ⟶ G) →* (A ⟶ G) where
  toFun g := u ≫ g
  map_one' := MonObj.comp_one u
  map_mul' g h := MonObj.comp_mul u g h

theorem pre_inj {X : Scheme.{0}} {A B : Over X} (u : A ⟶ B) (hu : Epi u.left) (G : Over X) [GrpObj G] :
    Function.Injective (pre u G) := fun g h e => by
  apply Over.OverMorphism.ext
  rw [← cancel_epi u.left]
  exact congrArg (fun m : A ⟶ G => m.left) e

theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp, CommRingCat.ofHom_comp]

end PositivityTheory.Xgn.TorsionGroupExtension

open PositivityTheory.Xgn.TorsionGroupExtension in
theorem PositivityTheory.Xgn.exists_torsion_group_extension : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [CharZero R'] (Ω : Type) [Field Ω] [Algebra R' Ω] [IsFractionRing R' Ω] (T : Type) [CommGroup T] (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (x' : Spec (CommRingCat.of R') ⟶ X) (ξ : Spec (CommRingCat.of Ω) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap R' Ω)) ≫ x' = ξ → ∀ N : ℕ, 1 ≤ N → ∀ pt : T →* (Over.mk ξ ⟶ G), Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → FullTorsion G ξ N → ∃ (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G x' N i' ∧ ∀ (a : FractionRing R' →+* Ω), a.comp (algebraMap R' (FractionRing R')) = algebraMap R' Ω → ∀ t, (pt t).left = Spec.map (CommRingCat.ofHom a) ≫ (Γ'.pt t).left ≫ i' := by
  intro R' _ _ _ _ Ω _ _ _ T _ X G _ hG x' ξ hξ N hN pt hinj htor hfull
  let e : FractionRing R' ≃+* Ω := (FractionRing.algEquiv R' Ω).toRingEquiv
  let b : Ω →+* FractionRing R' := e.symm.toRingHom
  let c : FractionRing R' →+* Ω := e.toRingHom
  have hc : c.comp (algebraMap R' (FractionRing R')) = algebraMap R' Ω :=
    RingHom.ext fun r => (FractionRing.algEquiv R' Ω).commutes r
  have hb : b.comp (algebraMap R' Ω) = algebraMap R' (FractionRing R') :=
    RingHom.ext fun r => (FractionRing.algEquiv R' Ω).symm.commutes r
  have hcb : c.comp b = RingHom.id Ω := RingHom.ext fun r => e.apply_symm_apply r
  have hu : Spec.map (CommRingCat.ofHom b) ≫ ξ =
      Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) ≫ x' := by
    rw [← hξ, ← Category.assoc, spec_comp, hb]
  let u : Over.mk ((BT.genPt R').hom ≫ x') ⟶ Over.mk ξ :=
    Over.homMk (Spec.map (CommRingCat.ofHom b)) hu
  let τ : T →* (Over.mk ((BT.genPt R').hom ≫ x') ⟶ G) := (pre u G).comp pt
  have hτ : ∀ t, (τ t).left = Spec.map (CommRingCat.ofHom b) ≫ (pt t).left := fun t => rfl
  obtain ⟨Γ, i, h1, h2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion R' T X G hG x' N hN τ
    ((pre_inj u (epi_spec b) G).comp hinj)
    (fun t => by
      change pre u G (pt t) ^ N = 1
      rw [← map_pow, (htor _).2 ⟨t, rfl⟩, map_one])
    (fun k _ _ a g hg => by
      have hv : spMap (a.comp b) ≫ ξ =
          Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt R').hom ≫ x' := by
        change Spec.map (CommRingCat.ofHom (a.comp b)) ≫ ξ = Spec.map (CommRingCat.ofHom a) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) ≫ x'
        rw [← hu, ← Category.assoc, spec_comp]
      let v : Over.mk (spMap (a.comp b) ≫ ξ) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (BT.genPt R').hom ≫ x') :=
        Over.homMk (𝟙 _) (by simpa using hv.symm)
      have hg' : (pre v G g) ^ N = 1 := by rw [← map_pow, hg, map_one]
      obtain ⟨x, hx⟩ := hfull k (a.comp b) (pre v G g) hg'
      let w : Over.mk (spMap (a.comp b) ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap (a.comp b)) rfl
      have hxw : pre w G x = pre v G g := Over.OverMorphism.ext hx.symm
      have hxN : x ^ N = 1 := by
        apply pre_inj w (epi_spec (a.comp b)) G
        rw [map_pow, map_one, hxw, hg']
      obtain ⟨t, rfl⟩ := (htor x).1 hxN
      refine ⟨t, ?_⟩
      have hx' : g.left = Spec.map (CommRingCat.ofHom (a.comp b)) ≫ (pt t).left :=
        (Category.id_comp _).symm.trans hx
      rw [hx', ← spec_comp, Category.assoc]
      rfl)
  refine ⟨Γ, i, h1, fun a ha t => ?_⟩
  have hac : a = c := IsLocalization.ringHom_ext (nonZeroDivisors R') (ha.trans hc.symm)
  have h3 : (Γ.pt t).left ≫ i = Spec.map (CommRingCat.ofHom b) ≫ (pt t).left := h2 t
  have h4 : Spec.map (CommRingCat.ofHom c) ≫ Spec.map (CommRingCat.ofHom b) ≫ (pt t).left = (pt t).left := by
    rw [← Category.assoc, spec_comp, hcb]
    erw [Spec.map_id]
    exact Category.id_comp _
  rw [hac]
  exact h4.symm.trans (congrArg (fun m => Spec.map (CommRingCat.ofHom c) ≫ m) h3.symm)
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.FullTorsionPacking
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.FullTorsionPacking

noncomputable def preHom {X : Scheme.{0}} (G : Over X) [GrpObj G] {A B : Over X} (u : A ⟶ B) :
    (B ⟶ G) →* (A ⟶ G) where
  toFun g := u ≫ g
  map_one' := MonObj.comp_one u
  map_mul' g h := MonObj.comp_mul u g h

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sp_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  rw [← Spec.map_id]; rfl

theorem isDominant_spMap {A B : Type} [Field A] [Field B] (i : A →+* B) : IsDominant (spMap i) := by
  refine ⟨Function.Surjective.denseRange fun y => ?_⟩
  haveI : Subsingleton (Spec (CommRingCat.of A)) := inferInstanceAs (Subsingleton (PrimeSpectrum A))
  exact ⟨(default : PrimeSpectrum B), Subsingleton.elim _ _⟩

theorem exists_inv {Ω : Type} [Field Ω] {O : Type} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω)
    [IsFractionRing R Ω] : ∃ e' : Ω →+* FractionRing R, (fracToField R).comp e' = RingHom.id Ω ∧
      e'.comp (algebraMap R Ω) = algebraMap R (FractionRing R) := by
  have h : fracToField R = (FractionRing.algEquiv R Ω : FractionRing R →+* Ω) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    have h1 : fracToField R (algebraMap R (FractionRing R) r) = algebraMap R Ω r :=
      IsFractionRing.lift_algebraMap _ r
    exact h1.trans ((FractionRing.algEquiv R Ω).commutes r).symm
  refine ⟨((FractionRing.algEquiv R Ω).symm : Ω →+* FractionRing R), ?_, ?_⟩
  · rw [h]; ext z; simp
  · ext r
    exact (FractionRing.algEquiv R Ω).symm.commutes r

end PositivityTheory.Xgn.FullTorsionPacking

open PositivityTheory.Xgn.FullTorsionPacking in
theorem PositivityTheory.Xgn.full_torsion_packing : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) [IsNoetherianRing R] [CharZero R] [IsFractionRing R Ω] (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∀ (T : Type) [CommGroup T] (pt : T →* (Over.mk ξ ⟶ G)) (N n : ℕ), 1 ≤ N → N ∣ n → FullTorsion G ξ n → Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → ∃ (Γ : QFGroup R T) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i ∧ ∀ t, (pt t).left = spMap (fracToField R) ≫ (Γ.pt t).left ≫ i := by
  intro X G _ hG Ω _ ξ O _ _ R _ _ _ x hx T _ pt N n hN hNn hFT hinj honto
  obtain ⟨e', he, he'⟩ := exists_inv R
  have hu : spMap e' ≫ ξ = (genPt R).hom ≫ x := by
    have h0 : spMap e' ≫ spMap (algebraMap R Ω) = spMap (algebraMap R (FractionRing R)) := by
      rw [sp_comp, he']
    subst hx
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) h0)
  have hee : spMap (fracToField R) ≫ spMap e' = 𝟙 _ := by
    rw [sp_comp, he, sp_id]
  let u : Over.mk ((genPt R).hom ≫ x) ⟶ Over.mk ξ := Over.homMk (spMap e') hu
  let τ : T →* (Over.mk ((genPt R).hom ≫ x) ⟶ G) := (preHom G u).comp pt
  have hτ : ∀ t, (τ t).left = spMap e' ≫ (pt t).left := fun t => rfl
  have hpt : ∀ t, (pt t).left = spMap (fracToField R) ≫ (τ t).left := fun t => by
    rw [hτ, ← Category.assoc, hee]
    exact (Category.id_comp _).symm
  have hτinj : Function.Injective τ := fun s t h => by
    apply hinj
    ext1
    rw [hpt, hpt, h]
  have hτN : ∀ t, τ t ^ N = 1 := fun t => by
    change preHom G u (pt t) ^ N = 1
    rw [← map_pow, (honto _).2 ⟨t, rfl⟩, map_one]
  obtain ⟨Γ, i, hΓ, hi⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.exists_qfGroup_torsion R T X G hG x N hN τ hτinj hτN (by
    intro Ω' _ _ a g hg
    have hw : spMap (a.comp e') ≫ ξ = Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x := by
      have h0 : spMap (a.comp e') ≫ ξ = spMap a ≫ spMap e' ≫ ξ := by
        rw [← sp_comp, Category.assoc]
      exact h0.trans (congrArg (spMap a ≫ ·) hu)
    let w : Over.mk (spMap (a.comp e') ≫ ξ) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom a) ≫ (genPt R).hom ≫ x) :=
      Over.homMk (𝟙 _) ((Category.id_comp _).trans hw.symm)
    have hgN : preHom G w g ^ N = 1 := by rw [← map_pow, hg, map_one]
    have hgn : preHom G w g ^ n = 1 := by
      obtain ⟨m, rfl⟩ := hNn
      rw [pow_mul, hgN, one_pow]
    obtain ⟨x₀, hx₀⟩ := hFT Ω' (a.comp e') _ hgn
    let v : Over.mk (spMap (a.comp e') ≫ ξ) ⟶ Over.mk ξ := Over.homMk (spMap (a.comp e')) rfl
    have hv : preHom G v x₀ = preHom G w g := by
      ext1
      exact hx₀.symm
    have h1 : preHom G v (x₀ ^ N) = preHom G v 1 := by
      rw [map_pow, hv, hgN, map_one]
    have h2 : x₀ ^ N = 1 := by
      haveI := hG.separated
      haveI := isDominant_spMap (a.comp e')
      haveI : IsReduced (Over.mk ξ).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of Ω)))
      ext1
      refine ext_of_isDominant_of_isSeparated G.hom ?_ (spMap (a.comp e')) ?_
      · rw [Over.w, Over.w]
      · exact congrArg CommaMorphism.left h1
    obtain ⟨t, rfl⟩ := (honto _).1 h2
    refine ⟨t, ?_⟩
    have h3 : (preHom G w g).left = g.left := Category.id_comp _
    have h4 : ∀ q : Spec (CommRingCat.of Ω) ⟶ G.left, spMap (a.comp e') ≫ q = spMap a ≫ spMap e' ≫ q := fun q => by
      rw [← sp_comp, Category.assoc]
    exact h3.symm.trans (hx₀.trans (h4 _)))
  exact ⟨Γ, i, hΓ, fun t => (hpt t).trans (congrArg (spMap (fracToField R) ≫ ·) (hi t).symm)⟩
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsIntegrallyClosedOfDenom
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.PackingFacts

def zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb (h ▸ dvd_zero p))
    have hb0' : (b' : Ω) ≠ 0 := Nat.cast_ne_zero.2 (fun h => hb' (h ▸ dvd_zero p))
    refine ⟨a * b' + b * a', b * b', (Fact.out : p.Prime).not_dvd_mul hb hb', ?_⟩
    rw [div_add_div _ _ hb0 hb0']
    push_cast
    ring
  one_mem' := ⟨1, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  zero_mem' := ⟨0, 1, (Fact.out : p.Prime).not_dvd_one, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; rw [neg_div]⟩

theorem mem_range_zp (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [Fact p.Prime] (x : Ω) :
    x ∈ (algebraMap (zp Ω p) Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact z.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem mem_adjoin_of_range_le {o o' : Type} [CommRing o] [CommRing o'] {Ω : Type} [Field Ω] [Algebra o Ω]
    [Algebra o' Ω] (hr : ∀ a : o, algebraMap o Ω a ∈ (algebraMap o' Ω).range) (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin o T) : w ∈ Algebra.adjoin o' T := by
  induction hw using Algebra.adjoin_induction with
  | mem w hw => exact Algebra.subset_adjoin hw
  | algebraMap r =>
    obtain ⟨a, ha⟩ := hr r
    rw [← ha]
    exact Subalgebra.algebraMap_mem _ a
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem mem_adjoin_of_int (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] (T : Set Ω)
    {w : Ω} (hw : w ∈ Algebra.adjoin ℤ T) : w ∈ Algebra.adjoin o T :=
  mem_adjoin_of_range_le (o := ℤ) (o' := o) (fun n : ℤ => ⟨((n : ℤ) : o), by rw [map_intCast, eq_intCast]⟩) T hw

theorem isUnit_natCast {A O : Type} [CommRing A] [CommRing O] [Algebra A O]
    (m : Ideal A) [m.IsPrime] [IsLocalization.AtPrime O m] (p : ℕ) [Fact p.Prime] (hpm : (p : A) ∈ m) (b : ℕ)
    (hb : ¬ p ∣ b) : IsUnit (b : O) := by
  have hbm : (b : A) ∉ m := by
    intro hbm
    have hcop : IsCoprime (b : ℤ) (p : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hb).symm
    obtain ⟨u, v, huv⟩ := hcop.map (Int.castRingHom A)
    have h1 : (1 : A) ∈ m := by
      rw [← huv]
      simp only [eq_intCast, Int.cast_natCast]
      exact add_mem (m.mul_mem_left _ hbm) (m.mul_mem_left _ hpm)
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 h1)
  have := IsLocalization.map_units O (⟨(b : A), hbm⟩ : m.primeCompl)
  simpa using this

theorem exists_denom {o A O Ω : Type} [CommRing o] [CommRing A] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra A Ω]
    [Algebra A O] [Algebra O Ω] [IsScalarTower A O Ω] (M : Submonoid A) [IsLocalization M O] (T : Set Ω)
    (hA : ∀ a : A, algebraMap A Ω a ∈ Algebra.adjoin o T) {w : Ω} (hw : w ∈ Algebra.adjoin O T) :
    ∃ s : M, w * algebraMap A Ω s ∈ Algebra.adjoin o T := by
  induction hw using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj M r
    refine ⟨s, ?_⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, e, ← IsScalarTower.algebraMap_apply]
    exact hA _
  | add x y _ _ hx hy =>
    obtain ⟨b, hx⟩ := hx
    obtain ⟨b', hy⟩ := hy
    refine ⟨b * b', ?_⟩
    have : (x + y) * algebraMap A Ω ((b * b' : M) : A) =
        x * algebraMap A Ω b * algebraMap A Ω b' + y * algebraMap A Ω b' * algebraMap A Ω b := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact add_mem (mul_mem hx (hA _)) (mul_mem hy (hA _))
  | mul x y _ _ hx hy =>
    obtain ⟨b, hx⟩ := hx
    obtain ⟨b', hy⟩ := hy
    refine ⟨b * b', ?_⟩
    have : (x * y) * algebraMap A Ω ((b * b' : M) : A) = x * algebraMap A Ω b * (y * algebraMap A Ω b') := by
      rw [Submonoid.coe_mul, map_mul]; ring
    rw [this]
    exact mul_mem hx hy

theorem isIntegrallyClosed_of_denom {o O Ω : Type} [CommRing o] [CommRing O] [Field Ω] [Algebra o Ω] [Algebra O Ω]
    (B : Subalgebra o Ω) (B' : Subalgebra O Ω) [IsIntegrallyClosed B] (hle : ∀ w ∈ B, w ∈ B')
    (hden : ∀ w ∈ B', ∃ s ∈ B, (∃ t ∈ B', s * t = 1) ∧ w * s ∈ B) : IsIntegrallyClosed B' := by
  let ψ : B →+* B' := (algebraMap B Ω).codRestrict _ fun s => hle _ s.2
  letI : Algebra B B' := ψ.toAlgebra
  let M : Submonoid B := (IsUnit.submonoid B').comap ψ
  haveI hloc : IsLocalization M B' := by
    refine ⟨fun s => s.2, fun a => ?_, fun {r s} h => ⟨1, ?_⟩⟩
    · obtain ⟨s, hs, ⟨t, ht, e⟩, hws⟩ := hden a a.2
      have hu : IsUnit (ψ ⟨s, hs⟩) := IsUnit.of_mul_eq_one (⟨t, ht⟩ : B') (Subtype.ext e)
      exact ⟨⟨⟨_, hws⟩, ⟨⟨s, hs⟩, hu⟩⟩, Subtype.ext rfl⟩
    · have h' : (r : Ω) = s := congrArg (fun z : B' => (z : Ω)) h
      rw [Subtype.ext h']
  have hM : M ≤ nonZeroDivisors B := by
    intro s hs
    refine mem_nonZeroDivisors_of_ne_zero fun h => ?_
    have hu : IsUnit (ψ s) := hs
    rw [h, map_zero] at hu
    exact not_isUnit_zero hu
  exact isIntegrallyClosed_of_isLocalization B' M hM

end PositivityTheory.Xgn.PackingFacts

open PositivityTheory.Xgn.PackingFacts in
theorem PositivityTheory.Xgn.torsion_packing_facts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c' : ∀ k, J k), mseg y c' ≠ 0 → CharZero Ω ∧ IsNoetherianRing (CR O y c') ∧ IsIntegrallyClosed (CR O y c') ∧ IsFractionRing (CR O y c') Ω ∧ ∃ x : Spec (CommRingCat.of (CR O y c')) ⟶ 𝔐.X, spMap (algebraMap (CR O y c') Ω) ≫ x = 𝔐.ξ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV p _ hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ c' hc'
  haveI hch : CharZero Ω := GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.charZero_of_isArithVar hV
  obtain ⟨-, -, -, -, -, -, hchart⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.hcpt_generic_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS (zp Ω p) (mem_range_zp Ω p)
  obtain ⟨-, hic, hfr, x₀, hx₀, -⟩ := hchart c' hc'
  obtain ⟨-, -, -, hconst, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.const_closure E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hV A
  have eO := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := O) y c' hc'
  have eo := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := zp Ω p) y c' hc'
  have eZ := PositivityTheory.HtPt.Hcptgen.chartRing_mseg (o := ℤ) y c' hc'
  have hr : ∀ a : zp Ω p, algebraMap (zp Ω p) Ω a ∈ (algebraMap O Ω).range := by
    intro a
    obtain ⟨a₁, b, hb, hab⟩ := (mem_range_zp Ω p _).1 ⟨a, rfl⟩
    have hu := isUnit_natCast (O := O) m p hpm b hb
    refine ⟨(a₁ : O) * ↑hu.unit⁻¹, ?_⟩
    rw [hab, map_mul, map_intCast, div_eq_mul_inv]
    congr 1
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_natCast (algebraMap O Ω) b, ← map_mul, hu.val_inv_mul, map_one]
  have hle : ∀ w ∈ chartRing (zp Ω p) (mseg y) c', w ∈ CR O y c' := by
    intro w hw
    exact eO.ge (mem_adjoin_of_range_le hr _ (eo.le hw))
  have hA : ∀ a : A, algebraMap A Ω a ∈
      Algebra.adjoin (zp Ω p) (Set.range fun j => mseg y j / mseg y c') := by
    intro a
    have h1 : algebraMap A Ω a ∈ chartRing ℤ (mseg y) c' := hconst c' hc' a
    rw [eZ] at h1
    exact mem_adjoin_of_int _ _ h1
  refine ⟨hch, ?_, ?_, ?_, ?_⟩
  · haveI : Algebra.FiniteType O (CR O y c') := by
      refine (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => mseg y j / mseg y c').toFinset, ?_⟩
      rw [Set.Finite.coe_toFinset]
      exact eO.symm
    exact Algebra.FiniteType.isNoetherianRing O _
  · refine isIntegrallyClosed_of_denom (chartRing (zp Ω p) (mseg y) c') (CR O y c') hle fun w hw => ?_
    obtain ⟨s, hs⟩ := exists_denom m.primeCompl _ hA (eO.le hw)
    have hu := IsLocalization.map_units O s
    refine ⟨algebraMap A Ω s, eo.ge (hA _), ⟨algebraMap O Ω ↑hu.unit⁻¹, Subalgebra.algebraMap_mem _ _, ?_⟩, eo.ge hs⟩
    rw [IsScalarTower.algebraMap_apply A O Ω, ← map_mul, hu.mul_val_inv, map_one]
  · refine IsFractionRing.of_field _ _ fun a => ?_
    obtain ⟨g, h, -, e⟩ := IsFractionRing.div_surjective (A := chartRing (zp Ω p) (mseg y) c') a
    exact ⟨⟨g, hle _ g.2⟩, ⟨h, hle _ h.2⟩, e.symm⟩
  · let ψ : chartRing (zp Ω p) (mseg y) c' →+* CR O y c' :=
      (algebraMap (chartRing (zp Ω p) (mseg y) c') Ω).codRestrict _ fun s => hle _ s.2
    refine ⟨spMap ψ ≫ x₀, ?_⟩
    have e : spMap (algebraMap (CR O y c') Ω) ≫ spMap ψ = spMap ((algebraMap (CR O y c') Ω).comp ψ) :=
      (Spec.map_comp _ _).symm
    rw [← Category.assoc, e]
    exact hx₀
end

