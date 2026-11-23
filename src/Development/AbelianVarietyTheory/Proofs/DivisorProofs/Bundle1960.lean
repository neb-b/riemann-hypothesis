module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEqOneComplex
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1915
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.EtaleDiv

open IsLocalRing

theorem formallyEtale_of_bijective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Bijective f) : f.FormallyEtale := by
  algebraize [f]
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)

theorem formallyEtale_of_comp_bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hg : Function.Bijective g) (h : (g.comp f).FormallyEtale) :
    f.FormallyEtale := by
  let e := RingEquiv.ofBijective g hg
  have : f = (e.symm : T →+* S).comp (g.comp f) := by
    ext x
    exact (e.symm_apply_apply (f x)).symm
  rw [this]
  exact h.comp (formallyEtale_of_bijective _ e.symm.bijective)

theorem formallyEtale_stalkMap {M W : Scheme.{0}} (f : M ⟶ W) (U : M.Opens)
    [Etale (U.ι ≫ f)] (w : U.toScheme) : (f.stalkMap (U.ι w)).hom.FormallyEtale := by
  have hu := FormallyUnramified.stalkMap (U.ι ≫ f) w
  have hs : ((U.ι ≫ f).stalkMap w).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp ((U.ι ≫ f).smoothLocus_eq_top.ge (Set.mem_univ w))
  have h : ((U.ι ≫ f).stalkMap w).hom.FormallyEtale := by
    algebraize [((U.ι ≫ f).stalkMap w).hom]
    exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hu, hs⟩
  have : IsIso (U.ι.stalkMap w) := inferInstance
  rw [Scheme.Hom.stalkMap_comp] at h
  exact formallyEtale_of_comp_bijective (f.stalkMap (U.ι w)).hom (U.ι.stalkMap w).hom
    (ConcreteCategory.bijective_of_isIso _) h

theorem strictMono_ι {M : Scheme.{0}} (U : M.Opens) : StrictMono U.ι := by
  have hi := U.ι.isOpenEmbedding.isInducing
  intro a b h
  refine lt_of_le_not_ge ?_ ?_
  · exact hi.specializes_iff.2 h.le
  · exact fun h' => h.not_ge (hi.specializes_iff.1 h')

theorem map_maximalIdeal_stalk {M W : Scheme.{0}} (f : M ⟶ W) [LocallyOfFiniteType f] (z : M)
    (h : (f.stalkMap z).hom.FormallyEtale) :
    (maximalIdeal (W.presheaf.stalk (f z))).map (f.stalkMap z).hom =
      maximalIdeal (M.presheaf.stalk z) := by
  have hft := LocallyOfFiniteType.stalkMap f z
  algebraize [(f.stalkMap z).hom]
  have : IsLocalHom (algebraMap (W.presheaf.stalk (f z)) (M.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  exact Algebra.FormallyUnramified.map_maximalIdeal

theorem log_ordFrac_map {K L : Type} [Field K] [Field L] (V : ValuationSubring K)
    (V' : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing V']
    (ρ : K →+* L) (ψ : V →+* V') (hψ : ∀ a, (ψ a : L) = ρ a) {t : V} (ht : Irreducible t)
    (ht' : Irreducible (ψ t)) {g : K} (hg : g ≠ 0) :
    WithZero.log (Ring.ordFrac V' (ρ g)) = WithZero.log (Ring.ordFrac V g) := by
  obtain ⟨m, u, rfl⟩ := exists_eq_unit_mul_zpow (F := K) ht hg
  have h1 := ordTop_vw_unit_mul_zpow (F := K) ht u m
  have h2 := ordTop_vw_unit_mul_zpow (F := L) ht' (Units.map ψ.toMonoidHom u) m
  have e : ρ (algebraMap V K u * algebraMap V K t ^ m) =
      algebraMap V' L (Units.map ψ.toMonoidHom u) * algebraMap V' L (ψ t) ^ m := by
    rw [map_mul, map_zpow₀]
    simp [hψ]
  rw [← e] at h2
  rw [ordTop_vw_of_ne_zero _ hg, WithTop.coe_inj] at h1
  rw [ordTop_vw_of_ne_zero _ ((map_ne_zero ρ).2 hg), WithTop.coe_inj] at h2
  rw [h1, h2]

theorem isFreeGen_formMap {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] {α : k →+* A}
    {β : k →+* B} {ρ : A →+* B} (hρ : ρ.FormallyEtale) (h : ρ.comp α = β) {D : ℕ}
    {ω : Forms α D} (hω : IsFreeGen A ω) : IsFreeGen B (TopForm.formMap D ρ h ω) := by
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq' h.symm
  haveI : Algebra.FormallyEtale A B := hρ
  exact hω.of_isBaseChange (isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k A B) D)

theorem maximalIdeal_eq_bot {X : Scheme.{0}} [IsIntegral X] {x : X} (h : Order.coheight x = 0) :
    maximalIdeal (X.presheaf.stalk x) = ⊥ := by
  have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h.le
  exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime ⊥).symm

theorem coheight_apply_eq_one {M W : Scheme.{0}} [IsIntegral W] (f : M ⟶ W) [LocallyOfFiniteType f]
    (U : M.Opens) [Etale (U.ι ≫ f)] (w : U.toScheme) (h1 : Order.coheight (U.ι w) = 1)
    (hB : maximalIdeal (M.presheaf.stalk (U.ι w)) ≠ ⊥) : Order.coheight (f (U.ι w)) = 1 := by
  have hle : Order.coheight w ≤ 1 :=
    h1 ▸ Order.coheight_le_coheight_apply_of_strictMono _ (strictMono_ι U) w
  have hle' := GlobalTheory.GenExtendNormal.coheight_apply_le_one (U.ι ≫ f) (Flat.generalizingMap _) w hle
  refine le_antisymm hle' ?_
  rw [Order.one_le_iff_ne_zero]
  intro h0
  apply hB
  rw [← map_maximalIdeal_stalk f _ (formallyEtale_stalkMap f U w), maximalIdeal_eq_bot h0,
    Ideal.map_bot]

theorem exists_isAt_ord_formOrd : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W]
    [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f]
    (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens),
    Etale (U.ι ≫ f) → ∀ z ∈ U, ∀ E' : DivOver (f ≫ p), E'.IsAt z →
    ∃ E : DivOver p, E.IsAt (f z) ∧
      (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧
      ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  intro M W _ _ _ _ p f _ n _ _ U hU z hz E' hE'
  haveI := hU
  obtain ⟨w, rfl⟩ : ∃ w : U.toScheme, U.ι w = z := ⟨⟨z, hz⟩, rfl⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  haveI := SmoothOfRelativeDimension.smooth n (f ≫ p)
  haveI : GlobalTheory.IsNormalScheme W := GlobalTheory.ModifSections.isNormalScheme_of_smooth p
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p
  haveI hB : IsDiscreteValuationRing (M.presheaf.stalk (U.ι w)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing hE'.equiv.symm
  have hφ := formallyEtale_stalkMap f U w
  have hmax := map_maximalIdeal_stalk f (U.ι w) hφ
  have hc := coheight_apply_eq_one f U w hE'.coheight_eq_one
    (IsDiscreteValuationRing.not_a_field _)
  obtain ⟨E, hE⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
  haveI hA : IsDiscreteValuationRing (W.presheaf.stalk (f (U.ι w))) :=
    GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hc
  let ψ : E.ring →+* E'.ring :=
    hE'.equiv.toRingHom.comp ((f.stalkMap (U.ι w)).hom.comp hE.equiv.symm.toRingHom)
  have hψ : ∀ a, (ψ a : M.functionField) = functionFieldMap f a := by
    intro a
    obtain ⟨b, rfl⟩ := hE.equiv.surjective a
    have e : ψ (hE.equiv b) = hE'.equiv (f.stalkMap (U.ι w) b) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact (functionFieldMap_algebraMap f (U.ι w) b).symm
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (W.presheaf.stalk (f (U.ι w)))
  have ht' : Irreducible (f.stalkMap (U.ι w) t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at ht ⊢
    rw [← hmax, ht, Ideal.map_span, Set.image_singleton]
  have htE : Irreducible (hE.equiv t) := ht.map hE.equiv
  have htE' : Irreducible (ψ (hE.equiv t)) := by
    have e : ψ (hE.equiv t) = hE'.equiv (f.stalkMap (U.ι w) t) := by
      simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    rw [e]
    exact ht'.map hE'.equiv
  have hord : ∀ g : W.functionFieldˣ,
      E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g := fun g =>
    log_ordFrac_map E.ring E'.ring (functionFieldMap f) ψ hψ htE htE' g.ne_zero
  refine ⟨E, hE, hord, fun η hη => ?_⟩
  have hn : topologicalKrullDim W = n := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨c, rfl⟩ := (E.isFreeGen_toRat hω).2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [h]; exact zero_smul _ _)
  have hconst : ψ.comp E.const = E'.const := RingHom.ext fun a => Subtype.ext
    ((hψ _).trans (RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a))
  have hψFE : ψ.FormallyEtale :=
    RingHom.FormallyEtale.comp (RingHom.FormallyEtale.comp
      (formallyEtale_of_bijective _ hE.equiv.symm.bijective) hφ)
      (formallyEtale_of_bijective _ hE'.equiv.bijective)
  have h3 : ((functionFieldMap f).comp E.ring.subtype).comp E.const = Cartier.constFn (f ≫ p) := by
    ext a
    exact RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p f) a
  have e1 : GlobalTheory.EtaleKlt.ratPull p f n (E.toRat n ω) =
      E'.toRat n (TopForm.formMap n ψ hconst ω) := by
    change TopForm.formMap n (functionFieldMap f) _ (TopForm.formMap n E.ring.subtype rfl ω) =
      TopForm.formMap n E'.ring.subtype rfl (TopForm.formMap n ψ hconst ω)
    exact (formMap_formMap E.ring.subtype (functionFieldMap f)
      ((functionFieldMap f).comp E.ring.subtype) rfl _ _ h3 ω).trans
      (formMap_formMap ψ E'.ring.subtype ((functionFieldMap f).comp E.ring.subtype)
        (RingHom.ext hψ) _ _ h3 ω).symm
  have h1 : E.formOrd (c • E.toRat n ω) = E.ord (Units.mk0 c hc0) :=
    DivOver.IsFormOrd.formOrd_eq hη ⟨ω, hω, Units.mk0 c hc0, rfl, rfl⟩
  have hη' : GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω) ≠ 0 := by
    have hfree := E'.isFreeGen_toRat (isFreeGen_formMap hψFE hconst hω)
    rw [map_smulₛₗ, e1]
    intro h0
    have := hfree.1 (a₁ := functionFieldMap f c) (a₂ := 0) (by simp only [h0, zero_smul])
    exact hc0 ((map_eq_zero _).1 this)
  have h2 : E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω)) =
      E'.ord (Units.map (functionFieldMap f).toMonoidHom (Units.mk0 c hc0)) :=
    DivOver.IsFormOrd.formOrd_eq hη' ⟨_, isFreeGen_formMap hψFE hconst hω, _,
      by rw [map_smulₛₗ, e1]; rfl, rfl⟩
  change E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n (c • E.toRat n ω)) =
    E.formOrd (c • E.toRat n ω)
  rw [h1, h2, hord]

end GlobalTheory.EtaleDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushEquivPolPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.FlatCM GlobalTheory.PointMap
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramAt

section Tate

variable {p : ℕ} {M : Type} [CommGroup M]

theorem lev_sum {J : Type} (s : Finset J) (t : J → Tate p M) (n : ℕ) :
    (∑ a ∈ s, t a).lev n = ∏ a ∈ s, (t a).lev n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, Tate.lev_add, ih]

theorem lev_nsmul (N : ℕ) (t : Tate p M) (n : ℕ) : (N • t).lev n = t.lev n ^ N := by
  induction N with
  | zero => simp
  | succ N ih => rw [succ_nsmul, Tate.lev_add, ih, pow_succ]

end Tate

section Algebraic

variable {R Ω C : Type} [CommRing R] [Field Ω] [Field C] (α : R →+* Ω) (κ : Ω →+* C) {β : R →+* C}
  (hβ : κ.comp α = β)

end Algebraic

theorem lamEq_polPull {S S' : Scheme.{0}} (s : S' ⟶ S) {X Y A B : Out.PolAV S} {f₁ : X.A ⟶ A.A} {f₂ : Y.A ⟶ A.A}
    {g₁ : X.A ⟶ B.A} {g₂ : Y.A ⟶ B.A} (h : LamEq A.L f₁ f₂ B.L g₁ g₂) :
    LamEq (X := (StrictPull.polPull X s).A) (Y := (StrictPull.polPull Y s).A) (StrictPull.polPull A s).L
      ((Over.pullback s).map f₁) ((Over.pullback s).map f₂)
      (StrictPull.polPull B s).L ((Over.pullback s).map g₁) ((Over.pullback s).map g₂) :=
  lamEq_baseChange _ _ s X.A Y.A A.A B.A _ _ (StrictPull.polPull A s).A (StrictPull.polPull B s).A
    (pullback.fst X.A.hom s) (pullback.fst Y.A.hom s) _ _ pullback.condition pullback.condition
    (isGrpPullback_pullback A.A s) (isGrpPullback_pullback B.A s) _ _ _ _ A.isLB B.isLB (StrictPull.polPull A s).isLB
    (StrictPull.polPull B s).isLB (PolBaseChange.lbIso_refl (StrictPull.polPull A s).isLB)
    (PolBaseChange.lbIso_refl (StrictPull.polPull B s).isLB) _ _ _ _ _ _ _ _ (pullback.lift_fst _ _ _)
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) h

theorem exists_pushEquiv₂ {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G']
    [GrpObj G''] {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ : G'.left ⟶ G.left} {φ' : G''.left ⟶ G'.left}
    (h' : IsGrpPullback G'' G' f' φ') (h : IsGrpPullback G' G f φ) (g : S'' ⟶ S) (hg : g = f' ≫ f) :
    ∃ e : ((Over.mk (𝟙 S'') : Over S'') ⟶ G'') ≃* (Over.mk g ⟶ G), ∀ x, (e x).left = x.left ≫ φ' ≫ φ := by
  obtain ⟨e₁, h₁⟩ := LiePull.exists_pushEquiv h' (Over.mk (𝟙 _)) f' (Category.id_comp _).symm
  obtain ⟨e₂, h₂⟩ := LiePull.exists_pushEquiv h (Over.mk f') g hg
  exact ⟨e₁.trans e₂, fun x => (h₂ _).trans ((congrArg (· ≫ _) (h₁ x)).trans (Category.assoc _ _ _))⟩

theorem exists_pushEquiv_polPull {S S' S'' : Scheme.{0}} (B : Out.PolAV S) (f : S' ⟶ S) (f' : S'' ⟶ S') (g : S'' ⟶ S)
    (hg : g = f' ≫ f) :
    ∃ e : ((Over.mk (𝟙 S'') : Over S'') ⟶ (StrictPull.polPull (StrictPull.polPull B f) f').A) ≃* (Over.mk g ⟶ B.A),
      ∀ x, (e x).left = x.left ≫ pullback.fst (StrictPull.polPull B f).A.hom f' ≫ pullback.fst B.A.hom f :=
  exists_pushEquiv₂ (G' := (StrictPull.polPull B f).A) (isGrpPullback_pullback (StrictPull.polPull B f).A f')
    (isGrpPullback_pullback B.A f) g hg

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type}
  [CommRing R] (j : R →+* O) {B B' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ)

def toBase : (goodPoint hv ε j B o).A.A.left ⟶ B.A.left :=
  (goodPoint hv ε j B o).gen ≫ pullback.fst B.A.hom (spMap j)

theorem homC_toBase (f : B.A ⟶ B'.A) :
    (homC hv ε j o o' f).left ≫ toBase hv ε j o' = toBase hv ε j o ≫ f.left := by
  have h2 : (homC hv ε j o o' f).left ≫ (goodPoint hv ε j B' o').gen =
      (goodPoint hv ε j B o).gen ≫ (homO hv ε j o o' f).left := pullback.lift_fst _ _ _
  have h3 : (homO hv ε j o o' f).left ≫ pullback.fst B'.A.hom (spMap j) = pullback.fst B.A.hom (spMap j) ≫ f.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h3).trans (Category.assoc _ _ _).symm)))

theorem exists_ptsEquiv : ∃ e : ChTor.Pts (goodPoint hv ε j B o).A.A ≃*
    (Over.mk (spMap ((algebraMap O C).comp j)) ⟶ B.A), ∀ x, (e x).left = x.left ≫ toBase hv ε j o :=
  exists_pushEquiv_polPull B (spMap j) (spMap (algebraMap O C)) _ (Spec.map_comp (CommRingCat.ofHom j) _)

def ptsEquiv : ChTor.Pts (goodPoint hv ε j B o).A.A ≃* (Over.mk (spMap ((algebraMap O C).comp j)) ⟶ B.A) :=
  (exists_ptsEquiv hv ε j o).choose

theorem ptsEquiv_left (x : ChTor.Pts (goodPoint hv ε j B o).A.A) :
    (ptsEquiv hv ε j o x).left = x.left ≫ toBase hv ε j o := (exists_ptsEquiv hv ε j o).choose_spec x

theorem ptsEquiv_homC (f : B.A ⟶ B'.A) (x : ChTor.Pts (goodPoint hv ε j B o).A.A) :
    ptsEquiv hv ε j o' (x ≫ homC hv ε j o o' f) = ptsEquiv hv ε j o x ≫ f :=
  Over.OverMorphism.ext (by
    rw [ptsEquiv_left, Over.comp_left, Over.comp_left, ptsEquiv_left, Category.assoc, homC_toBase, Category.assoc])

variable [IsAlgClosed C] [CharZero C]

theorem pairT_homT_of_lamEq {X Y A B : Out.PolAV (Sp R)} (oX : X.OAct Λ) (oY : Y.OAct Λ) (oA : A.OAct Λ)
    (oB : B.OAct Λ) (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A) [IsMonHom f₁] [IsMonHom f₂]
    [IsMonHom g₁] [IsMonHom g₂] (h : LamEq A.L f₁ f₂ B.L g₁ g₂) (s : (goodPoint hv ε j X oX).T)
    (t : (goodPoint hv ε j Y oY).T) :
    pairT (goodPoint hv ε j A oA).A ε (homT hv ε j oX oA f₁ s) (homT hv ε j oY oA f₂ t) =
      pairT (goodPoint hv ε j B oB).A ε (homT hv ε j oX oB g₁ s) (homT hv ε j oY oB g₂ t) := by
  have hW := weilEq_of_lamEq GlobalTheory.firstFiveLaws.1 C (goodPoint hv ε j X oX).A (goodPoint hv ε j Y oY).A
    (goodPoint hv ε j A oA).A (goodPoint hv ε j B oB).A (homC hv ε j oX oA f₁) (homC hv ε j oY oA f₂)
    (homC hv ε j oX oB g₁) (homC hv ε j oY oB g₂) inferInstance inferInstance inferInstance inferInstance
    (lamEq_polPull _ (lamEq_polPull _ h))
  refine congrArg ε.equiv.symm (Tate.ext fun n => ?_)
  have hn := one_le_ppow p n
  exact (weilIs_iff hn ((homT hv ε j oX oB g₁ s).lev_pow n) ((homT hv ε j oY oB g₂ t).lev_pow n) _).1
    ((hW _ _ _ _ hn (s.lev_pow n) (t.lev_pow n)).1
      ((weilIs_iff hn ((homT hv ε j oX oA f₁ s).lev_pow n) ((homT hv ε j oY oA f₂ t).lev_pow n) _).2 rfl))

omit [IsAlgClosed C] [CharZero C] in
theorem homT_one [IsMonHom (1 : B.A ⟶ B'.A)] : homT hv ε j o o' 1 = 0 :=
  LinearMap.ext fun t => Tate.ext fun n => (ptsEquiv hv ε j o').injective (by
    rw [lev_homT, ptsEquiv_homC, MonObj.comp_one, LinearMap.zero_apply, Tate.lev_zero, map_one])


omit [IsAlgClosed C] [CharZero C] in
theorem ptsEquiv_lev_sum {A A' : Out.PolAV (Sp R)} (oA : A.OAct Λ) (oA' : A'.OAct Λ) {m m' : ℕ}
    (φ : Fin m → (A.A ⟶ B.A)) (φ' : Fin m' → (A'.A ⟶ B.A)) [∀ k, IsMonHom (φ k)] [∀ k, IsMonHom (φ' k)]
    (s : Fin m → (goodPoint hv ε j A oA).T) (s' : Fin m' → (goodPoint hv ε j A' oA').T) (n : ℕ) :
    ptsEquiv hv ε j o ((∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)).lev n) =
      (∏ k, ptsEquiv hv ε j oA ((s k).lev n) ≫ φ k) * ∏ k, ptsEquiv hv ε j oA' ((s' k).lev n) ≫ φ' k := by
  simp only [Tate.lev_add, lev_sum, map_mul, map_prod, lev_homT, ptsEquiv_homC]


omit [IsAlgClosed C] [CharZero C] in
theorem homT_inverse {A A' : Out.PolAV (Sp R)} (oA : A.OAct Λ) (oA' : A'.OAct Λ) {m m' N : ℕ}
    (φ : Fin m → (A.A ⟶ B.A)) (φ' : Fin m' → (A'.A ⟶ B.A)) [∀ k, IsMonHom (φ k)] [∀ k, IsMonHom (φ' k)]
    (ψ : Fin m → (B.A ⟶ A.A)) (ψ' : Fin m' → (B.A ⟶ A'.A)) [∀ k, IsMonHom (ψ k)] [∀ k, IsMonHom (ψ' k)]
    (h1 : ∀ (T : Over (Sp R)) (x : T ⟶ B.A), (∏ k, x ≫ ψ k ≫ φ k) * (∏ k, x ≫ ψ' k ≫ φ' k) = x ^ N)
    (h2 : ∀ (T : Over (Sp R)) (a : Fin m → (T ⟶ A.A)) (a' : Fin m' → (T ⟶ A'.A)),
      (∀ l, ((∏ k, a k ≫ φ k) * ∏ k, a' k ≫ φ' k) ≫ ψ l = a l ^ N) ∧
      ∀ l, ((∏ k, a k ≫ φ k) * ∏ k, a' k ≫ φ' k) ≫ ψ' l = a' l ^ N) :
    (∀ t, ∑ k, homT hv ε j oA o (φ k) (homT hv ε j o oA (ψ k) t) +
      ∑ k, homT hv ε j oA' o (φ' k) (homT hv ε j o oA' (ψ' k) t) = N • t) ∧
    ∀ (s : Fin m → (goodPoint hv ε j A oA).T) (s' : Fin m' → (goodPoint hv ε j A' oA').T),
      (∀ l, homT hv ε j o oA (ψ l) (∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)) =
        N • s l) ∧
      ∀ l, homT hv ε j o oA' (ψ' l) (∑ k, homT hv ε j oA o (φ k) (s k) + ∑ k, homT hv ε j oA' o (φ' k) (s' k)) =
        N • s' l := by
  refine ⟨fun t => Tate.ext fun n => (ptsEquiv hv ε j o).injective ?_, fun s s' =>
    ⟨fun l => Tate.ext fun n => (ptsEquiv hv ε j oA).injective ?_,
      fun l => Tate.ext fun n => (ptsEquiv hv ε j oA').injective ?_⟩⟩
  · rw [ptsEquiv_lev_sum, lev_nsmul, map_pow, ← h1]
    simp only [lev_homT, ptsEquiv_homC, Category.assoc]
  · rw [lev_homT, ptsEquiv_homC, lev_nsmul, map_pow, ptsEquiv_lev_sum, (h2 _ _ _).1]
  · rw [lev_homT, ptsEquiv_homC, lev_nsmul, map_pow, ptsEquiv_lev_sum, (h2 _ _ _).2]

end Good

section Points

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] [IsAlgClosed C] [CharZero C]

theorem pairV_baseChange [Algebra ℤ_[p] C] {X Y A B : Point p v O Λ} {f₁ : X.T →ₗ[ℤ_[p]] A.T} {f₂ : Y.T →ₗ[ℤ_[p]] A.T}
    {g₁ : X.T →ₗ[ℤ_[p]] B.T} {g₂ : Y.T →ₗ[ℤ_[p]] B.T}
    (h : ∀ s t, pairT A.A A.eps (f₁ s) (f₂ t) = pairT B.A B.eps (g₁ s) (g₂ t)) (x : X.V) (y : Y.V) :
    A.pairV (f₁.baseChange C x) (f₂.baseChange C y) = B.pairV (g₁.baseChange C x) (g₂.baseChange C y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add (f := _), LinearMap.add_apply, hx, hx']
  | tmul c s =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
    | tmul d t => exact congrArg (· • (c * d)) (h s t)

theorem eq_zero_of_actT {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (hg : 0 < P.A.g)
    {a : 𝓞 E} (h : ∀ t, P.actT a t = 0) : a = 0 := by
  by_contra ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  haveI : Nontrivial P.T := Module.nontrivial_of_finrank_pos (R := ℤ_[p]) (by rw [P.hodgeTateLatticePoint_finrank_tateModule]; omega)
  obtain ⟨t, ht⟩ := exists_ne (0 : P.T)
  have e := congrArg (P.actT b) (h t)
  rw [map_zero, ← Module.End.mul_apply, ← map_mul, hb, map_natCast, Module.End.natCast_apply,
    ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_eq_zero] at e
  exact ht (e.resolve_left (Nat.cast_ne_zero.2 hn))

variable {A A' B : Point p v O Λ} {m m' : ℕ} (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (φ' : Fin m' → (A'.T →ₗ[ℤ_[p]] B.T))
  {N : ℕ} (hN : 0 < N) (ψ : Fin m → (B.T →ₗ[ℤ_[p]] A.T)) (ψ' : Fin m' → (B.T →ₗ[ℤ_[p]] A'.T))



include hN in
theorem det_ne_zero_of_inverse {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {A A' B : Point p v O (𝓞 E)}
    (hg : 0 < A.A.g) (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (φ' : Fin m' → (A'.T →ₗ[ℤ_[p]] B.T))
    (g : Matrix (Fin m) (Fin m) (𝓞 E))
    (hφ : ∀ a b s t, pairT B.A B.eps (φ a s) (φ b t) = pairT A.A A.eps (A.actT (g a b) s) t)
    (hφ' : ∀ a b s t, pairT B.A B.eps (φ a s) (φ' b t) = 0)
    (h1 : ∀ t, ∃ (s : Fin m → A.T) (s' : Fin m' → A'.T), ∑ k, φ k (s k) + ∑ k, φ' k (s' k) = N • t)
    (h2 : ∀ s : Fin m → A.T, ∑ k, φ k (s k) = 0 → s = 0) : g.det ≠ 0 := fun h0 => by
  obtain ⟨w, hw, hwg⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine hw (funext fun a => eq_zero_of_actT A hg fun t => congrFun (h2 (fun k => A.actT (w k) t) ?_) a)
  refine (injective_iff_map_eq_zero _).1 B.pairT_bijective.1 _ (LinearMap.ext fun y => ?_)
  obtain ⟨s, s', hs⟩ := h1 y
  refine (smul_eq_zero_iff_right hN.ne').1 ?_
  rw [← map_nsmul, ← hs]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, LinearMap.sum_apply, hφ, hφ', Finset.sum_const_zero, add_zero]
  refine Finset.sum_eq_zero fun b _ => ?_
  have e : ∑ k, g k b * w k = 0 := by simpa [Matrix.vecMul, dotProduct, mul_comm] using congrFun hwg b
  simp only [← Module.End.mul_apply, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← LinearMap.sum_apply, ← map_sum, ← LinearMap.sum_apply, ← map_sum, e]
  simp

theorem star_gram {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {A B : Point p v O (𝓞 E)}
    (hg : 0 < A.A.g) (φ : Fin m → (A.T →ₗ[ℤ_[p]] B.T)) (g : Matrix (Fin m) (Fin m) (𝓞 E))
    (hφ : ∀ a b s t, pairT B.A B.eps (φ a s) (φ b t) = pairT A.A A.eps (A.actT (g a b) s) t) (a b : Fin m) :
    star (g b a) = g a b := by
  refine sub_eq_zero.1 (eq_zero_of_actT A hg fun s => ?_)
  refine (injective_iff_map_eq_zero _).1 A.pairT_bijective.1 _ (LinearMap.ext fun t => ?_)
  have e : pairT A.A A.eps (A.actT (star (g b a)) s) t = pairT A.A A.eps s (A.actT (star (star (g b a))) t) :=
    pairT_act A.oA A.eps _ s t
  rw [map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, ← hφ, e, star_star,
    ← (isAlt_pairT A.A A.eps).neg_eq, ← hφ, (isAlt_pairT B.A B.eps).neg_eq, sub_self, LinearMap.zero_apply]

end Points

end GlobalTheory.GramAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulOfTwistedPullbacksSameBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_of_twistedPullbacks_sameBundle : ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (P : PolAV (Sp K)) (m : ℕ), 1 ≤ m →
    ∀ (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) (baseOver (Sp K))))
      (α α' : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver (Sp K)) P.A).left, (snd (baseOver (Sp K)) P.A ^ m).left]
        ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
      (s₁ s₁' : LB.Sec (LPow P.A P.L ((m ^ 2 : ℕ) : ℤ) (baseOver (Sp K)))), α.IsGen → α'.IsGen →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ →
    IsTwistPull P.A P.L (mulT P.A (baseOver (Sp K)) m) (snd (baseOver (Sp K)) P.A ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α' th s₁' →
    ∃ c : K, (SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁' : EA P (𝟙 (Sp K)) (m ^ 2)) = c • SecMod.mk (fst (baseOver (Sp K)) P.A).left s₁ := by
  first | exact @GlobalTheory.TwistRatio.exists_smul_of_isTwistPull | exact GlobalTheory.TwistRatio.exists_smul_of_isTwistPull | (intros; apply GlobalTheory.TwistRatio.exists_smul_of_isTwistPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializesDominatesStalkOfRegular
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

namespace GlobalTheory

theorem exists_specializes_dominatesStalk_of_regAt (X : Scheme.{0}) [IsIntegral X]
    (V : ValuationSubring X.functionField) (y : X) (hV : ∀ g, RegAt y g → g ∈ V) :
    ∃ z, z ⤳ y ∧ DominatesStalk V z := by
  let ψ : X.presheaf.stalk y →+* V :=
    (algebraMap (X.presheaf.stalk y) X.functionField).codRestrict V.toSubring
      fun a ↦ hV _ ⟨a, rfl⟩
  let l : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk y
  have hl : specAlgebraMap V X.functionField ≫ l = genericFieldPoint X := by
    rw [← specAlgebraMap_fromSpecStalk y, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨l (IsLocalRing.closedPoint V), ?_, dominatesStalk_iff_exists_hom.mpr ⟨l, hl, rfl⟩⟩
  have h := ((IsLocalRing.specializes_closedPoint
    ((Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint V))).map
      (X.fromSpecStalk y).continuous)
  rw [Scheme.fromSpecStalk_closedPoint] at h
  exact h

end GlobalTheory
end

