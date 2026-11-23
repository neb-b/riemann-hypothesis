module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0041
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HcptPull

theorem fullTorsion_of_dominates : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → FullTorsion G ξ n → FullTorsion G' ξ' n := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ _ _ φ n hd hp hf k _ i' g hg
  have hd' : ξ' ≫ f = spMap i ≫ ξ := hd
  have e : (spMap i' ≫ ξ') ≫ f = spMap (i'.comp i) ≫ ξ := by
    rw [Category.assoc, hd', ← Category.assoc]
    congr 1
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let ρ : (Over.mk (spMap i' ≫ ξ') ⟶ G') →* (Over.mk ((spMap i' ≫ ξ') ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt hp.1.w) fun x y => Over.OverMorphism.ext (hp.2 _ x y _ _ rfl rfl).symm
  have ha : (ρ g) ^ n = 1 := by rw [← map_pow, hg, map_one]
  have tr : ∀ {a b : Sp k ⟶ X} (_ : a = b) (u : Over.mk a ⟶ G), u ^ n = 1 →
      ∃ u' : Over.mk b ⟶ G, u'.left = u.left ∧ u' ^ n = 1 := by
    intro a b h u hu
    subst h
    exact ⟨u, rfl, hu⟩
  obtain ⟨u, hl, hu⟩ := tr e (ρ g) ha
  obtain ⟨x, hx⟩ := hf k (i'.comp i) u hu
  have hxw : x.left ≫ G.hom = ξ := by simpa using Over.w x
  have hw : (spMap i ≫ x.left) ≫ G.hom = ξ' ≫ f := by
    rw [Category.assoc, hxw, hd']
  have hs : spMap (i'.comp i) = spMap i' ≫ spMap i := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨Over.homMk (hp.1.lift (spMap i ≫ x.left) ξ' hw) (hp.1.lift_snd _ _ _), ?_⟩
  apply hp.1.hom_ext
  · have h1 : g.left ≫ φ = spMap (i'.comp i) ≫ x.left := by
      rw [← hx, hl]
      rfl
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_fst]
    rw [h1, hs, Category.assoc]
  · have h2 : g.left ≫ G'.hom = spMap i' ≫ ξ' := by simpa using Over.w g
    simp only [Over.homMk_left, Category.assoc, IsPullback.lift_snd]
    exact h2

end GlobalTheory.CompanionTheory.Ar.HcptPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsInGenericFibre
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open PositivityTheory.HtPt.Ml (generic_max mem_of_dense_of_max)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem genericPoints_subset_range_j :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O]
      (β : O →+* c.F) (Y : Model Xo c β),
      IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) →
        genericPoints Y.X ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y hO hFraction v hv
  let := β.toAlgebra
  have : IsFractionRing O c.F := hFraction
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have := Y.flat
  have := Y.jQ_open
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    have := hi
    have := isProper_str O N
    rw [← hs]
    infer_instance
  have : IsNoetherian (pullback Y.s (spMap β)) := {}

  -- Flatness lifts the generic point of the base to a generalization of v.
  let z : Sp c.F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum c.F)
  have hz : (spMap β z).asIdeal = ⊥ := by
    change RingHom.ker β = ⊥
    exact (RingHom.injective_iff_ker_eq_bot β).mp (IsFractionRing.injective O c.F)
  have hspec : spMap β z ⤳ Y.s v := by
    apply (PrimeSpectrum.le_iff_specializes _ _).mp
    change (spMap β z).asIdeal ≤ (Y.s v).asIdeal
    rw [hz]
    exact bot_le
  obtain ⟨v', hv'v, hv'⟩ := Flat.generalizingMap Y.s hspec
  rw [generic_max hv hv'v] at hv'
  obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback v z hv'
  -- Every generalization of q has the same image, and the projection is injective.
  have hqmax : ∀ q', q' ⤳ q → q' = q := by
    intro q' hq'
    apply (pullback.fst Y.s (spMap β)).isEmbedding.injective
    rw [hq]
    exact generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)
  obtain ⟨w, hw⟩ := mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax
  exact ⟨w, by rw [Model.j, Scheme.Hom.comp_apply, hw, hq]⟩

end GlobalTheory.CompanionTheory.Ar.M0
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

abbrev OCp (p : Nat.Primes) : Type :=
  (NormedField.valuation (K := ℂ_[p])).valuationSubring

def inE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) :
    E →+* c.F := τ.codRestrict c.F.toSubfield (c.conj τ)

def stdLat (A C : Type) [CommRing A] [Field C] [Algebra A C] (g : ℕ) : Submodule A (Fin g → C) where
  carrier := {x | ∀ i, x i ∈ (algebraMap A C).range}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun a x hx i => by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ (hx i)

section Eval

variable {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs]
  {C : Type} [Field C] {g : ℕ}

def comb {R : Subring Ω} (ℓ : Fin g → Vs) (x : Fin g → R) : Vs := ∑ i, (x i : Ω) • ℓ i

def Tied {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρ : 𝓞 E →+* Module.End Ω Vs)
    (ρC : 𝓞 E →+* Module.End C (Fin g → C)) : Prop :=
  ∀ (a : 𝓞 E) (x x' : Fin g → R), ρ a (comb ℓ x) = comb ℓ x' → ρC a (fun i => ψ (x i)) = fun i => ψ (x' i)

def HodgeAt {R : Subring Ω} {N : ℕ} (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (HL : Submodule R (Vs × Module.Dual Ω Vs)) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs) : Prop :=
  HT.IsFreeOn ρH HL t ∧
    HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) = Submodule.span R (Set.range ℓ) ∧
    ∀ f : Module.Dual Ω Vs, ((0 : Vs), f) ∈ HL ↔ ∀ e ∈ Submodule.span R (Set.range ℓ), f e ∈ R

def IsEval {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R (Vs × Module.Dual Ω Vs))
    (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C)) : Prop :=
  (∀ (a : 𝓞 E) (h : HL) (h' : ρH a (h : Vs × Module.Dual Ω Vs) ∈ HL), ev ⟨_, h'⟩ = ρHC a (ev h)) ∧
  (∀ (h : HL) (x : Fin g → R), (h : Vs × Module.Dual Ω Vs).1 = comb ℓ x → (ev h).1 = fun i => ψ (x i)) ∧
  (∀ (h : HL) (x : Fin g → R) (r : R), (h : Vs × Module.Dual Ω Vs).1 = 0 →
    (h : Vs × Module.Dual Ω Vs).2 (comb ℓ x) = r → (ev h).2 (fun i => ψ (x i)) = ψ r)

end Eval
end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IntOpen

theorem epi_of_mono_spMap {O F : Type} [CommRing O] [CommRing F] (β : O →+* F) (h : Mono (spMap β))
    {T : Type} [CommRing T] (g₁ g₂ : F →+* T) (e : g₁.comp β = g₂.comp β) : g₁ = g₂ := by
  have h1 : spMap g₁ ≫ spMap β = spMap g₂ ≫ spMap β := by
    rw [← spMap_comp, ← spMap_comp, e]
  have h2 := Spec.map_injective ((cancel_mono (spMap β)).1 h1)
  exact congrArg CommRingCat.Hom.hom h2

theorem lift_local {R : CommRingCat} [IsLocalRing R] {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (g : Spec R ⟶ X) (h : g (IsLocalRing.closedPoint R) ∈ Set.range j) : ∃ u, u ≫ j = g := by
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    have hs : p ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint p
    exact (hs.map g.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift j g hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem interior_iff_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (z : Sp ℂ ⟶ A.X), Mono (spMap β) → Mono Y.j ∧ (A.Interior z ↔ ∃ u : Spec (A.X.presheaf.stalk (centre z)) ⟶ Xo.XF c, u ≫ Y.j = A.X.fromSpecStalk (centre z) ≫ A.f) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A z hβ
  have hab : ∀ x : A.X, A.f x ∈ abLocus Y.t.G ↔ x ∈ abLocus A.t.G :=
    abLocus_pullback abLocusOne Y.t.semi A.m.cart.1
  refine ⟨?_, ?_⟩
  · have : IsOpenImmersion Y.jQ := Y.jQ_open
    unfold Model.j; infer_instance
  constructor
  · intro hx
    have hx' : A.f (centre z) ∈ abLocus Y.t.G := (hab _).2 hx
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := {}
    haveI : IsReduced A.X := by
      have : ∀ x : A.X, _root_.IsReduced (A.X.presheaf.stalk x) := fun x => by
        have := (A.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk A.X
    let g : Spec (A.X.presheaf.stalk (centre z)) ⟶ Sp O := A.X.fromSpecStalk (centre z) ≫ A.f ≫ Y.s
    let θ : O →+* A.X.presheaf.stalk (centre z) := (Spec.preimage g).hom
    have hk : ∀ a, β a = 0 → θ a = 0 := fun a ha =>
      _root_.GlobalTheory.CompanionTheory.Ggeo.germ_vanish_of_generic_dominated A.X Ω O A.ξ A.all (A.f ≫ Y.s) (A.cst.comp β) A.cst_over (centre z) a (by simp [ha])
    have hu : ∀ b, β b ≠ 0 → IsUnit (θ b) := fun b hb =>
      _root_.GlobalTheory.CompanionTheory.Ggeo.unit_of_local_hom_charZero_nf O c.F _ ℂ β θ (Scheme.stalkClosedPointTo z).hom (Scheme.isLocalHom_stalkClosedPointTo' z) hk b hb
    obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.CompanionTheory.Ggeo.extend_to_fraction_field_relay O c.F _ β θ (_root_.GlobalTheory.CompanionTheory.Ggeo.epi_subfield_closure_range_eq_top O c.F β (fun T _ g₁ g₂ e => epi_of_mono_spMap β hβ g₁ g₂ e)) hu hk
    have w : (A.X.fromSpecStalk (centre z) ≫ A.f) ≫ Y.s = spMap χ ≫ spMap β := by
      rw [← spMap_comp, hχ, Category.assoc]
      change g = _
      rw [← Spec.map_preimage g]
      rfl
    haveI : IsOpenImmersion Y.jQ := Y.jQ_open
    obtain ⟨u, hu⟩ := lift_local Y.jQ (pullback.lift _ _ w) (by
      rw [← Y.ab_gen]
      show (pullback.lift _ _ w ≫ pullback.fst _ _) _ ∈ abLocus _
      rw [pullback.lift_fst]
      have e1 : (A.X.fromSpecStalk (centre z) ≫ A.f) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z))) = A.f (centre z) := by
        show A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = _
        rw [Scheme.fromSpecStalk_closedPoint]
      exact e1 ▸ hx')
    refine ⟨u, ?_⟩
    rw [Model.j, ← Category.assoc, hu, pullback.lift_fst]
  · rintro ⟨u, hu⟩
    show centre z ∈ abLocus A.t.G
    rw [← hab]
    have h1 : A.f (centre z) = Y.j (u (IsLocalRing.closedPoint _)) := by
      have e1 := congrArg (fun φ : Spec (A.X.presheaf.stalk (centre z)) ⟶ Y.X => φ (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) hu
      change Y.j (u (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) at e1
      rw [Scheme.fromSpecStalk_closedPoint] at e1
      exact e1.symm
    rw [h1]
    have h2 : Y.jQ (u (IsLocalRing.closedPoint _)) ∈ Set.range Y.jQ := ⟨_, rfl⟩
    rw [← Y.ab_gen] at h2
    exact h2

end GlobalTheory.CompanionTheory.Ar.IntOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeTransportEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat

namespace HodgeTransport

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V V' : Type} [AddCommGroup V] [Module Ω V]
  [AddCommGroup V'] [Module Ω V'] {F F' : Type} [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
  {E : Type} [Field E] [NumberField E]

def conjE (e : V ≃ₗ[Ω] V') : (V × Module.Dual Ω V) ≃ₗ[Ω] (V' × Module.Dual Ω V') :=
  e.prodCongr e.symm.dualMap

theorem conjE_apply (e : V ≃ₗ[Ω] V') (y : V × Module.Dual Ω V) :
    conjE e y = (e y.1, y.2 ∘ₗ e.symm.toLinearMap) := rfl

theorem conjE_symm_apply (e : V ≃ₗ[Ω] V') (y : V' × Module.Dual Ω V') :
    (conjE e).symm y = (e.symm y.1, y.2 ∘ₗ e.toLinearMap) := rfl

def cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) : 𝓞 E →+* Module.End Ω F' :=
  (g.conjRingEquiv : Module.End Ω F →+* Module.End Ω F').comp ρ

theorem cj_apply (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (a : 𝓞 E) (y : F') :
    cj g ρ a y = g (ρ a (g.symm y)) := rfl

theorem mem_map_equiv (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (p : Cpt ξ) (y : F') :
    y ∈ M.map g.toLinearMap p ↔ g.symm y ∈ M p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem map_symm_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') :
    (M.map g.toLinearMap).map g.symm.toLinearMap = M := by
  funext p
  ext y
  rw [mem_map_equiv, mem_map_equiv]
  simp

theorem isFrameAt_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F} {p : Cpt ξ}
    (h : M.IsFrameAt b p) : (M.map g.toLinearMap).IsFrameAt (g ∘ b) p := by
  refine ⟨(LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1, ?_⟩
  change Submodule.map _ (M p) = _
  rw [h.2, Submodule.map_span, Set.range_comp]
  rfl

theorem isFrameAt_map_iff {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F'} {p : Cpt ξ} :
    (M.map g.toLinearMap).IsFrameAt b p ↔ M.IsFrameAt (g.symm ∘ b) p := by
  constructor
  · intro h
    have := isFrameAt_map g.symm h
    rwa [map_symm_map] at this
  · intro h
    have := isFrameAt_map g h
    have e : g ∘ g.symm ∘ b = b := by funext i; simp
    rwa [e] at this

theorem detLat_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') {r : ℕ} (u : Fin r → F') :
    detLat (M.map g.toLinearMap) u = detLat M (g.symm ∘ u) := by
  funext p
  simp only [detLat]
  congr 1
  ext t
  refine exists_congr fun A => and_congr_left fun _ => ?_
  rw [isFrameAt_map_iff]
  have e : (g.symm ∘ fun i => ∑ j, A i j • u j) = fun i => ∑ j, A i j • (g.symm ∘ u) j := by
    funext i
    simp
  rw [e]

theorem isFreeOn_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {ρ : 𝓞 E →+* Module.End Ω F} {p : Cpt ξ} {N : ℕ}
    {t : Fin N → F} (h : HT.IsFreeOn ρ (M p) t) :
    HT.IsFreeOn (cj g ρ) (M.map g.toLinearMap p) (g ∘ t) := by
  have e : (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      cj g ρ (RingOfIntegers.basis E q.2) ((g ∘ t) q.1)) =
      g ∘ fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        ρ (RingOfIntegers.basis E q.2) (t q.1) := by
    funext q
    simp [cj_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact (LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1
  · have e2 : ((M.map g.toLinearMap p : Submodule _ F') : Set F') = g '' (M p : Set F) := rfl
    rw [e2]
    have := Submodule.map_span g.toLinearMap (M p : Set F)
    rw [h.2.1, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm
  · rw [e]
    change Submodule.map _ (M p) = _
    rw [h.2.2, Submodule.map_span, Set.range_comp]
    rfl

theorem eigProj_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    HT.eigProj (cj g ρ) σ y = g (HT.eigProj ρ σ (g.symm y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [HT.eigProj, LinearMap.sum_apply, cj_apply, map_sum]

theorem mem_eigSp_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    y ∈ HT.eigSp (cj g ρ) σ ↔ g.symm y ∈ HT.eigSp ρ σ := by
  rw [HT.LatBasic.mem_eigSp, HT.LatBasic.mem_eigSp]
  refine forall_congr' fun a => ?_
  rw [cj_apply, ← map_smul, LinearEquiv.eq_symm_apply]

theorem eigQuot_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) :
    (M.map g.toLinearMap).map (HT.eigProj (cj g ρ) σ) = (M.map (HT.eigProj ρ σ)).map g.toLinearMap := by
  funext p
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩

variable {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {ρ' : 𝓞 E →+* Module.End Ω V'} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

def transport (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v)) :
    HodgeLat (L.map e.toLinearMap) ρ' bar r where
  ρH := cj (conjE e) 𝓗.ρH
  HL := 𝓗.HL.map (conjE e).toLinearMap
  act_fst a y := by
    rw [cj_apply, conjE_apply, 𝓗.act_fst, h, conjE_symm_apply]
    simp
  act_inr a φ := by
    rw [cj_apply, conjE_symm_apply]
    simp only [map_zero]
    rw [𝓗.act_inr, conjE_apply]
    refine Prod.ext (by simp) (LinearMap.ext fun x => ?_)
    simp [h]
  map_fst := by
    funext p
    conv_rhs => rw [← 𝓗.map_fst]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  comap_inr := by
    funext p
    ext φ
    have h1 : (φ ∈ (𝓗.HL.map (conjE e).toLinearMap).comap (LinearMap.inr Ω V' (Module.Dual Ω V')) p) ↔
        ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p := by
      change ((0, φ) : V' × Module.Dual Ω V') ∈ 𝓗.HL.map (conjE e).toLinearMap p ↔ _
      rw [mem_map_equiv, conjE_symm_apply]
      simp
    have h2 : ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p ↔
        φ ∘ₗ e.toLinearMap ∈ L.dual p := by
      rw [← 𝓗.comap_inr]
      rfl
    rw [h1, h2]
    change (∀ x ∈ L p, φ (e x) ∈ regAt ξ p) ↔ ∀ x ∈ L.map e.toLinearMap p, φ x ∈ regAt ξ p
    constructor
    · rintro hφ _ ⟨z, hz, rfl⟩
      exact hφ z hz
    · intro hφ z hz
      exact hφ _ ⟨z, hz, rfl⟩
  free p := by
    obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
    exact ⟨U, hU, conjE e ∘ x, fun q hq => isFreeOn_map (conjE e) (hx q hq)⟩
  vb := by
    rw [← e.finrank_eq]
    intro p hp
    obtain ⟨U, hU, b, hb, hf⟩ := 𝓗.vb p hp
    refine ⟨U, hU, e ∘ b, ?_, fun q hq hqU => isFrameAt_map e (hf q hq hqU)⟩
    rw [Set.range_comp]
    have := Submodule.map_span e.toLinearMap (Set.range b)
    rw [hb, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm

theorem transport_degZero (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v))
    (σ : E →+* Ω) (ϖ : Ω) (hd : 𝓗.DegZero σ ϖ) : (transport e 𝓗 h).DegZero σ ϖ := by
  intro u hu hsp
  have hq : (transport e 𝓗 h).quot σ = (𝓗.quot σ).map (conjE e).toLinearMap :=
    eigQuot_map 𝓗.HL (conjE e) 𝓗.ρH σ
  rw [hq, detLat_map]
  refine hd _ ((LinearMap.linearIndependent_iff (conjE e).symm.toLinearMap (LinearEquiv.ker _)).2 hu) ?_
  ext y
  have h1 : Set.range ((conjE e).symm ∘ u) = (conjE e).symm.toLinearMap '' Set.range u := Set.range_comp _ _
  rw [h1, ← Submodule.map_span, hsp]
  change _ ↔ y ∈ HT.eigSp 𝓗.ρH σ
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_eigSp_cj (conjE e) 𝓗.ρH σ z).1 hz
  · intro hy
    refine ⟨conjE e y, (mem_eigSp_cj (conjE e) 𝓗.ρH σ _).2 (by simpa using hy), by simp⟩

end HodgeTransport

theorem hodgeLat_transport : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  intro X Ω _ ξ E _ _ V V' _ _ _ _ e L ρ ρ' bar r 𝓗 h
  exact ⟨HodgeTransport.transport e 𝓗 h, fun σ ϖ hd => HodgeTransport.transport_degZero e 𝓗 h σ ϖ hd⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

