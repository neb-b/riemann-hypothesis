module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.EqOfSpecializes
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0062
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0115

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsAdded
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict

variable {X X' : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]

theorem valAt_unique {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (hg : IsCptGen ξ')
    {z : Spec (CommRingCat.of ℂ) ⟶ X'} {a : Ω} {r t : ℂ} (h₁ : ValAt ξ' z a r) (h₂ : ValAt ξ' z a t) :
    r = t := by
  obtain ⟨hA, s₁, hs₁, hr⟩ := h₁
  obtain ⟨hB, s₂, hs₂, ht⟩ := h₂
  have e : s₁ = s₂ := hg.inj ⟨centre z, hA⟩ (hs₁.trans hs₂.symm)
  rw [← hr, ← ht, e]

theorem valAt_mul {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'} {a b : Ω}
    {r t : ℂ} (h₁ : ValAt ξ' z a r) (h₂ : ValAt ξ' z b t) : ValAt ξ' z (a * b) (r * t) := by
  obtain ⟨hA, s₁, hs₁, hr⟩ := h₁
  obtain ⟨hB, s₂, hs₂, ht⟩ := h₂
  exact ⟨hA, s₁ * s₂, by rw [map_mul, hs₁, hs₂],
    (map_mul _ s₁ s₂).trans (congrArg₂ (· * ·) hr ht)⟩

theorem valAt_one {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    (h : genPt ξ' ⤳ centre z) : ValAt ξ' z (1 : Ω) 1 :=
  ⟨h, 1, map_one _, map_one _⟩

theorem isUnit_of_local {A : Type*} [CommRing A] (φ : A →+* ℂ) [IsLocalHom φ] (s : A) (h : φ s ≠ 0) :
    IsUnit s := by
  exact IsUnit.of_map φ s (Ne.isUnit h)

theorem unitAt_of_valAt {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {z : Spec (CommRingCat.of ℂ) ⟶ X'}
    (h' : genPt ξ' ⤳ centre z) {a : Ω} {r : ℂ} (hr : r ≠ 0) (hv : ValAt ξ' z a r) :
    unitAt ξ' ⟨centre z, h'⟩ a := by
  obtain ⟨h, s, hs, hr'⟩ := hv
  have hu : IsUnit s := isUnit_of_local (Scheme.stalkClosedPointTo z).hom s (by rw [hr']; exact hr)
  obtain ⟨u, rfl⟩ := hu
  have hinv : genMap ξ' ⟨centre z, h'⟩ ↑u⁻¹ * genMap ξ' ⟨centre z, h'⟩ ↑u = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hne : genMap ξ' ⟨centre z, h'⟩ ↑u ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hinv
    exact zero_ne_one hinv
  refine ⟨?_, ⟨↑u, hs⟩, ⟨↑u⁻¹, ?_⟩⟩
  · rw [← hs]; exact hne
  · rw [← hs]; exact eq_inv_of_mul_eq_one_left hinv

private theorem stalkSpecializes_comp_stalkClosedPointTo_congr {K : Type} [Field K] (g₁ g₂ : Spec (CommRingCat.of K) ⟶ X)
    (e : g₁ = g₂) {q : X} (h₁ : g₁ (IsLocalRing.closedPoint K) ⤳ q) (h₂ : g₂ (IsLocalRing.closedPoint K) ⤳ q) :
    X.presheaf.stalkSpecializes h₁ ≫ Scheme.stalkClosedPointTo g₁ =
      X.presheaf.stalkSpecializes h₂ ≫ Scheme.stalkClosedPointTo g₂ := by
  subst e; rfl

private theorem stalkSpecializes_comp_stalkClosedPointTo_specMap_comp {K K' : Type} [Field K] [Field K'] (i : K →+* K')
    (g : Spec (CommRingCat.of K) ⟶ X) {q : X}
    (h₂ : (Spec.map (CommRingCat.ofHom i) ≫ g) (IsLocalRing.closedPoint K') ⤳ q)
    (hp : g (IsLocalRing.closedPoint K) ⤳ q) :
    X.presheaf.stalkSpecializes h₂ ≫ Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ g) =
      X.presheaf.stalkSpecializes hp ≫ Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom i := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, TopCat.Presheaf.germ_stalkSpecializes_assoc,
    Scheme.germ_stalkClosedPointTo, Scheme.germ_stalkClosedPointTo_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality]
  simp only [← Category.assoc]
  congr 1

theorem valAt_of_regAt {ξ : Spec (CommRingCat.of Ω₀) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} {f : X' ⟶ X}
    {i : Ω₀ →+* Ω} (hd : Dominates ξ' ξ f i) (z : Spec (CommRingCat.of ℂ) ⟶ X')
    (h' : genPt ξ' ⤳ centre z) (hp : genPt ξ ⤳ f (centre z)) {a : Ω₀}
    (ha : a ∈ regAt ξ ⟨f (centre z), hp⟩) :
    ∃ r : ℂ, ValAt ξ (z ≫ f) a r ∧ ValAt ξ' z (i a) r := by
  obtain ⟨s, hs⟩ := RingHom.mem_range.1 ha
  refine ⟨(Scheme.stalkClosedPointTo (z ≫ f)).hom s, ⟨hp, s, hs, rfl⟩, h', (f.stalkMap (centre z)).hom s, ?_, ?_⟩
  · have h₁ : (ξ' ≫ f) (IsLocalRing.closedPoint Ω) ⤳ f (centre z) := f.base.hom.map_specializes h'
    have h₂ : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint Ω) ⤳ f (centre z) := by
      rw [← hd]; exact h₁
    have h'' : ξ' (IsLocalRing.closedPoint Ω) ⤳ centre z := h'
    have hp'' : ξ (IsLocalRing.closedPoint Ω₀) ⤳ f (centre z) := hp
    have key : f.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h'' ≫ Scheme.stalkClosedPointTo ξ' =
        X.presheaf.stalkSpecializes hp'' ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
      rw [← Category.assoc, ← Scheme.Hom.stalkSpecializes_stalkMap, Category.assoc,
        ← Scheme.stalkClosedPointTo_comp]
      exact (stalkSpecializes_comp_stalkClosedPointTo_congr (ξ' ≫ f) (Spec.map (CommRingCat.ofHom i) ≫ ξ) hd h₁ h₂).trans
        (stalkSpecializes_comp_stalkClosedPointTo_specMap_comp i ξ h₂ hp'')
    have := congrArg (fun φ => φ.hom s) key
    rw [← hs]
    exact this
  · rw [Scheme.stalkClosedPointTo_comp]
    rfl

theorem coordsAt_restrict : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, addJ J N k) → ℂ),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → IsCptGen ξ' →
    (∀ q : X', genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordsAt ξ' (addY y x') z w → CoordsAt ξ y (z ≫ f) (fun p => w (addV J N p)) := by
  intro X X' Ω₀ Ω _ _ _ ξ ξ' f K _ J _ y N x' z w hgen htie hcpt hgen' hd hc
  classical
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨fun k => hc1 (Sum.inr k), fun k c hu => ?_⟩
  have hyA : ∀ j : J k, addY y x' ⟨Sum.inr k, j⟩ = algebraMap Ω₀ Ω (y ⟨k, j⟩) := fun j => rfl
  obtain ⟨hy, hv⟩ := hc2 (Sum.inr k) c hu
  rw [hyA] at hy
  have hyc : y ⟨k, c⟩ ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
  refine ⟨hyc, fun j => ?_⟩
  have hp : genPt ξ ⤳ f (centre z) := hgen _
  have h' : genPt ξ' ⤳ centre z := hgen' _
  obtain ⟨c₀, hc₀ne, hc₀⟩ := htie.cover ⟨f (centre z), hp⟩
  have hx0 : (∏ k', y ⟨k', c₀ k'⟩) ≠ 0 := hc₀ne
  have hy0 : y ⟨k, c₀ k⟩ ≠ 0 := fun h0 => hx0 (Finset.prod_eq_zero (Finset.mem_univ k) h0)
  have hprod : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) * y ⟨k, c₀ k⟩ =
      (∏ k', y ⟨k', c₀ k'⟩) * y ⟨k, j⟩ := by
    intro j
    rw [← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', Function.update c₀ k j k'⟩) (Finset.mem_univ k),
      ← Finset.mul_prod_erase Finset.univ (fun k' => y ⟨k', c₀ k'⟩) (Finset.mem_univ k)]
    have e : ∏ x ∈ Finset.univ.erase k, y ⟨x, Function.update c₀ k j x⟩ =
        ∏ x ∈ Finset.univ.erase k, y ⟨x, c₀ x⟩ :=
      Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
    simp only [Function.update_self]
    rw [e]
    ring
  have hratio : ∀ j : J k, (∏ k', y ⟨k', Function.update c₀ k j k'⟩) / (∏ k', y ⟨k', c₀ k'⟩) =
      y ⟨k, j⟩ / y ⟨k, c₀ k⟩ := by
    intro j
    rw [div_eq_div_iff hx0 hy0, hprod j, mul_comm]
  have hreg : ∀ j : J k, y ⟨k, j⟩ / y ⟨k, c₀ k⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := fun j => by
    rw [← hratio j]
    exact hc₀ (Function.update c₀ k j)
  obtain ⟨r₂, hr₂a, hr₂b⟩ := valAt_of_regAt hd z h' hp (hreg c)
  obtain ⟨r₀, hr₀, -⟩ := hv (c₀ k)
  rw [hyA, hyA] at hr₀
  have hmul := valAt_mul hr₂b hr₀
  have hy0' : algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) ≠ 0 := (map_ne_zero _).2 hy0
  have hone : algebraMap Ω₀ Ω (y ⟨k, c⟩ / y ⟨k, c₀ k⟩) *
      (algebraMap Ω₀ Ω (y ⟨k, c₀ k⟩) / algebraMap Ω₀ Ω (y ⟨k, c⟩)) = 1 := by
    rw [map_div₀]
    field_simp
  rw [hone] at hmul
  have h1 : r₂ * r₀ = 1 := valAt_unique hcpt hmul (valAt_one h')
  have hr₂ne : r₂ ≠ 0 := left_ne_zero_of_mul_eq_one h1
  have hunit := unitAt_of_valAt hp hr₂ne hr₂a
  have hinvreg : (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ ∈ regAt ξ ⟨f (centre z), hp⟩ := hunit.2.2
  have hregjc : y ⟨k, j⟩ / y ⟨k, c⟩ ∈ regAt ξ ⟨f (centre z), hp⟩ := by
    have e : y ⟨k, j⟩ / y ⟨k, c⟩ = (y ⟨k, j⟩ / y ⟨k, c₀ k⟩) * (y ⟨k, c⟩ / y ⟨k, c₀ k⟩)⁻¹ := by
      field_simp
    rw [e]
    exact Subring.mul_mem _ (hreg j) hinvreg
  obtain ⟨r, hr1, hr2⟩ := valAt_of_regAt hd z h' hp hregjc
  obtain ⟨r', hr', hw⟩ := hv j
  rw [hyA, hyA] at hr'
  rw [map_div₀] at hr2
  have e3 : r = r' := valAt_unique hcpt hr2 hr'
  refine ⟨r, hr1, ?_⟩
  rw [e3]
  exact hw

end GlobalTheory.CompanionTheory.Ar.FlagStep.CoordsRestrict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexCoordsReindexed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordsDown

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isUnit_natCast_of_local {A : Type*} [CommRing A] (φ : A →+* ℂ) [IsLocalHom φ] (r : ℕ) (hr : r.Prime) :
    IsUnit (r : A) := by
  apply isUnit_of_map_unit φ
  rw [map_natCast]
  exact isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hr.ne_zero)

theorem unitAt_centre {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (z : Spec (CommRingCat.of ℂ) ⟶ X')
    (h : genPt ξ' ⤳ centre z) (r : ℕ) (hr : r.Prime) : unitAt ξ' ⟨centre z, h⟩ (r : Ω) := by
  have hz : IsLocalHom (Scheme.stalkClosedPointTo z).hom := inferInstance
  have hu : IsUnit ((r : X'.presheaf.stalk (centre z))) := isUnit_natCast_of_local (Scheme.stalkClosedPointTo z).hom r hr
  have hu' : IsUnit ((r : Ω)) := by
    have := hu.map (genMap ξ' ⟨centre z, h⟩)
    rwa [map_natCast] at this
  obtain ⟨u, hu1⟩ := hu.exists_right_inv
  refine ⟨hu'.ne_zero, ⟨(r : X'.presheaf.stalk (centre z)), map_natCast _ _⟩, ⟨u, ?_⟩⟩
  have e := congrArg (genMap ξ' ⟨centre z, h⟩) hu1
  rw [map_mul, map_natCast, map_one] at e
  exact eq_inv_of_mul_eq_one_right e

theorem genMap_stalkMap (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

theorem valAt_down {ξ' : Spec (CommRingCat.of Ω) ⟶ X'} (g : X' ⟶ X) (hinj : IsCptGen ξ')
    (z : Spec (CommRingCat.of ℂ) ⟶ X') (h' : genPt ξ' ⤳ centre z)
    (h : genPt (ξ' ≫ g) ⤳ g (centre z))
    (hreg : regAt ξ' ⟨centre z, h'⟩ = regAt (ξ' ≫ g) ⟨g (centre z), h⟩)
    {a : Ω} {r : ℂ} (hv : ValAt ξ' z a r) : ValAt (ξ' ≫ g) (z ≫ g) a r := by
  obtain ⟨h1, s, hs, rfl⟩ := hv
  have ha : a ∈ regAt (ξ' ≫ g) ⟨g (centre z), h⟩ := by
    rw [← hreg]
    exact ⟨s, hs⟩
  obtain ⟨s₀, hs₀⟩ := ha
  have e : (g.stalkMap (centre z)).hom s₀ = s := by
    apply hinj.inj ⟨centre z, h'⟩
    rw [genMap_stalkMap ξ' g ⟨centre z, h'⟩ h s₀]
    exact hs₀.trans hs.symm
  subst e
  refine ⟨h, s₀, hs₀, ?_⟩
  exact congrArg (fun t => t.hom s₀) (Scheme.stalkClosedPointTo_comp z g)

theorem coordsAt_down : ∀ (X X' : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (K' : Type) (J' : K' → Type) (y' : (Σ k, J' k) → Ω) (bk : K → K') (bx : ∀ k, J k ≃ J' (bk k)) (z : Spec (CommRingCat.of ℂ) ⟶ X') (w : (Σ k, J' k) → ℂ), (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → IsCptGen ξ' → ξ' ≫ g = ξ → (∀ k a, y' ⟨bk k, bx k a⟩ = y ⟨k, a⟩) → (∀ q' : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q') → ∀ h : genPt ξ ⤳ g q'.1, regAt ξ' q' = regAt ξ ⟨g q'.1, h⟩) → CoordsAt ξ' y' z w → CoordsAt ξ y (z ≫ g) (fun p : (Σ k, J k) => w ⟨bk p.1, bx p.1 p.2⟩) := by
  intro X X' Ω _ ξ ξ' g K J y K' J' y' bk bx z w hall hall' hgen hcomp hy hreg hw
  subst hcomp
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := hw.1 (bk k)
    exact ⟨(bx k).symm c, by simpa using hc⟩
  · obtain ⟨hne, hv⟩ := hw.2 (bk k) (bx k c) hc
    refine ⟨by rwa [hy] at hne, fun i => ?_⟩
    obtain ⟨r, hr, e⟩ := hv (bx k i)
    rw [hy, hy] at hr
    have h' := hall' (centre z)
    have h := hall (g (centre z))
    refine ⟨r, valAt_down g hgen z h' h (hreg ⟨centre z, h'⟩ (fun p hp hf => hf (unitAt_centre z h' p hp)) h) hr, e⟩

end GlobalTheory.CompanionTheory.Ar.CoordsDown
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.GenPtModel

theorem mem_genericPoints_of_eq {X : Scheme.{0}} {x : X}
    (h : ∀ p : X, p ⤳ x → p = x) : x ∈ genericPoints X := by
  show closure {x} ∈ irreducibleComponents X
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, fun T hT hxT => ?_⟩
  obtain ⟨p, hp⟩ := QuasiSober.sober hT.2 hT.1
  have hpx : p = x := h p ((hp.specializes_iff_mem).2 (hxT (subset_closure (Set.mem_singleton x))))
  intro y hy
  rw [← hpx]
  exact specializes_iff_mem_closure.1 ((hp.specializes_iff_mem).2 hy)

theorem genPt_mem_genericPoints : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.genPt ξ₀ ∈ genericPoints Y.X := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  apply mem_genericPoints_of_eq
  intro p hp
  have hp' : p ∈ Set.range (Y.X.fromSpecStalk (GlobalTheory.CompanionTheory.Ar.genPt ξ₀)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hp
  obtain ⟨q, rfl⟩ := hp'
  have hfield : IsField (Y.X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.genPt ξ₀)) :=
    MulEquiv.isField (Field.toIsField Ω₀)
      (RingEquiv.ofBijective (CommRingCat.Hom.hom (Scheme.stalkClosedPointTo ξ₀)) hξ.bij).toMulEquiv
  have hq : q = IsLocalRing.closedPoint _ := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal q.isPrime.ne_top
    · intro a ha
      by_cases h0 : a = 0
      · rw [h0]
        exact q.asIdeal.zero_mem
      · obtain ⟨b, hb⟩ := hfield.mul_inv_cancel h0
        exact absurd ⟨⟨a, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩ ((IsLocalRing.mem_maximalIdeal a).1 ha)
  rw [hq, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.CompanionTheory.Ar.GenPtModel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAddedProjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem block_ratio_mem {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {c : (k : K) → J k} {p : Cpt ξ}
    (hc : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p) (k : K) (i : J k) :
    y ⟨k, c k⟩ ≠ 0 ∧ y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ regAt ξ p := by
  classical
  obtain ⟨h0, hc⟩ := hc
  have hck : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 h0) k (Finset.mem_univ k)
  refine ⟨hck k, ?_⟩
  have h := hc (Function.update c k i)
  have e : (∏ k', y ⟨k', Function.update c k i k'⟩) / (∏ k', y ⟨k', c k'⟩) = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · simp
    · intro b _ hb
      rw [Function.update_of_ne hb]
      exact div_self (hck b)
    · simp
  rw [← e]
  exact h

theorem tie_blocks : ∀ (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω₀) (N : ℕ) (x' : Fin (N + 1) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    CoordTie ℤ ξ' (fun c' : (k : Unit ⊕ K) → addJ J N k => ∏ k, addY y x' ⟨k, c' k⟩) := by
  intro X X' Ω₀ Ω _ _ _ ξ ξ' f K _ J _ y N x' _ hy hx hd
  have h1 : CoordTie ℤ ξ' (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x' p.2) ⟨k, c' k⟩) := by
    simpa using CoordBase.coordTie_reindex (Equiv.funUnique Unit (Fin (N + 1))) hx
  have h2 : ∀ (k : K) (p : Cpt ξ'), ∃ i, InChart ξ'
      (fun i' : J k => (fun p : (Σ k, J k) => algebraMap Ω₀ Ω (y p)) ⟨k, i'⟩) i p := by
    intro k p
    obtain ⟨h, hreg, -⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f (algebraMap Ω₀ Ω) hd p
    obtain ⟨c, hc⟩ := hy.cover ⟨f p.1, h⟩
    refine ⟨c k, ?_, fun i => ?_⟩
    · exact (map_ne_zero _).2 (block_ratio_mem hc k (c k)).1
    · have := hreg _ (block_ratio_mem hc k i).2
      rwa [map_div₀] at this
  have h3 := _root_.GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi X' Ω ξ' Unit (fun _ => Fin (N + 1)) (fun p => x' p.2) K J
    (fun p => algebraMap Ω₀ Ω (y p)) h1 h2
  convert h3 using 2 with c'
  exact Fintype.prod_sum_type _

end GlobalTheory.CompanionTheory.Ar.FlagStep.TieBlocks
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DenseOpenGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus

theorem exists_dense_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), M.ξ ≫ f = y₀ ≫ Y.j → ∃ U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens, Dense (U : Set ((pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}))) ∧ pullback.fst (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' (f ⁻¹' abLocus Y.t.G) = U := by
  intro E _ _ _ H D l Xo c Y Ω _ κ _ x M f y₀ hξ
  set π := spMap (algebraMap (𝓞 c.F) c.F) with hπ
  haveI : IsOpenImmersion Y.jQ := Y.jQ_open
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI hpre : IsPreimmersion π :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  haveI hfst : IsPreimmersion (pullback.fst (f ≫ Y.s) π) := inferInstance
  have hcond : (pullback.fst (f ≫ Y.s) π ≫ f) ≫ Y.s = pullback.snd (f ≫ Y.s) π ≫ π := by
    rw [Category.assoc, pullback.condition]
  set g := pullback.lift (pullback.fst (f ≫ Y.s) π ≫ f) (pullback.snd (f ≫ Y.s) π) hcond with hg
  have hgf : g ≫ pullback.fst Y.s π = pullback.fst (f ≫ Y.s) π ≫ f := pullback.lift_fst _ _ _
  have hpt : ∀ p, f (pullback.fst (f ≫ Y.s) π p) = pullback.fst Y.s π (g p) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgf]
  have hopen : IsOpen (g ⁻¹' Set.range Y.jQ) :=
    (IsOpenImmersion.isOpen_range Y.jQ).preimage g.continuous
  refine ⟨⟨g ⁻¹' Set.range Y.jQ, hopen⟩, ?_, ?_⟩
  · have hc2 : M.ξ ≫ f ≫ Y.s = (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) ≫ π := by
      rw [← Category.assoc, hξ]
      simp only [Model.j, Category.assoc, pullback.condition]
      rfl
    set ξ' := pullback.lift M.ξ (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) hc2 with hξ'
    have hξg : ξ' ≫ g = y₀ ≫ Y.jQ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hgf, ← Category.assoc, pullback.lift_fst, hξ]
        simp only [Model.j, Category.assoc]
        rfl
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc]
    set p0 := ξ' (IsLocalRing.closedPoint Ω) with hp0
    have hp0U : p0 ∈ g ⁻¹' Set.range Y.jQ := by
      refine ⟨y₀ (IsLocalRing.closedPoint Ω), ?_⟩
      have h := congrArg (fun (k : Spec (CommRingCat.of Ω) ⟶ pullback Y.s π) => k (IsLocalRing.closedPoint Ω)) hξg
      change g (ξ' (IsLocalRing.closedPoint Ω)) = Y.jQ (y₀ (IsLocalRing.closedPoint Ω)) at h
      exact h.symm
    have hp0M : pullback.fst (f ≫ Y.s) π p0 = genPt M.ξ := by
      have h := congrArg (fun (k : Spec (CommRingCat.of Ω) ⟶ M.X) => k (IsLocalRing.closedPoint Ω))
        (pullback.lift_fst M.ξ (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) hc2)
      change pullback.fst (f ≫ Y.s) π (ξ' (IsLocalRing.closedPoint Ω)) = M.ξ (IsLocalRing.closedPoint Ω) at h
      exact h
    have hemb := Scheme.Hom.isEmbedding (pullback.fst (f ≫ Y.s) π)
    intro p
    have hsp : p0 ⤳ p := by
      rw [← hemb.isInducing.specializes_iff, hp0M]
      exact M.all _
    exact closure_mono (Set.singleton_subset_iff.2 hp0U) (specializes_iff_mem_closure.1 hsp)
  · ext p
    simp only [Set.mem_preimage, TopologicalSpace.Opens.coe_mk]
    rw [hpt, ← Set.mem_preimage (f := pullback.fst Y.s π), Y.ab_gen]

end GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsClopenIrreducibleCpt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_cptOver_mem_isClopen_isIrreducible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (u : Xo.XF c), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ (U : Set (Xo.XF c)) (_ : CptOver Y U), u ∈ U ∧ IsClopen U ∧ IsIrreducible U := by
  intro E _ _ _ H D l Xo c O _ β Y u hyp
  obtain ⟨hinj, hnoeth, hfrac⟩ := hyp
  have hmem := irreducibleComponent_mem_irreducibleComponents u
  obtain ⟨Z⟩ := nonempty_cptOver_of_fraction hinj hfrac Y _ hmem
  obtain ⟨U', hU', -⟩ := cptOver_isOpen_isDomain E H D l Xo c O β Y _ Z ⟨hinj, hnoeth, hfrac⟩
  refine ⟨irreducibleComponent u, Z, mem_irreducibleComponent, ⟨isClosed_of_mem_irreducibleComponents _ hmem, ?_⟩,
    isIrreducible_irreducibleComponent⟩
  rw [← hU']
  exact U'.isOpen

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

