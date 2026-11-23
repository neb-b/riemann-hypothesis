module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0005
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivBalancedOrderLocus
section
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
  (I : X.IdealSheafData) (m : ℕ)

theorem orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) (x : X) :
    orderAt I x = 0 ∨ (m : ℕ∞) ≤ orderAt I x := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · right
    simp
  have hm1 : 1 ≤ m := hpos
  by_cases h0 : orderAt I x = 0
  · exact Or.inl h0
  right
  have hlt : m - 1 < m := by omega
  have hle : derivIdealSheafIterate k p (m - 1) I ^ m ≤ I ^ (m - (m - 1)) :=
    IsDerivBalanced.derivIdealSheafIterate_pow_le k p h hlt
  have hsub : m - (m - 1) = 1 := by omega
  rw [hsub, pow_one] at hle
  have hord : orderAt I x ≤ orderAt (derivIdealSheafIterate k p (m - 1) I ^ m) x :=
    orderAt_le_of_le hle x
  rw [orderAt_pow k p (derivIdealSheafIterate k p (m - 1) I) m x] at hord
  have hne : orderAt (derivIdealSheafIterate k p (m - 1) I) x ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hord
    exact h0 (le_antisymm hord (by exact zero_le))
  have hmem : x ∈ (derivIdealSheafIterate k p (m - 1) I).support := by
    by_contra hc
    exact hne ((orderAt_eq_zero_iff_not_mem_support _ x).mpr hc)
  have heq := support_derivIdealSheafIterate_eq_orderAtLeastLocus k p I hm1
  have hx : x ∈ orderAtLeastLocus I m := by
    rw [← heq]
    exact hmem
  exact (mem_orderAtLeastLocus_iff I m x).mp hx

theorem orderAtLeastLocus_eq_support_of_isDerivBalanced
    (h : IsDerivBalanced k p I m) (hm : 1 ≤ m) :
    orderAtLeastLocus I m = (I.support : Set X) := by
  ext x
  rw [mem_orderAtLeastLocus_iff]
  constructor
  · intro hx
    have h1 : (1 : ℕ∞) ≤ orderAt I x := le_trans (by exact_mod_cast hm) hx
    exact (one_le_orderAt_iff_mem_support I x).mp h1
  · intro hx
    have hx' : x ∈ I.support := hx
    have hne : orderAt I x ≠ 0 := fun h0 =>
      (orderAt_eq_zero_iff_not_mem_support I x).mp h0 hx'
    rcases orderAt_eq_zero_or_le_orderAt_of_isDerivBalanced k p I m h x with h0 | h0
    · exact absurd h0 hne
    · exact h0

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem le_natCast_or_succ_le (a : ℕ∞) (r : ℕ) :
    a ≤ (r : ℕ∞) ∨ ((r + 1 : ℕ) : ℕ∞) ≤ a := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · exact Or.inr le_top
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ha
    rcases Nat.lt_or_ge r m with hm | hm
    · exact Or.inr (by exact_mod_cast hm)
    · exact Or.inl (by exact_mod_cast hm)

private theorem germ_comp_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (e : V ≤ h ⁻¹ᵁ U) (y : Y) (hy : y ∈ V) :
    (Y.presheaf.germ V y hy).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) (e hy)).hom := by
  have key : h.appLE U V e ≫ Y.presheaf.germ V y hy
      = X.presheaf.germ U (h.base y) (e hy) ≫ h.stalkMap y := by
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    exact (Scheme.Hom.germ_stalkMap ..).symm
  simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom key

theorem stalkIdeal_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    stalkIdeal (I.comap h) y =
      Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y)) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (show h.base y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hV, hyV, e⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (show y ∈ h ⁻¹ᵁ U from hxU)
  have hcomp : (Y.presheaf.germ V y hyV).hom.comp (h.appLE U V e).hom
      = (h.stalkMap y).hom.comp (X.presheaf.germ U (h.base y) hxU).hom :=
    germ_comp_appLE h U V e y hyV
  rw [stalkIdeal_eq_map_germ (I.comap h) y ⟨V, hV⟩ hyV,
    stalkIdeal_eq_map_germ I (h.base y) ⟨U, hU⟩ hxU,
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨U, hU⟩ ⟨V, hV⟩ e,
    Ideal.map_map, Ideal.map_map]
  exact congrArg (fun φ => Ideal.map φ (I.ideal ⟨U, hU⟩)) hcomp

theorem orderAt_le_orderAt_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (I : X.IdealSheafData) (y : Y) :
    orderAt I (h.base y) ≤ orderAt (I.comap h) y := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_orderAt_iff] at hn ⊢
  rw [stalkIdeal_comap]
  have hmono : Ideal.map (h.stalkMap y).hom (stalkIdeal I (h.base y))
      ≤ Ideal.map (h.stalkMap y).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (h.base y)) ^ n) := Ideal.map_mono hn
  exact le_trans hmono
    (le_trans (Ideal.map_pow ..).le
      (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le ..) n))

private theorem one_le_orderAt_of_one_le_orderAt_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (J : X.IdealSheafData)
    (y : Y) (hy : (1 : ℕ∞) ≤ orderAt (J.comap h) y) : (1 : ℕ∞) ≤ orderAt J (h.base y) := by
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (J.comap h) y := by exact_mod_cast hy
  suffices hs : ((1 : ℕ) : ℕ∞) ≤ orderAt J (h.base y) by exact_mod_cast hs
  rw [le_orderAt_iff] at h1 ⊢
  rw [stalkIdeal_comap, pow_one] at h1
  rw [pow_one]
  simpa only [IsLocalRing.maximalIdeal_comap] using
    Ideal.le_comap_map.trans (Ideal.comap_mono h1)

theorem orderAt_comap (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (I : X.IdealSheafData) (y : Y) :
    orderAt (I.comap h) y = orderAt I (h.base y) := by
  have : LocallyOfFiniteType p := inferInstance
  have : LocallyOfFiniteType (h ≫ p) := inferInstance
  refine le_antisymm ?_ (orderAt_le_orderAt_comap h I y)
  rcases eq_or_ne (orderAt I (h.base y)) ⊤ with hI | hI
  · rw [hI]; exact le_top
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 hI
  rw [← hr]
  rcases le_natCast_or_succ_le (orderAt (I.comap h) y) r with hle | hlt
  · exact hle
  exfalso
  have h1 : ((1 : ℕ) : ℕ∞) ≤ orderAt (derivIdealSheafIterate k (h ≫ p) r (I.comap h)) y :=
    le_orderAt_derivIdealSheafIterate k (h ≫ p) (I.comap h) y 1 r (by
      rw [Nat.add_comm]; exact hlt)
  rw [derivIdealSheafIterate_comap k p h r I] at h1
  have h2 : (1 : ℕ∞) ≤ orderAt ((derivIdealSheafIterate k p r I).comap h) y := by exact_mod_cast h1
  have h3 := one_le_orderAt_of_one_le_orderAt_comap h (derivIdealSheafIterate k p r I) y h2
  have h4 : orderAt (derivIdealSheafIterate k p r I) (h.base y) = ((r - r : ℕ) : ℕ∞) :=
    orderAt_derivIdealSheafIterate_eq_sub k p I (h.base y) hr.symm (le_refl r)
  rw [h4, Nat.sub_self] at h3
  simp at h3

theorem orderAtLeastLocus_comap (k : Type u) [Field k] [CharZero k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (h : Y ⟶ X) [AlgebraicGeometry.Smooth h] (I : X.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus (I.comap h) m = ⇑h.base ⁻¹' orderAtLeastLocus I m := by
  ext y
  simp only [Set.mem_preimage, mem_orderAtLeastLocus_iff, orderAt_comap k p h I y]

end FunctorialResolution.EmbeddedResolution
end

