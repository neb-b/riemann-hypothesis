module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.Bundle0001

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Complex

variable {R : Type u} [Ring R] {ι' : Type*} {c : ComplexShape ι'} {ι : Type*}
  {K : HomologicalComplex (ModuleCat.{u} R) c} {L : ι → HomologicalComplex (ModuleCat.{u} R) c}

theorem homologyMap_pi_bijective (p : ∀ i, K ⟶ L i)
    (hp : ∀ m, Function.Bijective fun (x : K.X m) (i : ι) => ((p i).f m).hom x) (n : ι') :
    Function.Bijective fun (x : K.homology n) (i : ι) =>
      (HomologicalComplex.homologyMap (p i) n).hom x := by
  constructor
  · intro x y hxy
    rw [← sub_eq_zero]
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance (x - y)
    have h0 : ∀ i, (HomologicalComplex.homologyMap (p i) n).hom (x - y) = 0 := fun i => by
      rw [map_sub, sub_eq_zero]
      exact congrFun hxy i
    rw [← hz] at h0 ⊢
    have hw : ∀ i, ∃ w : (L i).X (c.prev n),
        ((L i).d (c.prev n) n).hom w = ((p i).f n).hom ((K.iCycles n).hom z) := fun i => by
      have h := h0 i
      rw [homologyMap_homologyπ_apply, homologyπ_eq_zero_iff, iCycles_cyclesMap_apply] at h
      exact h
    choose w hw using hw
    obtain ⟨v, hv⟩ := (hp (c.prev n)).2 w
    rw [homologyπ_eq_zero_iff]
    refine ⟨v, (hp n).1 (funext fun i => ?_)⟩
    have hvi : ((p i).f (c.prev n)).hom v = w i := congrFun hv i
    change ((p i).f n).hom ((K.d (c.prev n) n).hom v) = ((p i).f n).hom ((K.iCycles n).hom z)
    rw [hom_f_d_apply, hvi, hw i]
  · intro y
    have hz : ∀ i, ∃ z : (L i).cycles n, ((L i).homologyπ n).hom z = y i := fun i =>
      (ModuleCat.epi_iff_surjective _).1 inferInstance (y i)
    choose z hz using hz
    obtain ⟨x, hx⟩ := (hp n).2 fun i => ((L i).iCycles n).hom (z i)
    have hxi : ∀ i, ((p i).f n).hom x = ((L i).iCycles n).hom (z i) := fun i => congrFun hx i
    have hdx : (K.d n (c.next n)).hom x = 0 := by
      refine (hp (c.next n)).1 (funext fun i => ?_)
      change ((p i).f (c.next n)).hom ((K.d n (c.next n)).hom x) = ((p i).f (c.next n)).hom 0
      rw [map_zero, hom_f_d_apply, hxi]
      exact iCycles_d_apply _ _ _ _
    obtain ⟨w, hw⟩ := exists_iCycles_eq K x hdx
    refine ⟨(K.homologyπ n).hom w, funext fun i => ?_⟩
    change (HomologicalComplex.homologyMap (p i) n).hom ((K.homologyπ n).hom w) = y i
    rw [homologyMap_homologyπ_apply, ← hz i]
    congr 1
    apply (ModuleCat.mono_iff_injective ((L i).iCycles n)).1 inferInstance
    rw [iCycles_cyclesMap_apply, hw, hxi]

end Complex

section GroupCohomology

variable {k G : Type u} [CommRing k] [Group G] {ι : Type*} {P : Rep.{u} k G}
  {A : ι → Rep.{u} k G}

end GroupCohomology

end GroundTheory.ProfCoh
