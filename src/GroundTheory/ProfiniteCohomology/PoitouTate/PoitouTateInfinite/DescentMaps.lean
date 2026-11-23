module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.InflationRestriction.CohomologyResMemCohomologyConjInvariants
public import GroundTheory.ProfiniteCohomology.Bundle0002
public import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
public import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

noncomputable section

section Square

variable {k : Type u} [CommRing k] {H G' G : Type u} [Group H] [Group G'] [Group G] [TopologicalSpace H]
  [TopologicalSpace G'] [TopologicalSpace G] [IsTopologicalGroup H] [IsTopologicalGroup G'] [IsTopologicalGroup G]

theorem cochainsMapAlong_eq_of_forall_eq {A : Rep.{u} k G} {C : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep C]
    (φ ψ : H →* G) (hφ : Continuous φ) (hψ : Continuous ψ) (f : Rep.res φ A ⟶ C) (g : Rep.res ψ A ⟶ C)
    (h : ∀ σ, φ σ = ψ σ) (hfg : ∀ a : A, f.hom a = g.hom a) :
    cochainsMapAlong φ hφ f = cochainsMapAlong ψ hψ g := by
  ext n x : 3
  apply Subtype.ext
  funext s
  change f.hom (((cochainsComplexι A).f n).hom x (⇑φ ∘ s)) = g.hom (((cochainsComplexι A).f n).hom x (⇑ψ ∘ s))
  have e : ⇑φ ∘ s = ⇑ψ ∘ s := funext fun i => h (s i)
  rw [e, hfg]

theorem cohomologyMapAlong_comp_apply_of_eq (φ : H →* G) (hφ : Continuous φ) (π : G →* G') (hπ : Continuous π)
    (φ' : H →* G') (hφ' : Continuous φ') (hc : ∀ σ, π (φ σ) = φ' σ) {B : Rep.{u} k G'} {A : Rep.{u} k G}
    {C : Rep.{u} k H} [IsDiscreteRep B] [IsDiscreteRep A] [IsDiscreteRep C] (f : Rep.res π B ⟶ A)
    (g : Rep.res φ A ⟶ C) (g' : Rep.res φ' B ⟶ C) (hg : ∀ b, g'.hom b = g.hom (f.hom b)) (n : ℕ)
    (x : cohomology B n) :
    (cohomologyMapAlong φ hφ g n).hom ((cohomologyMapAlong π hπ f n).hom x) =
      (cohomologyMapAlong φ' hφ' g' n).hom x := by
  have e := cohomologyMapAlong_comp π hπ f φ hφ g n
  have e2 : cohomologyMapAlong (π.comp φ) (hπ.comp hφ) ((Rep.resFunctor φ).map f ≫ g) n =
      cohomologyMapAlong φ' hφ' g' n := by
    rw [cohomologyMapAlong, cohomologyMapAlong,
      cochainsMapAlong_eq_of_forall_eq (π.comp φ) φ' (hπ.comp hφ) hφ' ((Rep.resFunctor φ).map f ≫ g) g' hc
        fun b => (hg b).symm]
  rw [← e2, e]
  rfl

theorem cohomologyMap_cohomologyMapAlong_apply (φ : H →* G) (hφ : Continuous φ) {A : Rep.{u} k G}
    {B C : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C] (f : Rep.res φ A ⟶ B) (g : B ⟶ C)
    (n : ℕ) (x : cohomology A n) :
    (cohomologyMap g n).hom ((cohomologyMapAlong φ hφ f n).hom x) = (cohomologyMapAlong φ hφ (f ≫ g) n).hom x := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap]
  have e := cohomologyMapAlong_comp φ hφ f (MonoidHom.id H) continuous_id g n
  have e2 : cohomologyMapAlong (φ.comp (MonoidHom.id H)) (hφ.comp continuous_id)
      ((Rep.resFunctor (MonoidHom.id H)).map f ≫ g) n = cohomologyMapAlong φ hφ (f ≫ g) n := by
    rw [cohomologyMapAlong, cohomologyMapAlong,
      cochainsMapAlong_eq_of_forall_eq (φ.comp (MonoidHom.id H)) φ (hφ.comp continuous_id) hφ
        ((Rep.resFunctor (MonoidHom.id H)).map f ≫ g) (f ≫ g) (fun _ => rfl) fun _ => rfl]
  rw [← e2, e]
  rfl

end Square

section Descend

variable {k H G Q Q' : Type u} [CommRing k] [Group H] [Group G] [Group Q] [Group Q'] [TopologicalSpace H]
  [TopologicalSpace G] [TopologicalSpace Q] [TopologicalSpace Q']
  (π : G →ₜ* Q) (hπ : Function.Surjective π) (A : Rep.{u} k G) (hA : ∀ g, π g = 1 → A.ρ g = 1)

variable {D : Rep.{u} k G} {DQ : Rep.{u} k Q}

variable {DQ' : Rep.{u} k Q'}

end Descend

end

end GroundTheory.ProfCoh
