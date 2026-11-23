module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial

variable {S : Scheme.{0}} {k : Type} [Field k]

def ptObj (t : Spec (CommRingCat.of k) ⟶ S) : Over S := Over.mk t

def dualObj (t : Spec (CommRingCat.of k) ⟶ S) : Over S :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ t)

def origin (t : Spec (CommRingCat.of k) ⟶ S) : ptObj t ⟶ dualObj t :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ t = t
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k :=
      (TrivSqZeroExt.fstHom k k k).comp_algebraMap
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

def scaleAlg (c : k) : DualNumber k →ₐ[k] DualNumber k :=
  TrivSqZeroExt.map (c • LinearMap.id)

def scale (t : Spec (CommRingCat.of k) ⟶ S) (c : k) : dualObj t ⟶ dualObj t :=
  Over.homMk (Spec.map (CommRingCat.ofHom (scaleAlg c).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ ≫ t = Spec.map _ ≫ t
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (scaleAlg c).toRingHom.comp (algebraMap k (DualNumber k)) = algebraMap k (DualNumber k) :=
      (scaleAlg c).comp_algebraMap
    rw [this])

lemma origin_scale (t : Spec (CommRingCat.of k) ⟶ S) (c : k) : origin t ≫ scale t c = origin t := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  simp [scaleAlg]

variable (G : Over S) [GrpObj G]

def Lie (t : Spec (CommRingCat.of k) ⟶ S) : Subgroup (dualObj t ⟶ G) where
  carrier := {v | origin t ≫ v = 1}
  mul_mem' {v w} hv hw := by
    change origin t ≫ (v * w) = 1
    rw [MonObj.comp_mul, hv, hw, _root_.mul_one]
  one_mem' := MonObj.comp_one _
  inv_mem' {v} hv := by
    change origin t ≫ v⁻¹ = 1
    rw [GrpObj.comp_inv, hv, inv_one]

variable {G}

def smulLie {t : Spec (CommRingCat.of k) ⟶ S} (c : k) (v : Lie G t) : Lie G t :=
  ⟨scale t c ≫ v.1, by
    change origin t ≫ scale t c ≫ v.1 = 1
    rw [← Category.assoc, origin_scale]; exact v.2⟩

def mapLie {H : Over S} [GrpObj H] (f : G ⟶ H) [IsMonHom f] (t : Spec (CommRingCat.of k) ⟶ S)
    (v : Lie G t) : Lie H t :=
  ⟨v.1 ≫ f, by
    change origin t ≫ v.1 ≫ f = 1
    have hv : origin t ≫ v.1 = 1 := v.2
    rw [← Category.assoc, hv, MonObj.one_comp]⟩

variable {O : Type} [CommRing O]

def actLie (ρ : OAct O G) (t : Spec (CommRingCat.of k) ⟶ S) (a : O) (v : Lie G t) : Lie G t :=
  haveI := ρ.hom a
  mapLie (ρ.act a) t v

def eigenspace (ρ : OAct O G) (t : Spec (CommRingCat.of k) ⟶ S) (τ : O →+* k) : Set (Lie G t) :=
  {v | ∀ a : O, actLie ρ t a v = smulLie (τ a) v}

variable [IsCommMonObj G]

def comb {t : Spec (CommRingCat.of k) ⟶ S} {n : ℕ} (v : Fin n → Lie G t) (c : Fin n → k) : Lie G t :=
  ∏ i, smulLie (c i) (v i)

def IsBasisOf {t : Spec (CommRingCat.of k) ⟶ S} (W : Set (Lie G t)) {n : ℕ} (v : Fin n → Lie G t) : Prop :=
  (∀ i, v i ∈ W) ∧ Set.BijOn (comb v) Set.univ W

def HasEigenDim (ρ : OAct O G) (t : Spec (CommRingCat.of k) ⟶ S) (τ : O →+* k) (n : ℕ) : Prop :=
  ∃ v : Fin n → Lie G t, IsBasisOf (eigenspace ρ t τ) v

end GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs
