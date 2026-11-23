module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems

noncomputable section

section Local

variable {O : Type u} [CommRing O] [IsLocalRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G]

def unitSec : Spec (CommRingCat.of O) ⟶ G.left := η[G].left

lemma unitSec_hom : unitSec G ≫ G.hom = 𝟙 _ := Over.w η[G]

def origin : G.left := unitSec G (closedPoint (CommRingCat.of O))

def LocRing : Type u := G.left.presheaf.stalk (origin G)

instance : CommRing (LocRing G) :=
  inferInstanceAs (CommRing (G.left.presheaf.stalk (origin G)))

def fromLoc : Spec (CommRingCat.of (LocRing G)) ⟶ G.left := G.left.fromSpecStalk (origin G)

def strMap : CommRingCat.of O ⟶ CommRingCat.of (LocRing G) :=
  Spec.preimage (fromLoc G ≫ G.hom)

instance : Algebra O (LocRing G) := (strMap G).hom.toAlgebra

def augMap : CommRingCat.of (LocRing G) ⟶ CommRingCat.of O :=
  Scheme.stalkClosedPointTo (unitSec G)

lemma spec_augMap : Spec.map (augMap G) ≫ fromLoc G = unitSec G :=
  Scheme.Spec_stalkClosedPointTo_fromSpecStalk (unitSec G)

lemma spec_strMap : Spec.map (strMap G) = fromLoc G ≫ G.hom := Spec.map_preimage _

lemma strMap_augMap : strMap G ≫ augMap G = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, spec_strMap, ← Category.assoc, spec_augMap, unitSec_hom, Spec.map_id]

def aug : LocRing G →ₐ[O] O :=
  { (augMap G).hom with
    commutes' := fun r => congrArg (fun φ => φ.hom r) (strMap_augMap G) }

def augIdeal : Ideal (LocRing G) := RingHom.ker (aug G)

def Cotangent : Type u := (augIdeal G).Cotangent

instance : AddCommGroup (Cotangent G) := inferInstanceAs (AddCommGroup (augIdeal G).Cotangent)

instance : Module O (Cotangent G) := inferInstanceAs (Module O (augIdeal G).Cotangent)

abbrev Lie : Type u := Module.Dual O (Cotangent G)

lemma sub_aug_mem (a : LocRing G) : a - algebraMap O (LocRing G) (aug G a) ∈ augIdeal G := by
  rw [augIdeal, RingHom.mem_ker]
  simp

def dAt (a : LocRing G) : Cotangent G :=
  (augIdeal G).toCotangent ⟨a - algebraMap O (LocRing G) (aug G a), sub_aug_mem G a⟩

lemma dAt_add (a b : LocRing G) : dAt G (a + b) = dAt G a + dAt G b := by
  unfold dAt
  have e : (⟨a + b - algebraMap O (LocRing G) (aug G (a + b)), sub_aug_mem G (a + b)⟩ : augIdeal G) =
      ⟨a - algebraMap O (LocRing G) (aug G a), sub_aug_mem G a⟩ +
        ⟨b - algebraMap O (LocRing G) (aug G b), sub_aug_mem G b⟩ := by
    apply Subtype.ext
    simp only [map_add (f := _), Submodule.coe_add]
    ring
  rw [e]
  exact map_add _ _ _

lemma dAt_algebraMap (r : O) : dAt G (algebraMap O (LocRing G) r) = 0 := by
  unfold dAt
  have e : (⟨algebraMap O (LocRing G) r - algebraMap O (LocRing G) (aug G (algebraMap O (LocRing G) r)),
      sub_aug_mem G _⟩ : augIdeal G) = 0 := by
    apply Subtype.ext
    simp
  rw [e]
  exact map_zero _

lemma dAt_mul (a b : LocRing G) : dAt G (a * b) = aug G a • dAt G b + aug G b • dAt G a := by
  unfold dAt
  have ha := sub_aug_mem G a
  have hb := sub_aug_mem G b
  have e : (⟨a * b - algebraMap O (LocRing G) (aug G (a * b)), sub_aug_mem G (a * b)⟩ : augIdeal G) =
      algebraMap O (LocRing G) (aug G a) • ⟨b - algebraMap O (LocRing G) (aug G b), hb⟩ +
        algebraMap O (LocRing G) (aug G b) • ⟨a - algebraMap O (LocRing G) (aug G a), ha⟩ +
          ⟨(a - algebraMap O (LocRing G) (aug G a)) * (b - algebraMap O (LocRing G) (aug G b)),
            Ideal.mul_mem_left _ _ hb⟩ := by
    apply Subtype.ext
    simp only [map_mul, Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    ring
  have hz : (augIdeal G).toCotangent
      ⟨(a - algebraMap O (LocRing G) (aug G a)) * (b - algebraMap O (LocRing G) (aug G b)),
        Ideal.mul_mem_left _ _ hb⟩ = 0 := by
    rw [Ideal.toCotangent_eq_zero, pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [e]
  show (augIdeal G).toCotangent (_ + _ + _) = aug G a • (augIdeal G).toCotangent _ + aug G b • (augIdeal G).toCotangent _
  rw [map_add (f := _), map_add (f := _), hz, add_zero, map_smul, map_smul, algebraMap_smul, algebraMap_smul]

variable {G} in
def tangentAlg {R : Type u} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R) :
    LocRing G →ₐ[O] DualNumber R where
  toFun a := TrivSqZeroExt.inl (algebraMap O R (aug G a)) + TrivSqZeroExt.inr (v (dAt G a))
  map_one' := by
    have := dAt_algebraMap G 1
    rw [map_one] at this
    simp [this]
  map_mul' a b := by
    ext
    · simp
    · simp [dAt_mul, ← Algebra.smul_def, add_comm]
      simp [Algebra.smul_def, mul_comm, add_comm]
  map_zero' := by
    have := dAt_algebraMap G 0
    rw [map_zero] at this
    simp [this]
  map_add' a b := by
    ext
    · simp
    · simp [dAt_add]
  commutes' r := by
    simp [dAt_algebraMap, TrivSqZeroExt.algebraMap_eq_inl']

end Local

section Points

variable (O : Type u) [CommRing O]

def specOver (R : Type u) [CommRing R] [Algebra O R] : Over (Spec (CommRingCat.of O)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap O R)))


end Points

section Tangent

variable {O : Type u} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]

def tangentPt {R : Type u} [CommRing R] [Algebra O R] (v : Cotangent G →ₗ[O] R) :
    specOver O (DualNumber R) ⟶ G :=
  Over.homMk (Spec.map (CommRingCat.ofHom (tangentAlg v).toRingHom) ≫ fromLoc G) (by
    change (Spec.map _ ≫ fromLoc G) ≫ G.hom = Spec.map _
    rw [Category.assoc, ← spec_strMap, ← Spec.map_comp]
    congr 1
    ext r : 2
    exact (tangentAlg v).commutes r)

end Tangent

section Characters

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]


variable [IsCommMonObj G] (G)

variable {G}

end Characters

section HodgeTate

variable {O : Type u} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))}
  [GrpObj G] [IsCommMonObj G]

variable (G)

end HodgeTate

section Valued

variable {C : Type u} [Field C]

end Valued

end

end GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems
