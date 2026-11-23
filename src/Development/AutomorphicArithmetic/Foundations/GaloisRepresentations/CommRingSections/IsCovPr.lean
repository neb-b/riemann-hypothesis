module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0004

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh (inter inter_le_comp)

namespace UpperTheory.Gal.DifferentialFormSections

variable {K : Type} [CommRing K]

abbrev Fm (K A : Type) [CommRing K] [CommRing A] [Algebra K A] : Type := ExteriorAlgebra A Ω[A⁄K]

section
variable {A B : Type} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]

def fmMap (φ : A →ₐ[K] B) : Fm K A →ₐ[K] Fm K B :=
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  (ExteriorAlgebra.lift A ⟨((ExteriorAlgebra.ι B).restrictScalars A) ∘ₗ KaehlerDifferential.map K K A B,
    fun _ => ExteriorAlgebra.ι_sq_zero _⟩).restrictScalars K

end

abbrev Sch (K : Type) [CommRing K] : Type 1 := Over (Spec (CommRingCat.of K))

def Sec (X : Sch K) (U : X.left.Opens) : Type := Γ(X.left, U)

instance (X : Sch K) (U : X.left.Opens) : CommRing (Sec X U) := inferInstanceAs (CommRing Γ(X.left, U))

instance (X : Sch K) (U : X.left.Opens) : Algebra K (Sec X U) :=
  (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ Scheme.Hom.appLE X.hom ⊤ U le_top).hom : K →+* Γ(X.left, U)).toAlgebra

def secMap {X Y : Sch K} (f : Y ⟶ X) {U : X.left.Opens} {V : Y.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U) : Sec X U →ₐ[K] Sec Y V where
  toRingHom := (Scheme.Hom.appLE f.left U V h).hom
  commutes' r := by
    have e : Scheme.Hom.appLE X.hom ⊤ U le_top ≫ Scheme.Hom.appLE f.left U V h = Scheme.Hom.appLE Y.hom ⊤ V le_top := by
      refine (Scheme.Hom.appLE_comp_appLE f.left X.hom ⊤ U V le_top h).trans ?_
      have e2 := Over.w f
      revert e2
      generalize Y.hom = g
      rintro rfl
      rfl
    exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom r)) e

def secRes (X : Sch K) {U V : X.left.Opens} (h : V ≤ U) : Sec X U →ₐ[K] Sec X V := secMap (𝟙 X) h

variable {X Y : Sch K} {ι κ : Type}

abbrev cap (U : ι → X.left.Opens) {n : ℕ} (i : Fin n → ι) : X.left.Opens := inter (X := X.left.toTopCat) U i

abbrev Co (U : ι → X.left.Opens) (n : ℕ) : Type := ∀ i : Fin (n + 1) → ι, Fm K (Sec X (cap U i))

def dC (U : ι → X.left.Opens) (n : ℕ) : Co U n →ₗ[K] Co U (n + 1) :=
  LinearMap.pi fun i => ∑ k : Fin (n + 2), ((-1 : ℤ) ^ (k : ℕ)) •
    ((fmMap (secRes X (inter_le_comp (X := X.left.toTopCat) U i k.succAbove))).toLinearMap ∘ₗ LinearMap.proj (i ∘ k.succAbove))

def Bd (U : ι → X.left.Opens) : (n : ℕ) → Submodule K (Co U n)
  | 0 => ⊥
  | n + 1 => LinearMap.range (dC U n)

abbrev HC (U : ι → X.left.Opens) (n : ℕ) : Type := LinearMap.ker (dC U n) ⧸ (Bd U n).submoduleOf (LinearMap.ker (dC U n))


abbrev all (X : Sch K) : X.left.affineOpens → X.left.Opens := Subtype.val

abbrev H (X : Sch K) (n : ℕ) : Type := HC (all X) n

structure IsCov (U : ι → X.left.Opens) : Prop where
  aff : ∀ i, IsAffineOpen (U i)
  cov : iSup U = ⊤

structure Coc (X : Sch K) : Type 1 where
  ι : Type
  U : ι → X.left.Opens
  cov : IsCov U
  g : ∀ i : Fin 2 → ι, (Sec X (cap U i))ˣ
  coc : ∀ i : Fin 3 → ι,
    secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 2)) (g (i ∘ Fin.succAbove 2)).val *
      secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 0)) (g (i ∘ Fin.succAbove 0)).val =
      secRes X (inter_le_comp (X := X.left.toTopCat) U i (Fin.succAbove 1)) (g (i ∘ Fin.succAbove 1)).val

end UpperTheory.Gal.DifferentialFormSections
