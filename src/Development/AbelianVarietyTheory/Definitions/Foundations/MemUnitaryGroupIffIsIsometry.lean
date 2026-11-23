module

public import Mathlib

@[expose] public section

open scoped TensorProduct
open NumberField

namespace GlobalTheory

abbrev SesqForm (R M : Type*) [CommRing R] [StarRing R] [AddCommGroup M] [Module R M] :=
  M →ₗ[R] M →ₗ⋆[R] R

structure HermForm (R M : Type*) [CommRing R] [StarRing R] [AddCommGroup M] [Module R M] where

  toSesq : SesqForm R M
  star_apply' : ∀ x y, star (toSesq x y) = toSesq y x

namespace HermForm

section Ring

variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

instance : FunLike (HermForm R M) M (M →ₗ⋆[R] R) where
  coe h := h.toSesq
  coe_injective f g H := by
    cases f; cases g; congr; exact DFunLike.coe_injective H

instance : LinearMapClass (HermForm R M) R M (M →ₗ⋆[R] R) where
  map_add h := h.toSesq.map_add
  map_smulₛₗ h := h.toSesq.map_smul

variable (h : HermForm R M)

@[simp] theorem star_apply (x y : M) : star (h x y) = h y x := h.star_apply' x y

theorem add_left (x y z : M) : h (x + y) z = h x z + h y z := by simp

theorem smul_left (a : R) (x y : M) : h (a • x) y = a * h x y := by simp

theorem apply_eq_zero_comm (x y : M) : h x y = 0 ↔ h y x = 0 := by
  rw [← h.star_apply x y, star_eq_zero]

def ofFun (f : M → M → R) (add_left : ∀ x y z, f (x + y) z = f x z + f y z)
    (smul_left : ∀ (a : R) x y, f (a • x) y = a * f x y)
    (star_symm : ∀ x y, star (f x y) = f y x) : HermForm R M where
  toSesq := LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) f add_left smul_left
    (fun x y z => by rw [← star_symm, add_left, star_add, star_symm, star_symm])
    (fun a x y => by rw [← star_symm, smul_left, star_mul', star_symm]; rfl)
  star_apply' := star_symm

def Nondegenerate : Prop := h.toSesq.Nondegenerate

theorem nondegenerate_iff_left : h.Nondegenerate ↔ ∀ x, (∀ y, h x y = 0) → x = 0 :=
  ⟨fun H => H.1, fun H => ⟨H, fun y hy => H y fun x => (h.apply_eq_zero_comm x y).1 (hy x)⟩⟩

variable {h}

theorem Nondegenerate.eq_zero_left (H : h.Nondegenerate) {x : M} (hx : ∀ y, h x y = 0) : x = 0 :=
  H.1 x hx

structure IsometryEquiv (h₁ : HermForm R M) (h₂ : HermForm R N) extends M ≃ₗ[R] N where
  map_app' : ∀ x y, h₂ (toFun x) (toFun y) = h₁ x y

def Isometric (h₁ : HermForm R M) (h₂ : HermForm R N) : Prop := Nonempty (h₁.IsometryEquiv h₂)

namespace IsometryEquiv

variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}

instance : EquivLike (h₁.IsometryEquiv h₂) M N where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

instance : LinearEquivClass (h₁.IsometryEquiv h₂) R M N where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

@[simp] theorem map_app (f : h₁.IsometryEquiv h₂) (x y : M) : h₂ (f x) (f y) = h₁ x y :=
  f.map_app' x y

@[symm] def symm (f : h₁.IsometryEquiv h₂) : h₂.IsometryEquiv h₁ :=
  ⟨f.toLinearEquiv.symm, fun x y => by
    rw [← f.map_app]
    exact congrArg₂ (fun a b => h₂ a b) (f.toLinearEquiv.apply_symm_apply x)
      (f.toLinearEquiv.apply_symm_apply y)⟩

@[trans] def trans (f : h₁.IsometryEquiv h₂) (g : h₂.IsometryEquiv h₃) : h₁.IsometryEquiv h₃ :=
  ⟨f.toLinearEquiv.trans g.toLinearEquiv, fun x y => (g.map_app _ _).trans (f.map_app x y)⟩

@[simp] theorem apply_symm_apply (f : h₁.IsometryEquiv h₂) (x : N) : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x

theorem map_app_right (f : h₁.IsometryEquiv h₂) (x : N) (y : M) :
    h₂ x (f y) = h₁ (f.symm x) y := by rw [← f.map_app, apply_symm_apply]

theorem nondegenerate (f : h₁.IsometryEquiv h₂) (H : h₁.Nondegenerate) : h₂.Nondegenerate := by
  rw [nondegenerate_iff_left]
  intro x hx
  have : f.symm x = 0 := H.eq_zero_left fun y => by rw [← f.map_app_right, hx]
  simpa using congrArg f this

end IsometryEquiv

namespace Isometric

variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}

end Isometric

def unitaryGroup (h : HermForm R M) : Subgroup (M ≃ₗ[R] M) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' _ _ := rfl
  mul_mem' hg hg' x y := (hg _ _).trans (hg' x y)
  inv_mem' {g} hg x y := by
    rw [← hg]
    exact congrArg₂ (fun a b => h a b) (g.apply_symm_apply x) (g.apply_symm_apply y)

namespace unitaryGroup


end unitaryGroup

end Ring

section Field

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : HermForm K V}

end Field

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (h : HermForm ℂ V)

variable {h}

end Complex

end HermForm

universe u v

structure HermModule (R : Type u) [CommRing R] [StarRing R] where

  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module R carrier]

  form : HermForm R carrier

attribute [instance] HermModule.addCommGroup HermModule.module

structure HermSpace (K : Type u) [Field K] [StarRing K] where

  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module K carrier]
  [finite : FiniteDimensional K carrier]

  form : HermForm K carrier
  nondegenerate : form.Nondegenerate

attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite

class IsStarFixed (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E] :
    Prop where
  star_algebraMap : ∀ a : F, star (algebraMap F E a) = algebraMap F E a

attribute [simp] IsStarFixed.star_algebraMap

section IsStarFixed

variable (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E]

variable [IsStarFixed F E]

variable {F E}

end IsStarFixed

def StarTensor (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E]
    [Algebra F A] : Type _ := E ⊗[F] A

namespace StarTensor

section NoStar

variable (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]


variable {F E A}


variable {B C : Type*} [CommRing B] [CommRing C] [Algebra F B] [Algebra F C]



end NoStar

section Star

variable {F E A : Type*} [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
  [StarRing E] [IsStarFixed F E]


variable {B : Type*} [CommRing B] [Algebra F B]

end Star

end StarTensor

section RingOfIntegers

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]


end RingOfIntegers

section CM

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]

variable {E}

@[simp] theorem complexEmbedding_star (τ : E →+* ℂ) (x : E) : τ (star x) = star (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x


variable (E) in
theorem exists_star_ne : ∃ x : E, star x ≠ x := by
  by_contra! H
  exact IsCMField.complexConj_ne_one E (AlgEquiv.ext H)

noncomputable instance : StarRing (𝓞 E) where
  star := IsCMField.ringOfIntegersComplexConj E
  star_involutive x := RingOfIntegers.ext (star_star (x : E))
  star_mul x y := by rw [map_mul, mul_comm]
  star_add x y := map_add _ x y


variable (E) in
abbrev CMTensor (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A] : Type _ :=
  StarTensor (maximalRealSubfield E) E A

namespace CMTensor

variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A]

end CMTensor

end CM

end GlobalTheory
