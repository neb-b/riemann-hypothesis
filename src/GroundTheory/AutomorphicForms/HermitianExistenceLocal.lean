module

public import Mathlib
public import GroundTheory.AutomorphicForms.HermitianValues
public import GroundTheory.AutomorphicForms.Bundle0016

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] {ι : Type*} [Fintype ι] [DecidableEq ι]


end Transport

section Split

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Split

section OfGram

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def HermitianForm.ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) : HermitianForm F A (ι → A) where
  toSesq := LinearMap.mk₂'ₛₗ (conjHom F A) (RingHom.id A)
    (fun x y => ∑ i, ∑ j, conj F A (x i) * H i j * y j)
    (fun x x' y => by
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, conjHom_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)
  isSymm := ⟨fun x y => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.mk₂'ₛₗ_apply, conjHom_apply, map_sum, map_mul, conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : conj F A (H j i) = H i j := congrFun (congrFun hH i) j
    rw [this]
    ring⟩
  nonsingular := by
    refine bijective_of_injective_sesq _ ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    have hv : Matrix.vecMul (fun i => conj F A (x i)) H = 0 := by
      funext j
      have := LinearMap.congr_fun hx (Pi.single j 1)
      rw [LinearMap.mk₂'ₛₗ_apply] at this
      simpa [vecMul, dotProduct, Pi.single_apply] using this
    have hinj := (Matrix.vecMul_injective_iff_isUnit (A := H)).2
      ((Matrix.isUnit_iff_isUnit_det H).2 hu)
    have h0 := hinj (hv.trans (Matrix.zero_vecMul H).symm)
    funext i
    have := congrFun h0 i
    rw [← conj_conj (F := F) (x i), this]
    simp

theorem HermitianForm.ofGram_apply (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) (x y : ι → A) :
    (HermitianForm.ofGram H hH hu).toSesq x y = ∑ i, ∑ j, conj F A (x i) * H i j * y j :=
  rfl

theorem gram_ofGram (H : Matrix ι ι A) (hH : IsHermitianFor (conjHom F A) H)
    (hu : IsUnit H.det) :
    gram (HermitianForm.ofGram H hH hu).toSesq (Pi.basisFun A ι) = H := by
  ext i j
  rw [gram_apply, HermitianForm.ofGram_apply]
  simp [Pi.single_apply]

end OfGram

section LocalField

variable {F A : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A] [Algebra.IsSeparable F A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end LocalField

section Diagonal

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]

end Diagonal

end GroundTheory.Automorphic
