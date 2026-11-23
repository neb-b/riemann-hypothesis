module

public import Mathlib

@[expose] public section

open TensorProduct PiTensorProduct

namespace GlobalTheory

noncomputable section

universe u v w

variable {A : Type u} [CommRing A] {σ : Type w} [Fintype σ] [DecidableEq σ] {X : σ → Type v}
  [∀ s, CommRing (X s)] [∀ s, Algebra A (X s)] {S : Type*} [CommRing S] [Algebra A S]

def piTensorLift (f : ∀ s, X s →ₐ[A] S) : (⨂[A] s, X s) →ₐ[A] S :=
  liftAlgHom ((MultilinearMap.mkPiAlgebra A σ S).compLinearMap fun s => (f s).toLinearMap)
    (by simp) (fun x y => by simp [Finset.prod_mul_distrib])


omit [DecidableEq σ] in
@[simp] theorem piTensorLift_tprod (f : ∀ s, X s →ₐ[A] S) (x : ∀ s, X s) :
    piTensorLift f (tprod A x) = ∏ s, f s (x s) := by
  refine (PiTensorProduct.lift.tprod x).trans ?_
  simp

@[simp] theorem piTensorLift_comp_single (f : ∀ s, X s →ₐ[A] S) (s : σ) :
    (piTensorLift f).comp (singleAlgHom s) = f s := by
  ext x
  rw [AlgHom.comp_apply, singleAlgHom_apply, piTensorLift_tprod,
    Finset.prod_eq_single s (fun t _ ht => by simp [Pi.mulSingle_eq_of_ne ht]) (by simp)]
  simp

theorem piTensorLift_single (f : ∀ s, X s →ₐ[A] S) (s : σ) (x : X s) :
    piTensorLift f (singleAlgHom s x) = f s x := congr($(piTensorLift_comp_single f s) x)


end

end GlobalTheory
