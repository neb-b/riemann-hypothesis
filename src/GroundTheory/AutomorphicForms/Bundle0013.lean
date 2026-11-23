module

public import Mathlib
public import GroundTheory.AutomorphicForms.HermitianOrthogonal
public import GroundTheory.AutomorphicForms.StableConjCyclic
public import GroundTheory.AutomorphicForms.Bundle0011

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.StableConjTorus
section
namespace GroundTheory.Automorphic

open Module

section CommuteField

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]

theorem commute_of_commute_of_separable_charpoly {f g g' : Module.End E V}
    (hf : f.charpoly.Separable) (hg : Commute f g) (hg' : Commute f g') : Commute g g' := by
  classical
  set n := finrank E V
  let b : Basis (Fin n) E V := Module.finBasis E V
  let K := AlgebraicClosure E
  let φ : E →+* K := algebraMap E K
  let Φ : Module.End E V →+* Matrix (Fin n) (Fin n) K :=
    φ.mapMatrix.comp (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toRingHom
  let Ψ : Matrix (Fin n) (Fin n) K →+* Module.End K (Fin n → K) :=
    (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).toRingEquiv.toRingHom
  have hsep : (Ψ (Φ f)).charpoly.Separable := by
    change (Matrix.toLin' ((LinearMap.toMatrix b b f).map φ)).charpoly.Separable
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    exact hf.map
  have hc := commute_of_commute_of_separable hsep ((hg.map Φ).map Ψ) ((hg'.map Φ).map Ψ)
  have hinj : Function.Injective (Ψ.comp Φ) := by
    intro x y hxy
    have h1 : Φ x = Φ y := (Matrix.toLinAlgEquiv' (R := K) (n := Fin n)).injective hxy
    have h2 : LinearMap.toMatrixAlgEquiv b x = LinearMap.toMatrixAlgEquiv b y := by
      ext i j
      exact φ.injective (congrFun (congrFun h1 i) j)
    exact (LinearMap.toMatrixAlgEquiv b).injective h2
  change g * g' = g' * g
  apply hinj
  rw [map_mul, map_mul]
  exact hc.eq

end CommuteField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V]

namespace HermitianForm

variable (h : HermitianForm F E V)

noncomputable def adjoint (A : Module.End E V) : Module.End E V where
  toFun y := (Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)
  map_add' x y := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, map_add (f := _), LinearMap.add_comp]
  map_smul' c x := by
    apply h.nonsingular.1
    simp only [Equiv.ofBijective_apply_symm_apply, LinearMap.map_smulₛₗ, LinearMap.smul_comp,
      RingHom.id_apply]

theorem toSesq_adjoint_left (A : Module.End E V) (y x : V) :
    h.toSesq (h.adjoint A y) x = h.toSesq y (A x) := by
  change h.toSesq ((Equiv.ofBijective _ h.nonsingular).symm ((h.toSesq y).comp A)) x = _
  rw [Equiv.ofBijective_apply_symm_apply (⇑h.toSesq) h.nonsingular]
  rfl

theorem eq_adjoint_iff (A B : Module.End E V) :
    B = h.adjoint A ↔ ∀ y x, h.toSesq (B y) x = h.toSesq y (A x) := by
  refine ⟨fun hB y x => hB ▸ h.toSesq_adjoint_left A y x, fun hB => LinearMap.ext fun y => ?_⟩
  apply h.nonsingular.1
  ext x
  rw [hB, toSesq_adjoint_left]

theorem adjoint_mul (A B : Module.End E V) : h.adjoint (A * B) = h.adjoint B * h.adjoint A := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rw [Module.End.mul_apply, toSesq_adjoint_left, toSesq_adjoint_left, Module.End.mul_apply]

theorem adjoint_one : h.adjoint 1 = 1 := by
  symm
  rw [eq_adjoint_iff]
  intro y x
  rfl

noncomputable def adjointEquiv (g : V ≃ₗ[E] V) : V ≃ₗ[E] V where
  toLinearMap := h.adjoint g.toLinearMap
  invFun := h.adjoint g.symm.toLinearMap
  left_inv x := by
    change (h.adjoint g.symm.toLinearMap * h.adjoint g.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.toLinearMap * g.symm.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl
  right_inv x := by
    change (h.adjoint g.toLinearMap * h.adjoint g.symm.toLinearMap) x = x
    rw [← adjoint_mul]
    have : g.symm.toLinearMap * g.toLinearMap = 1 := by
      ext y; simp
    rw [this, adjoint_one]
    rfl

end HermitianForm

section Stable

variable [FiniteDimensional E V]

def IsRegularSemisimple (γ : V ≃ₗ[E] V) : Prop :=
  (γ.toLinearMap).charpoly.Separable

def torusE (γ : V ≃ₗ[E] V) : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.centralizer {γ}



def TorusE (γ : V ≃ₗ[E] V) : Type _ := torusE γ

namespace TorusE

variable {γ : V ≃ₗ[E] V}




variable [Fact (IsRegularSemisimple γ)]

end TorusE

end Stable

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.UnitaryGroupEquations
section
namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)

section Coordinates

variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]

noncomputable def matrixCoords : Matrix ι ι (R ⊗[F] E) ≃ (ι × ι × κ → R) where
  toFun g p := (Algebra.TensorProduct.basis R b).repr (g p.1 p.2.1) p.2.2
  invFun x i j := (Algebra.TensorProduct.basis R b).repr.symm
    (Finsupp.equivFunOnFinite.symm fun k => x (i, j, k))
  left_inv g := by
    ext i j
    simp
  right_inv x := by
    funext ⟨i, j, k⟩
    simp

omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem matrixCoords_apply (g : Matrix ι ι (R ⊗[F] E)) (i j : ι) (k : κ) :
    matrixCoords b R g (i, j, k) = (Algebra.TensorProduct.basis R b).repr (g i j) k := rfl


variable {R}


omit [Algebra.IsQuadraticExtension F E] [Fintype κ] in
theorem repr_tensorMap (f : R →ₐ[F] S) (z : R ⊗[F] E) (k : κ) :
    (Algebra.TensorProduct.basis S b).repr
        (TensorProduct.map f.toLinearMap (LinearMap.id : E →ₗ[F] E) z) k =
      f ((Algebra.TensorProduct.basis R b).repr z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.mapRange_apply]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]


omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem matrixCoords_map (f : R →ₐ[F] S) (g : Matrix ι ι (R ⊗[F] E)) :
    matrixCoords b S (g.map (TensorProduct.map f.toLinearMap
      (LinearMap.id : E →ₗ[F] E))) =
      f ∘ matrixCoords b R g := by
  funext ⟨i, j, k⟩
  rw [Function.comp_apply, matrixCoords_apply, matrixCoords_apply, Matrix.map_apply, repr_tensorMap]

end Coordinates

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.UnitarySplit
section
namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable (F : Type*) [Field F]

variable {F}

section Split

variable (F) (R : Type*) [CommRing R] [Algebra F R]

noncomputable def splitEquiv : R ⊗[F] (F × F) ≃ₐ[R] R × R :=
  (Algebra.TensorProduct.prodRight F R R F F).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.rid F R R) (Algebra.TensorProduct.rid F R R))

variable {F R}



variable {ι : Type*} [Fintype ι] [DecidableEq ι]



variable (H : Matrix ι ι (F × F))






end Split

section SplitFunctor

open CategoryTheory

universe u

variable (F : Type u) [Field F] (ι : Type u) [Fintype ι] [DecidableEq ι]

variable {F ι}

end SplitFunctor

end GroundTheory.Automorphic
end

