module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitCoboundaryOfMulCocycleStatement
section
theorem _root_.GlobalTheory.T.exists_unit_coboundary_of_cocycle_addMonoidAlgebra : ∀ (B : Type) [CommRing B] (I : Ideal B), IsNilpotent I → ∀ (X : Type) [AddCommGroup X] (f : AddMonoidAlgebra B (X × X)), (∀ p, (f - 1).coeff p ∈ I) → AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.1, p.2)) f * AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, (0 : X))) f = AddMonoidAlgebra.mapDomain (fun p : X × X => (p.1, p.2, p.2)) f * AddMonoidAlgebra.mapDomain (fun p : X × X => ((0 : X), p.1, p.2)) f → ∃ g : (AddMonoidAlgebra B X)ˣ, (∀ x, (g.val - 1).coeff x ∈ I) ∧ f * AddMonoidAlgebra.mapDomain (fun x : X => (x, x)) g.val = AddMonoidAlgebra.mapDomain (fun x : X => (x, (0 : X))) g.val * AddMonoidAlgebra.mapDomain (fun x : X => ((0 : X), x)) g.val := by
  first | exact @GlobalTheory.exists_unit_coboundary_of_mul_cocycle | exact GlobalTheory.exists_unit_coboundary_of_mul_cocycle | (intros; apply GlobalTheory.exists_unit_coboundary_of_mul_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isIntegral_tensor_left_of_smooth_grpObj (S : Scheme.{0}) (B T : Over S) [GrpObj B]
    [Smooth B.hom] [GeometricallyConnected B.hom] [IsIntegral T.left] :
    IsIntegral (T ⊗ B).left :=
  isIntegral_of_isPullback_of_smooth (IsPullback.of_hasPullback T.hom B.hom).flip

end GlobalTheory
end

