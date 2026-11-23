module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.EtaleCohomology.EtaleSheaves.Bundle0038
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0017
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0040
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0033
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CurvePicardOfSelmerPicardOfModelCurve
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.curve_picard_of_selmerPicard_of_modelCurve :
    LateralTheory.E.LeafPicCut.LeafSelPic → LateralTheory.E.LeafCurveVCut.LeafModelCurve → LateralTheory.E.E4.LeafPic := by
  intro hSel hModel hH q _ k B _ _ _ _ _ _ hq
  by_cases hB : IsField B
  · letI := hB.toField
    haveI : Subsingleton (CommRing.Pic B) := inferInstance
    exact Finite.of_subsingleton
  · haveI hK : IsFunctionField k (FractionRing B) := UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType k B hB
    obtain ⟨u, hu, hfd⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := FractionRing B)
    obtain ⟨C0, c0, x, ψ, hc, hx, hψ⟩ := hModel k (FractionRing B) u hu hfd
    haveI : IsIntegral C0 := hc.1
    obtain rfl : x = genericPoint C0 := hx.eq (genericPoint_spec C0)
    letI : Algebra k C0.functionField :=
      (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ).hom.toAlgebra
    letI : Algebra (FractionRing B) C0.functionField := (Spec.preimage ψ).hom.toAlgebra
    haveI : IsScalarTower k (FractionRing B) C0.functionField := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have heq : Spec.map (CommRingCat.ofHom (algebraMap k C0.functionField)) =
        C0.fromSpecStalk (genericPoint C0) ≫ c0 := by
      change Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing B)) ≫ Spec.preimage ψ) = _
      rw [Spec.map_comp, Spec.map_preimage, hψ]
    obtain ⟨hF, hch⟩ := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit hH q k hq c0 hc heq
    haveI := hF
    exact UpperTheory.finite_pic_torsion_of_finite_kummerSelmer hSel k B q
      (UpperTheory.finite_kummerSelmer_of_finite_extension k (FractionRing B) C0.functionField q hq (UpperTheory.finite_kummerSelmer_of_charts k _ q hch))
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFiniteOfIsPullbackFpqc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.isFinite_of_isPullback_fpqc :
    ∀ {X Y X' Y' : Scheme.{0}} (a : X' ⟶ X) (q : X' ⟶ Y') (p : X ⟶ Y) (t : Y' ⟶ Y), IsPullback a q p t → Surjective t → Flat t → QuasiCompact t → IsFinite q → IsFinite p := by
  intro X Y X' Y' a q p t h h₁ h₂ h₃ hq
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have ht : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) t :=
    ⟨⟨h₁, h₂⟩, h₃⟩
  have hA : IsAffineHom p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) h.flip ht inferInstance
  have hU : UniversallyClosed p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip ht inferInstance
  have hL : LocallyOfFiniteType p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip ht inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hU, hA⟩, hL⟩
end

