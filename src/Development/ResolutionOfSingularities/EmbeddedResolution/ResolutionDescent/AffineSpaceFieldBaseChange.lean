module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0010
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem exists_baseChangeAffineSpaceIso (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : Type u) :
    ∃ e : baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n,
      e.hom ≫ affineSpaceIndexedByToSpec K n = baseChangeToSpec (affineSpaceIndexedByToSpec k n) K := by
  have hA : IsPullback (baseChangeProjection (affineSpaceIndexedByToSpec k n) K)
      (baseChangeToSpec (affineSpaceIndexedByToSpec k n) K) (affineSpaceIndexedByToSpec k n)
      (specMapAlgebraMap k K) := IsPullback.of_hasPullback _ _
  have hB : IsPullback (AlgebraicGeometry.AffineSpace.map n (specMapAlgebraMap k K))
      (affineSpaceIndexedByToSpec K n) (affineSpaceIndexedByToSpec k n) (specMapAlgebraMap k K) :=
    AlgebraicGeometry.AffineSpace.isPullback_map (n := n) (specMapAlgebraMap k K)
  exact ⟨hA.isoIsPullback _ _ hB, hA.isoIsPullback_hom_snd _ _ hB⟩

def baseChangeAffineSpaceIso (k K : Type u) [Field k] [Field K] [Algebra k K] (n : Type u) :
    baseChange (affineSpaceIndexedByToSpec k n) K ≅ affineSpaceIndexedBy K n :=
  (exists_baseChangeAffineSpaceIso k K n).choose

@[simp]
theorem baseChangeAffineSpaceIso_hom_comp_toSpec (k K : Type u) [Field k] [Field K] [Algebra k K]
    (n : Type u) :
    (baseChangeAffineSpaceIso k K n).hom ≫ affineSpaceIndexedByToSpec K n =
      baseChangeToSpec (affineSpaceIndexedByToSpec k n) K :=
  (exists_baseChangeAffineSpaceIso k K n).choose_spec

def affineSpaceChartBaseChangeAmbientIso
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK).ambient ≅
      affineSpaceIndexedBy K (ULift.{u, 0} (Fin (hemb k Y pY).choose)) :=
  baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin (hemb k Y pY).choose))

def affineSpaceChartBaseChangePresentation
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k K : Type u) [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    (hker : NonzeroOnComponents
      (Scheme.Hom.ker ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChangeEmb K)))
    (hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).ambientStruct K) []) :
    ClosedEmbeddingIntoAffineSpace
      ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK) :=
  presentationOfAmbientIso hsm
    ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).baseChange K hker hsncK)
    (hemb k Y pY).choose
    (affineSpaceChartBaseChangeAmbientIso hemb hsnc hsm k K Y pY hker hsncK)
    (by exact baseChangeAffineSpaceIso_hom_comp_toSpec k K (ULift.{u, 0} (Fin (hemb k Y pY).choose)))

end FunctorialResolution.EmbeddedResolution

end
