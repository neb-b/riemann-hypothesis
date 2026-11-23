module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedBlowupsFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldExtensionEtaleCover
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0009
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0010
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRuleLocality
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem principalizationAlgorithm_toSequenceOfBlowups_congr_ideal (A : PrincipalizationAlgorithm.{u}) (k : Type u) [Field k] [CharZero k]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p]
    (I J : X.IdealSheafData) (hIJ : I = J)
    (hI : NonzeroOnComponents I) (hJ : NonzeroOnComponents J)
    (E : List X.IdealSheafData) (hE hE' : InStrictNormalCrossingPosition p E) :
    (A k X p I hI E hE).toSequenceOfBlowups = (A k X p J hJ E hE').toSequenceOfBlowups := by
  subst hIJ
  rfl

private theorem isPullbackSequenceOfBlowups_congr_left {X X' : Scheme.{u}} {φ : X' ⟶ X}
    {s1 s2 : SequenceOfBlowups X'} {t : SequenceOfBlowups X} (h : s1 = s2) (H : IsPullbackBlowupSequence φ s1 t) :
    IsPullbackBlowupSequence φ s2 t := by
  subst h
  exact H

theorem embeddedResolutionRule_isPullbackBlowupSequence_of_smooth
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p'] [AlgebraicGeometry.QuasiCompact p']
    [AlgebraicGeometry.IsReduced Y'] [AlgebraicGeometry.IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) [AlgebraicGeometry.Smooth φ] (ψ : Y' ⟶ Y)
    (hφ : φ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ψ φ D.emb) :
    IsPullbackBlowupSequence ψ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have : AlgebraicGeometry.Flat φ := inferInstance
  have : AlgebraicGeometry.QuasiCompact D.emb := inferInstance
  have : AlgebraicGeometry.QuasiCompact D'.emb := inferInstance
  have hker : D'.emb.ker = D.emb.ker.comap φ :=
    ker_eq_comap_ker_of_isPullback_of_flat hsq.flip
  have hI' : NonzeroOnComponents (D.emb.ker.comap φ) := hker ▸ D'.nonzeroOnComponents_ker
  have hE' : InStrictNormalCrossingPosition D'.ambientStruct
      (List.map (fun Z => Z.comap φ) ([] : List D.ambient.IdealSheafData)) := D'.sncEmpty
  have h0 := hA.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
      D.nonzeroOnComponents_ker [] D.sncEmpty D'.ambient D'.ambientStruct φ hφ hI' hE'
  have hpb : IsPullbackBlowupSequence φ (D'.toEmbeddedBlowupSequence A).ambientSeq (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal A k D'.ambient D'.ambientStruct
        (D.emb.ker.comap φ) D'.emb.ker hker.symm hI' _ [] hE' _) h0
  have hflat2 : AlgebraicGeometry.Flat
      (show (D'.toEmbeddedBlowupSequence A).ambient ⟶ (D.toEmbeddedBlowupSequence A).ambient from φ) :=
    (inferInstance : AlgebraicGeometry.Flat φ)
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A) (D'.toEmbeddedBlowupSequence A) φ ψ
    hsq.flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _

theorem embeddedResolutionRule_isCompatibleWithSmoothAmbientMaps
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A) :
    EmbeddedResolutionRule.IsCompatibleWithSmoothAmbientMaps (embeddedResolutionRuleOfPrincipalization A hw) := by
  intro k _ _ Y Y' p p' _ _ _ _ _ _ _ _ D D' φ _ ψ hφ hsq
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' φ ψ hφ hsq

theorem embeddedResolutionRule_isStrictPullbackBlowupSeq_baseChange
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    (D : EmbeddingDatum k Y p) (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [AlgebraicGeometry.IsReduced (baseChange p K)]
    (hker : NonzeroOnComponents (D.baseChangeEmb K).ker)
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      ([] : List (baseChange D.ambientStruct K).IdealSheafData)) :
    haveI : AlgebraicGeometry.IsAffine (baseChange p K) := isAffine_baseChange p K
    haveI : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
      locallyOfFiniteType_baseChangeToSpec p K
    haveI : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
      quasiCompact_baseChangeToSpec p K
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (embeddedResolutionRuleOfPrincipalization A hw K (baseChange p K) (baseChangeToSpec p K)
        (D.baseChange K hker hsnc))
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have : AlgebraicGeometry.IsAffine (baseChange p K) := isAffine_baseChange p K
  have : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
    locallyOfFiniteType_baseChangeToSpec p K
  have : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
    quasiCompact_baseChangeToSpec p K
  have : AlgebraicGeometry.IsAffine (baseChange D.ambientStruct K) :=
    EmbeddingDatum.isAffine_baseChange_ambientToSpec D K
  have : AlgebraicGeometry.Smooth (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec D K
  have : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.locallyOfFiniteType_baseChangeToSpec_ambientToSpec D K
  have : AlgebraicGeometry.QuasiCompact (baseChangeToSpec D.ambientStruct K) :=
    EmbeddingDatum.quasiCompact_baseChangeToSpec_ambientToSpec D K
  have : AlgebraicGeometry.Flat (baseChangeProjection D.ambientStruct K) := inferInstance
  have : AlgebraicGeometry.Surjective (baseChangeProjection p K) := inferInstance
  have : AlgebraicGeometry.QuasiCompact D.emb := inferInstance
  have : AlgebraicGeometry.QuasiCompact (D.baseChangeEmb K) := inferInstance
  show IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (embeddedResolutionRuleOfPrincipalization A hw K (baseChange p K) (baseChangeToSpec p K)
        (D.baseChange K hker hsnc))
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D)
  have hkerbc : (D.baseChangeEmb K).ker
      = D.emb.ker.comap (baseChangeProjection D.ambientStruct K) :=
    ker_eq_comap_ker_of_isPullback_of_flat (D.isPullback_baseChangeEmb K).flip
  have hI' : NonzeroOnComponents (D.emb.ker.comap (baseChangeProjection D.ambientStruct K)) :=
    hkerbc ▸ hker
  have hE' : InStrictNormalCrossingPosition (baseChangeToSpec D.ambientStruct K)
      (List.map (fun Z => Z.comap (baseChangeProjection D.ambientStruct K))
        ([] : List D.ambient.IdealSheafData)) := hsnc
  have h0 := hA.base_change k D.ambient D.ambientStruct D.emb.ker D.nonzeroOnComponents_ker
      [] D.sncEmpty K (algebraMap k K) hI' hE'
  have hpb : IsPullbackBlowupSequence (baseChangeProjection D.ambientStruct K)
      ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A).ambientSeq
      (D.toEmbeddedBlowupSequence A).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups]
    exact isPullbackSequenceOfBlowups_congr_left
      (principalizationAlgorithm_toSequenceOfBlowups_congr_ideal A K (baseChange D.ambientStruct K)
        (baseChangeToSpec D.ambientStruct K)
        (D.emb.ker.comap (baseChangeProjection D.ambientStruct K)) (D.baseChangeEmb K).ker
        hkerbc.symm hI' _ [] hE' _) h0
  have hflat2 : AlgebraicGeometry.Flat
      (show ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A).ambient ⟶
          (D.toEmbeddedBlowupSequence A).ambient from baseChangeProjection D.ambientStruct K) :=
    (inferInstance : AlgebraicGeometry.Flat (baseChangeProjection D.ambientStruct K))
  rw [embeddedResolutionRuleOfPrincipalization_apply, embeddedResolutionRuleOfPrincipalization_apply]
  refine IsPullbackBlowupSequence.isStrictPullback_of_surjective ?_ ?_
  · exact (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence A)
      ((D.baseChange K hker hsnc).toEmbeddedBlowupSequence A) (baseChangeProjection D.ambientStruct K)
      (baseChangeProjection p K) (D.isPullback_baseChangeEmb K).flip hpb).isPullbackBlowupSequence_inducedBlowupsWithoutIso _ _
  · intro i hi
    exact SequenceOfBlowups.withoutIsoBlowups_center_ne_top ((D.toEmbeddedBlowupSequence A).inducedBlowups _) hi

theorem embeddedResolutionRule_isCompatibleWithFieldBaseChange
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A) :
    EmbeddedResolutionRule.IsCompatibleWithFieldBaseChange (embeddedResolutionRuleOfPrincipalization A hw) := by
  intro k _ _ Y p _ _ _ _ D K _ _ _ _ hker hsnc
  exact embeddedResolutionRule_isStrictPullbackBlowupSeq_baseChange A hA hw k Y p D K hker hsnc

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelection
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure PresentedSelection where
  sel : EmbeddingChoice.{u}
  pres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], ClosedEmbeddingIntoAffineSpace (sel k Y p)
  basePres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    (hker : NonzeroOnComponents (Scheme.Hom.ker ((sel k Y p).baseChangeEmb K)))
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec (sel k Y p).ambientStruct K) []),
    ClosedEmbeddingIntoAffineSpace ((sel k Y p).baseChange K hker hsnc)

theorem isCompatibleWithFieldBaseChange_toAffineResolutionRule (R : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u}) (hinv : R.IsIndependentOfPresentedEmbedding)
    (hfield : R.IsCompatibleWithFieldBaseChange)
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithFieldBaseChange (R.toAffineResolutionRule C.sel) := by
  intro k _ _ Y p _ _ _ _ K _ _ _ _ _
  have hlft : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
    locallyOfFiniteType_baseChangeToSpec p K
  have hqcb : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
    quasiCompact_baseChangeToSpec p K
  have hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      ([] : List (baseChange (C.sel k Y p).ambientStruct K).IdealSheafData) :=
    hsnc K (baseChange (C.sel k Y p).ambientStruct K)
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      (EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec (C.sel k Y p) K)
  have hsq : IsPullback (baseChangeProjection p K) ((C.sel k Y p).baseChangeEmb K)
      (C.sel k Y p).emb (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    (EmbeddingDatum.isPullback_baseChangeEmb (C.sel k Y p) K).flip
  have hflat : AlgebraicGeometry.Flat (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    inferInstance
  have hqc1 : AlgebraicGeometry.QuasiCompact (C.sel k Y p).emb := inferInstance
  have hqc2 : AlgebraicGeometry.QuasiCompact ((C.sel k Y p).baseChangeEmb K) :=
    quasiCompact_of_isPullback hsq
  have hkerK : NonzeroOnComponents (Scheme.Hom.ker ((C.sel k Y p).baseChangeEmb K)) := by
    rw [ker_eq_comap_ker_of_isPullback_of_flat hsq]
    exact NonzeroOnComponents.comap_of_flat (C.sel k Y p).nonzeroOnComponents_ker _
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback (hfield k Y p (C.sel k Y p) K hkerK hsncK)
    (hinv K (baseChange p K) (baseChangeToSpec p K)
      ((C.sel k Y p).baseChange K hkerK hsncK)
      (C.sel K (baseChange p K) (baseChangeToSpec p K))
      (C.basePres k Y p K hkerK hsncK)
      (C.pres K (baseChange p K) (baseChangeToSpec p K)))

def affineSpacePresentedSelection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    PresentedSelection.{u} where
  sel := affineSpaceEmbeddingChoice hemb hsncE hsm
  pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
  basePres := fun k _ _ Y p _ _ _ _ K _ _ _ _ _ =>
    let n := (hemb k Y p).choose
    presentationOfAmbientIso hsm _ n
      (baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin n)))
      (baseChangeAffineSpaceIso_hom_comp_toSpec k K (ULift.{u, 0} (Fin n)))

@[simp]
theorem affineSpacePresentedSelection_selection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    (affineSpacePresentedSelection hemb hsncE hsm).sel = affineSpaceEmbeddingChoice hemb hsncE hsm :=
  rfl

end FunctorialResolution.EmbeddedResolution

end
end

