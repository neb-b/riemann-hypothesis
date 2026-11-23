module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0009
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.FieldExtensionBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionResolution
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionTrivialCases
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SmoothBaseChangeCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxOrderReduction

private theorem orderAtBaseFieldChangeInvariance_of_geometryHypotheses (hG : PrincipalizationGeometryHypotheses.{u}) :
    OrderAtBaseFieldChangeInvariance.{u} := by
  intro T hT L _ _ f B b pB hpB IB EB hTB Q a b' hpb A y
  subst hpB
  have hQ : IsPullback
      (Limits.pullback.fst b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
      (Limits.pullback.snd b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))) b
      (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    IsPullback.of_hasPullback _ _
  let E : Q ≅ Limits.pullback (b ≫ T.structMap) (specMapOfFieldHom T.base L f) :=
    hpb.isoIsPullback B (Limits.pullback T.structMap (specMapOfFieldHom T.base L f)) hQ ≪≫
      Limits.pullbackRightPullbackFstIso T.structMap (specMapOfFieldHom T.base L f) b
  have he : E.hom ≫ Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f) = a := by
    simp [E, Iso.trans_hom]
  have hcomp : A.comap a =
      (A.comap
        (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f))).comap E.hom := by
    rw [← he]
    simp [Scheme.IdealSheafData.comap_comp]
  have h1 : orderAt (A.comap a) y
      = orderAt (A.comap (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)))
          (E.hom.base y) := by
    rw [hcomp]
    exact FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isIso E.hom _ y
  have h2 := hG.orderAt_baseChange
    (MarkedIdealWithBoundary.mk T.base B (b ≫ T.structMap) IB T.mult EB) hTB L f A (E.hom.base y)
  have h3 : orderAt A
      ((Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)).base (E.hom.base y))
      = orderAt A (a y) := by
    rw [← he]
    simp
  exact h1.trans (h2.trans h3)

theorem monomialPrincipalization_spec (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) : MonomialPrincipalizationHypotheses hinv := by
  have h := isLocallyMonomialPrincipalization_monomialPrincipalization hG.monomialInputs hinv
      (orderAtBaseFieldChangeInvariance_of_geometryHypotheses hG) (fun _ => True)
  exact
    { cert := fun T hTm i hi => h.cert T hTm trivial i hi
      center_nonempty := fun T hTm i hi => h.center_nonempty T hTm trivial i hi
      resolves := fun T hTm => h.resolves T hTm trivial
      trivial_of_coSupport_empty := fun T hTm hc => h.trivial_of_coSupport_empty T hTm trivial hc }

theorem isMaxOrderReduction_orderReductionSeq (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) (fun T => orderReductionSeq hinv T (principalizationOfDimLe T A)) A := by
  have hmon : MonomialPrincipalizationHypotheses hinv := monomialPrincipalization_spec hG hinv
  refine
    { cert := fun T hT hdim i hi => certificate_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      orderRed_equiv := fun T hT hdim hE hord =>
        orderReductionSeq_isomorphic_of_boundary_nil hG hinv hmon hspec hT hdim hE hord
      center_nonempty := fun T hT hdim i hi =>
        center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      resolves := fun T hT hdim => isResolution_orderReductionSeq hG hinv hmon hspec hT hdim
      trivial_of_coSupport_empty := fun T hT hdim hc =>
        orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A hc
      base_change := ?_
      base_change_strict := ?_
      smooth_pullback := ?_
      smooth_pullback_strict := ?_ }
  · intro T hT hdim L _ _ f E' hE hT' hdim'
    exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
      (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
      (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
  · intro T hT hdim L _ _ f E' hE hT' hdim'
    have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
      (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
      (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
    have hsurj : AlgebraicGeometry.Surjective (baseChangeProj T L f) :=
      instSurjectivePullbackFstSpecMapField T.base L f T.scheme T.structMap
    exact hp.isStrictPullback_of_surjective fun i hi =>
      (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
        (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)
  · intro T hT hdim Y q h hsm hq E' hE hT' hdim'
    have := hsm
    exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
      hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)
  · intro T hT hdim Y q h hsm hsurj hq E' hE hT' hdim'
    have := hsm
    have := hsurj
    have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
      hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)
    exact hp.isStrictPullback_of_surjective fun i hi =>
      (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
        (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)

theorem isMaxOrderReduction_canonicalAlgorithmRules (hG : PrincipalizationGeometryHypotheses.{u})
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (n : ℕ) (A B : PrincipalizationAssignment.{u})
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) ((canonicalAlgorithmRules hres).maxOrderFamily A) A :=
  isMaxOrderReduction_orderReductionSeq hG comapIsoInvariance n A B hspec

end MaxOrderReduction

end FunctorialResolution.EmbeddedResolution

end
