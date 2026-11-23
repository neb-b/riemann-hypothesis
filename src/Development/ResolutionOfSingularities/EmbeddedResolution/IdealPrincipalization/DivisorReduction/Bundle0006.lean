module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0006
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsSmoothPullback
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem smooth_of_isPullback (X Y S S' : Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X)
    (ψ : S' ⟶ S) (hpb : IsPullback σ' ψ φ σ) (hφ : AlgebraicGeometry.Smooth φ) :
    AlgebraicGeometry.Smooth ψ :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Smooth) hpb hφ

theorem orderAtLeastLocus_comap_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    (_hq : h ≫ T.structMap = q) (m : ℕ) :
    orderAtLeastLocus (T.ideal.comap h) m = ⇑h ⁻¹' orderAtLeastLocus T.ideal m := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  exact FunctorialResolution.EmbeddedResolution.orderAtLeastLocus_comap T.base T.structMap h T.ideal m

private theorem withBoundary_withBoundary (T : MarkedIdealWithBoundary.{u})
    (E F : List T.scheme.IdealSheafData) :
    (T.withBoundary E).withBoundary F = T.withBoundary F := rfl

private theorem isAdmissible_of_withBoundary_isAdmissible (S : MarkedIdealWithBoundary.{u})
    (E : List S.scheme.IdealSheafData) (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary E)
    (hV : (S.withBoundary E).IsAdmissible) : S.IsAdmissible := by
  have h1 : ((S.withBoundary E).withBoundary S.boundary).IsAdmissible :=
    MarkedIdealWithBoundary.validOfSameNontrivialBoundary _ _ hV hBE.symm
  rw [withBoundary_withBoundary, MarkedIdealWithBoundary.withBoundary_self] at h1
  exact h1

theorem isAdmissible_pullbackAlong_of_withBoundary_isAdmissible :
    ∀ (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
      (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible → (T.pullbackAlong Y q h).IsAdmissible := by
  intro T Y q h E' hBE hV
  exact isAdmissible_of_withBoundary_isAdmissible (T.pullbackAlong Y q h) E' hBE hV

theorem containedComponentsIdeal_pullbackAlong_of_isAdmissible_pullbackAlong
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (T : MarkedIdealWithBoundary.{u}) (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base))
      (h : Y ⟶ T.scheme) (E' : List Y.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
        ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible → (T.pullbackAlong Y q h).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV'
  have : AlgebraicGeometry.Smooth h := hsm
  have hj' : j < (T.pullbackAlong Y q h).boundary.length := by
    change j < (T.boundary.map (fun D => D.comap h)).length
    simpa only [List.length_map] using hj
  have hVal : (T.pullbackAlong Y q h).IsAdmissible := hvbr T Y q h E' hBE hV'
  rw [containedComponentsIdeal_withBoundary T j Y q h E' hjE hj' htake]
  exact hfacts.preIdeal_pullbackAlong T hV Y q h hq hVal j hj hj'

theorem containedComponentsIdeal_pullbackAlong_of_smooth {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} (hfacts : DivisorReductionTerminationProperties hres hno) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
              containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (containedComponentsIdeal T j hj).comap h :=
  containedComponentsIdeal_pullbackAlong_of_isAdmissible_pullbackAlong hfacts
    isAdmissible_pullbackAlong_of_withBoundary_isAdmissible

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.InducedSubschemePullback
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem exists_lift_pullback_subschemeι_comap {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    ∃ ψ : Limits.pullback h D.subschemeι ⟶ D'.subscheme,
      ψ ≫ D'.subschemeι = Limits.pullback.fst h D.subschemeι := by
  have hle : D'.subschemeι.ker ≤ (Limits.pullback.fst h D.subschemeι).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hD]
    exact le_rfl
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift D'.subschemeι
      (Limits.pullback.fst h D.subschemeι) hle, by simp⟩

theorem isPullback_subschemeMapOfComap (X Y : Scheme.{u}) (h : Y ⟶ X) (D : X.IdealSheafData)
    (D' : Y.IdealSheafData) (hD : D' = D.comap h) :
    IsPullback (subschemeMapOfComap h D D' hD) D'.subschemeι D.subschemeι h := by
  have hcomm : subschemeMapOfComap h D D' hD ≫ D.subschemeι = D'.subschemeι ≫ h :=
    subschemeMapOfComap_comp h D D' hD
  obtain ⟨ψ, hψ⟩ := exists_lift_pullback_subschemeι_comap h D D' hD
  have h1 : Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm ≫ ψ = 𝟙 _ := by
    rw [← cancel_mono D'.subschemeι, Category.assoc, hψ, Category.id_comp]
    exact Limits.pullback.lift_fst _ _ _
  have h2 : ψ ≫ Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      exact hψ
    · rw [Category.assoc, Limits.pullback.lift_snd, Category.id_comp,
        ← cancel_mono D.subschemeι, Category.assoc, hcomm, ← Category.assoc, hψ]
      exact Limits.pullback.condition
  refine (IsPullback.of_iso_pullback ⟨hcomm.symm⟩
    { hom := Limits.pullback.lift D'.subschemeι (subschemeMapOfComap h D D' hD) hcomm.symm
      inv := ψ
      hom_inv_id := h1
      inv_hom_id := h2 } ?_ ?_).flip
  · exact Limits.pullback.lift_fst _ _ _
  · exact Limits.pullback.lift_snd _ _ _

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusDisjointBoundary
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    {S X : Scheme.{u}} (ι : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι]
    (J : X.IdealSheafData) (m : ℕ) (h : orderAtLeastLocus (J.comap ι) m = ∅) :
    orderAtLeastLocus J m ∩ (↑(Scheme.Hom.ker ι).support : Set ↥X) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hker
  have hcl : IsClosed (Set.range ⇑ι.base) :=
    (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding ι).isClosed_range
  have hmem : x ∈ closure (Set.range ⇑ι.base) := by
    rw [Scheme.Hom.support_ker ι] at hker
    exact hker
  rw [hcl.closure_eq] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hxo : (m : ℕ∞) ≤ orderAt J x := hx
  have hyo : (m : ℕ∞) ≤ orderAt (J.comap ι) y := by
    refine le_trans ?_ (orderAt_le_orderAt_comap ι J y)
    rw [hy]
    exact hxo
  have hy' : y ∈ orderAtLeastLocus (J.comap ι) m := hyo
  rw [h] at hy'
  exact hy'

theorem orderAtLeastLocus_inter_support_ker_eq_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hdiv : ∀ i < s.length,
      ∃ B : ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).obj
          (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).map i)
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).center i) ^ T.mult *
            B =
          (((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
              (lowerIdealWithoutBlowup T) T.mult i).comap
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).map i)))
    (hempty : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
          ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
            T.ideal T.mult s.length)
          T.mult ∩
        (↑(Scheme.Hom.ker
              (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
                s.length)).support :
          Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).obj s.length)) =
      ∅ := by
  have hid : lowerIdealWithoutBlowup T = T.ideal := by
    show T.ideal.comap (CategoryStruct.id T.scheme) = T.ideal
    simp
  have hcomap := comap_controlledTransform_embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr s.length le_rfl hdiv
  have hctrl :
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
          T.ideal T.mult s.length =
        (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
          (lowerIdealWithoutBlowup T) T.mult s.length :=
    congrArg
      (fun I => (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
        I T.mult s.length) hid.symm
  refine orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr s.length) _ T.mult ?_
  rw [hctrl, hcomap]
  exact hempty

theorem orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hdiv : ∀ i < s.length,
      ∃ B : ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj
          (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).map i)
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).center i) ^
              T.mult * B =
          (((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).controlledTransform
              (lowerIdealAfterBlowup T j hj) T.mult i).comap
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).map i)))
    (hone :
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
          T.ideal T.mult 1 =
        (lowerIdealAfterBlowup T j hj).comap
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).isoZero.hom)
    (hempty : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
          ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
                (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s
                  hpr)).controlledTransform
            T.ideal T.mult (s.length + 1))
          T.mult ∩
        (↑(Scheme.Hom.ker
              (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr
                s.length)).support :
          Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj
            s.length)) =
      ∅ := by
  have h1 := BlowupSequenceData.controlledTransform_prepend_succ (containedComponentsIdeal T j hj) hb
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
    T.ideal (lowerIdealAfterBlowup T j hj) T.mult hone s.length
  have h2 := comap_controlledTransform_embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr s.length le_rfl hdiv
  refine orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr s.length)
    _ T.mult ?_
  rw [h1, h2]
  exact hempty

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

