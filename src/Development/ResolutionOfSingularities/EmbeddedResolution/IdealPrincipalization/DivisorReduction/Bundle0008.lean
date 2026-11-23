module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0006
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerDimensionSmoothPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyPulledBackCenter
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0007
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem smooth_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Smooth (CategoryTheory.CategoryStruct.id X) := by
  intro X
  infer_instance

theorem surjective_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Surjective (CategoryTheory.CategoryStruct.id X) := by
  intro X
  constructor
  intro x
  exact ⟨x, rfl⟩

theorem comap_comap :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (I : Z.IdealSheafData),
      (I.comap g).comap f = I.comap (f ≫ g) := by
  intro X Y Z f g I
  simp

theorem comap_ne_top_of_surjective :
    ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [AlgebraicGeometry.Surjective h] (Z : X.IdealSheafData),
      Z ≠ ⊤ → Z.comap h ≠ ⊤ := by
  intro X Y h hsurj Z hZ
  have hne : (↑Z.support : Set ↥X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    exact hZ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty Z).mpr he)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hsurj.1 x
  subst hy
  refine (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp ⟨y, ?_⟩
  simpa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] using hx

theorem flat_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Flat (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base K f) := instFlatSpecMapOfFieldHom ..
  exact MorphismProperty.of_isPullback
    ((CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip)
    hflat

theorem surjective_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hsurj : AlgebraicGeometry.Surjective (specMapOfFieldHom T.base K f) :=
    instSurjectiveSpecMapOfFieldHom ..
  exact surjective_snd_of_isPullback_of_surjective T.structMap
    (CategoryTheory.Limits.pullback.snd T.structMap (specMapOfFieldHom T.base K f))
    (specMapOfFieldHom T.base K f) (fieldBaseChangeProjection T K f)
    (CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip

theorem comap_fieldBaseChangeProjection_ne_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K)
      (I : T.scheme.IdealSheafData), I ≠ ⊤ → I.comap (fieldBaseChangeProjection T K f) ≠ ⊤ := by
  intro T K _ f I hI
  have : AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) :=
    surjective_fieldBaseChangeProjection T K f
  exact comap_ne_top_of_surjective _ _ (fieldBaseChangeProjection T K f) I hI

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsFieldBaseChange
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem isAdmissible_of_withBoundary_isAdmissible
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible)
    (T : MarkedIdealWithBoundary.{u}) (E' : List T.scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary T.boundary E')
    (hV : (T.withBoundary E').IsAdmissible) : T.IsAdmissible := by
  have hBE' : MarkedIdealWithBoundary.SameNontrivialBoundary (T.withBoundary E').boundary T.boundary := hBE.symm
  have h := hvbr (T.withBoundary E') T.boundary hV hBE'
  have he : (T.withBoundary E').withBoundary T.boundary = T := MarkedIdealWithBoundary.withBoundary_self T
  rwa [he] at h

private theorem containedComponentsIdeal_withBoundary_of_get_eq (S : MarkedIdealWithBoundary.{u})
    (E' : List S.scheme.IdealSheafData) (j : ℕ) (hjE : j < E'.length)
    (hj : j < S.boundary.length)
    (hget : E'.get ⟨j, hjE⟩ = S.boundary.get ⟨j, hj⟩) :
    DivisorReduction.containedComponentsIdeal (S.withBoundary E') j hjE = DivisorReduction.containedComponentsIdeal S j hj := by
  rw [DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal (S.withBoundary E') j hjE,
    DivisorReduction.containedComponentsIdeal_eq_componentsInOrderLocusIdeal S j hj]
  exact congrArg (fun D => DivisorReduction.componentsInOrderLocusIdeal S.ideal S.mult D) hget

private theorem lowerIdealWithoutBlowup_eq_ideal (S : MarkedIdealWithBoundary.{u}) :
    DivisorReduction.lowerIdealWithoutBlowup S = S.ideal := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  simp [Scheme.IdealSheafData.comap_id]

theorem containedComponentsIdeal_withBoundary_baseChange
    {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}} {hno : BlowupPreservesNoetherian.{u}}
    (hfacts : DivisorReductionTerminationProperties hres hno)
    (hvbr : ∀ (S : MarkedIdealWithBoundary.{u}) (F : List S.scheme.IdealSheafData), S.IsAdmissible →
      MarkedIdealWithBoundary.SameNontrivialBoundary S.boundary F → (S.withBoundary F).IsAdmissible) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
        (E' : List (T.baseChange K f).scheme.IdealSheafData),
        MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E' →
        ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
          List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary →
          ((T.baseChange K f).withBoundary E').IsAdmissible →
            DivisorReduction.containedComponentsIdeal ((T.baseChange K f).withBoundary E') j hjE =
              (DivisorReduction.containedComponentsIdeal T j hj).comap (fieldBaseChangeProjection T K f) := by
  intro T hV K iK iCZ f E' hBE j hj hjE htake hV'
  have hVb : (T.baseChange K f).IsAdmissible :=
    isAdmissible_of_withBoundary_isAdmissible hvbr (T.baseChange K f) E' hBE hV'
  have hj' : j < (T.baseChange K f).boundary.length := by
    have h := congrArg List.length htake
    rw [List.length_take, List.length_take] at h
    omega
  have hget : E'.get ⟨j, hjE⟩ = (T.baseChange K f).boundary.get ⟨j, hj'⟩ :=
    get_eq_get_of_take_succ_eq E' (T.baseChange K f).boundary j htake hjE hj'
  rw [containedComponentsIdeal_withBoundary_of_get_eq (T.baseChange K f) E' j hjE hj' hget]
  exact hfacts.preIdeal_baseChange T hV K f hVb j hj hj'

theorem lowerIdealWithoutBlowup_withBoundary_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
      (E' : List (T.baseChange K f).scheme.IdealSheafData),
      DivisorReduction.lowerIdealWithoutBlowup ((T.baseChange K f).withBoundary E') =
        (DivisorReduction.lowerIdealWithoutBlowup T).comap (fieldBaseChangeProjection T K f) := by
  intro T K iK iCZ f E'
  rw [lowerIdealWithoutBlowup_eq_ideal, lowerIdealWithoutBlowup_eq_ideal, MarkedIdealWithBoundary.withBoundary_ideal]
  exact MarkedIdealWithBoundary.baseChange_ideal T K f

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

structure DivisorReductionHypotheses (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) : Prop where
  trivial_of_coSupport_empty :
    ∀ (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      j < T.boundary.length →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h],
        h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
          (orderAtLeastLocus T.ideal T.mult).Nonempty →
          orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅ →
          ∀ (B' : SequenceOfBlowups Y), B'.length = 0 →
            IsPullbackBlowupSequence h B' (((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups)
  baseChange : SmoothPullbackCompatibility.{u}
  smoothImpliesFlat : FlatOfSmooth.{u}
  degenerateTransversal : EmptyPulledBackCenterCompatibility.{u}
  fieldBaseChangeCompatibility : FieldBaseChangeCompatibility.{u}
  boundaryReindexingInvariance : BoundaryReindexingInvariance.{u}
  fieldLower : DivisorRestrictionFieldBaseChange.{u}
  divisorReduction : DivisorReductionStepProperties hres blowupPreservesNoetherian
  pushedBlowupSequenceProperties : PushedBlowupSequenceProperties hres blowupPreservesNoetherian

theorem DivisorReductionHypotheses.divisorReductionTerminationProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) :
    DivisorReductionTerminationProperties hres blowupPreservesNoetherian :=
  hin.divisorReduction.toDivisorReductionTerminationProperties

theorem DivisorReductionHypotheses.trivialPullbackBlowupSequence {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) (L : PrincipalizationAssignment.{u}) (j : ℕ) :
    IsPullbackSeqOfEmptyBlowupSeq hres L j :=
  pullbackOfEmptySequence_of_isPullbackSequenceOfBlowups hres L j
    (fun T hV hj Y q h _ hq E' hV' hcs hcs' B' hB' =>
      hin.trivial_of_coSupport_empty L j T hV hj Y q h hq E' hV' hcs hcs' B' hB')

theorem DivisorReductionHypotheses.divisorReductionSeqEqAmbient {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    (hin : DivisorReductionHypotheses hres) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (_hL : IsMaxOrderReduction (fun d => d < n) L O) :
    ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReductionSeqEqAmbient hres L j T hV hj := by
  intro j T hV hj _hdim hO hD hcs
  have : AlgebraicGeometry.IsNoetherian T.scheme := isNoetherian_scheme_of_isAdmissible T hV
  have h := divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hin.divisorReductionTerminationProperties L j T hV hj hO hD hcs.ne_empty
  rcases h with ⟨hZ, hpr, hmk, hstep⟩ | ⟨hZ, hb, hpr, hmk, hstep⟩
  · exact Or.inl ⟨hZ, hpr, hmk, hstep hmk⟩
  · exact Or.inr ⟨hZ, hb, hpr, hmk, hstep hmk⟩

end DivisorReduction

private theorem strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ) :
    DivisorReduction.StrictPullbackOfSmoothBaseChangeOnDivisor n L j := by
  constructor
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_eq_top hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
  · intro T hV hdim hO hbal hj hcs Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'
    exact DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor hres hfacts n L O hL j hbc T hV hdim hO hbal
      hj hcs Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE hcs' hZ hZ'

theorem isBoundaryDivisorReduction_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      ∀ (j : ℕ),
        IsBoundaryDivisorReduction (fun d => d ≤ n) j ((canonicalAlgorithmRules hres).divisorFamily L j) L := by
  intro n L O hL j
  have hshapeN : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs => hin.divisorReductionSeqEqAmbient n L O hL j T hV hj hdim hO hbal hcs
  have hshapeE : ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      orderAtLeastLocus T.ideal T.mult ≠ ∅ → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj :=
    fun T hV hj hdim hO hbal hcs =>
      hshapeN T hV hj hdim hO hbal (Set.nonempty_iff_ne_empty.mpr hcs)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E' hBE htake
      hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj K _ _ f E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_fieldBaseChange_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties
      hin.baseChange hin.fieldBaseChangeCompatibility hin.fieldLower n L O hL j hshapeE T hV hdim hO hbal hj K f E'
      hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj i hi x
    exact divisorFamily_canonicalAlgorithmRules_orderAt_le_mult hres hin.divisorReductionTerminationProperties n L j T hV hdim hO hbal hj i hi x
  · intro T hV hdim hO hbal hj i hi
    exact divisorFamily_canonicalAlgorithmRules_center_nonempty hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO hbal
      hj i hi
  · intro T hV hdim hO hbal hj hm J hVJ hdimJ him
    exact isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties n L O hL j T hV hdim hO
      (fun _ => hbal) hj hm J hVJ hdimJ him
  · intro T hV hdim hO hbal hj
    obtain ⟨D, b, h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_smoothDivisorSeq_divisorFamily_canonicalAlgorithmRules hres hin.divisorReductionTerminationProperties hin.pushedBlowupSequenceProperties n L O hL j T hV hdim hO
        hbal hj
    refine ⟨D, b, h1, h2, h3, h4, ?_, h6, ?_⟩
    · intro t ht hb
      exact h5 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
    · intro t ht hb
      exact h7 t ht (fun hbt h0 => hb ⟨hbt, h0⟩)
  · intro T hV hdim hO hbal hj Y q h _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isPullbackBlowupSequence hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j (hin.trivialPullbackBlowupSequence L j)
      (restrictedSmoothPullback_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange
        hin.degenerateTransversal n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj Y q h _ _ hq E' hBE htake hV' hdim' hO' hDB' hjE
    have hjE2 : j < E'.length := hjE
    exact DivisorReduction.divisorFamily_isStrictPullbackBlowupSeq_of_smooth hres hin.divisorReductionTerminationProperties hin.baseChange
      hin.smoothImpliesFlat n L j
      (strictPullbackOfSmoothBaseChangeOnDivisor_of_isMaxOrderReduction hres hin.divisorReductionTerminationProperties hin.baseChange n L O hL j)
      hshapeN T hV hdim hO hbal hj Y q h hq E' hBE htake hV' hdim' hO' hDB' hjE2
  · intro T hV hdim hO hbal hj hcs
    exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO hbal hj hcs

theorem isBoundaryPositionInvariant_divisorFamily_canonicalAlgorithmRules
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hin : DivisorReduction.DivisorReductionHypotheses hres) :
    ∀ (n : ℕ) (L O : PrincipalizationAssignment.{u}),
      IsMaxOrderReduction (fun d => d < n) L O →
      IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  fun n L O hL =>
    isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient hres hin.divisorReductionTerminationProperties hin.baseChange hin.boundaryReindexingInvariance
      n L O hL (hin.divisorReductionSeqEqAmbient n L O hL)

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryFieldBaseChange
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem sameNontrivialBoundary_take_eraseIdx_comap {X Y : Scheme.{u}} (p : Y ⟶ X)
    (B : List X.IdealSheafData) (E' : List Y.IdealSheafData) (j : ℕ)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap p) B) E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (List.map (fun D => D.comap p) B))
    (hj : j < B.length) (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E'.eraseIdx j))
      (List.map (fun D => D.comap p) (List.take (B.length - 1) (B.eraseIdx j))) := by
  have hE : List.take (E'.length - 1) (E'.eraseIdx j) = E'.eraseIdx j :=
    List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hjE))
  have hB : List.take (B.length - 1) (B.eraseIdx j) = B.eraseIdx j :=
    List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hj))
  rw [hE, hB, ← List.eraseIdx_map]
  exact hBE.symm.eraseIdx j htake

private theorem isClosed_setOf_connectedComponent_subset {X : Type u} [TopologicalSpace X]
    (hop : ∀ x : X, IsOpen (connectedComponent x)) (P : Set X) :
    IsClosed {x : X | connectedComponent x ⊆ P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨connectedComponent x, ?_, hop x, mem_connectedComponent⟩
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
  intro hsub
  apply hx
  rw [connectedComponent_eq hy]
  exact hsub

theorem lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryWithoutBlowup ((T.baseChange K f).withBoundary E')).eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  rw [lowerBoundaryWithoutBlowup_eq ((T.baseChange K f).withBoundary E'), lowerBoundaryWithoutBlowup_eq T]
  exact sameNontrivialBoundary_take_eraseIdx_comap (fieldBaseChangeProjection T K f) T.boundary E' j hBE htake hj hjE

theorem preimageSupportEqComponentsInOrderLocus_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) : PreimageSupportEqComponentsInOrderLocus T j hj := by
  intro h
  have := hV.isNoetherian
  have := FunctorialResolution.Blowup.noetherianSpace_subscheme (T.boundary.get ⟨j, hj⟩)
  have hnsU : TopologicalSpace.NoetherianSpace
      ↥((boundaryComponentsInOrderLocusOpens T j hj h).toScheme) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace ↥(boundaryComponentsInOrderLocus T j hj))
  have hqc : AlgebraicGeometry.QuasiCompact
      ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) := by
    constructor
    intro V _ _
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hclosed : IsClosed (boundaryComponentsInOrderLocus T j hj) :=
    isClosed_setOf_connectedComponent_subset
      (fun x => Blowup.isOpen_connectedComponent_of_noetherianSpace _ x) _
  have hinj : Function.Injective ⇑(T.boundary.get ⟨j, hj⟩).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).injective
  have himg : IsClosed (⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj) :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).isClosedMap _ hclosed
  have hU : Set.range ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι = boundaryComponentsInOrderLocus T j hj :=
    Scheme.Opens.range_ι _
  have hcomp : ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
      = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ∘ ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι := by
    funext x
    simp
  have hrange :
      Set.range ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
        = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj := by
    rw [hcomp, Set.range_comp, hU]
  have hsupp : ((AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme)
      = closure (Set.range
          ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [hsupp, hrange, himg.closure_eq]
  exact Set.preimage_image_eq _ hinj

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

