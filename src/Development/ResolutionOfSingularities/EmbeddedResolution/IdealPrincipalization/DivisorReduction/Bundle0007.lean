module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariantSucc
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Prepend
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupMarked
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

theorem IsMarked.of_comap_isoObjZero_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {d : BlowupSequenceData X} {p : X ⟶ Spec (CommRingCat.of k)} {m : ℕ}
    {I I' : X.IdealSheafData} {E E' : List X.IdealSheafData}
    (hI : I.comap d.isoZero.hom = I'.comap d.isoZero.hom)
    (hE : List.map (fun D => D.comap d.isoZero.hom) E =
      List.map (fun D => D.comap d.isoZero.hom) E')
    (h : d.IsMarked p I m E) : d.IsMarked p I' m E' := by
  have hIc : ∀ t : ℕ, d.controlledTransform I m t = d.controlledTransform I' m t := fun t =>
    d.controlledTransform_congr I I' (by rw [d.projectionToBase_zero]; exact hI) m t
  have hEc : ∀ t : ℕ, d.boundaryFrom E t = d.boundaryFrom E' t := fun t =>
    d.boundary_congr E E' (by simp only [d.projectionToBase_zero]; exact hE) t
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [← hIc i]
    exact h.divisible i hi
  · intro i hi
    rw [← hIc i]
    exact h.center_order i hi
  · exact h.center_smooth
  · intro i hi
    rw [← hEc i]
    exact h.center_snc i hi

end BlowupSequenceData

namespace DivisorReduction

theorem goingUpInvariant_of_le (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j)
    (t : ℕ) (ht : t ≤ s.length) :
    GoingUpInvariant hres hno T j hj I₀ E₀ s hpr t := by
  induction t with
  | zero => exact goingUpInvariant_zero hres hno T j hj I₀ E₀ s hpr hE₀ hjE hget htrunc
  | succ n ih =>
      exact GoingUpInvariant.succ (ih (Nat.le_of_succ_le ht)) hbal hm hV hlift (Nat.lt_of_succ_le ht)

theorem isMarked_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).IsMarked T.structMap I₀ T.mult E₀ := by
  have hlen : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length = s.length :=
    ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      (i + 1) hi).exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i (Nat.lt_succ_self i)
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      i (le_of_lt hi)).support_center_subset_orderAtLeastLocus hbal hm hV hi
  · intro i hi
    rw [hlen] at hi
    exact smooth_ambientBlowupSeq_center_comp hres hno T j hj I₀ E₀ s hpr i hi
  · intro i hi
    rw [hlen] at hi
    exact (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
      i (le_of_lt hi)).hasStrictNormalCrossingsWith_center_boundary hlift hi

theorem comap_controlledTransform_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult) (hm : 1 ≤ T.mult)
    (hV : (restrictToBoundaryDivisor T j hj I₀ E₀).IsAdmissible) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (hE₀ : InStrictNormalCrossingPosition T.structMap E₀) (hjE : j < E₀.length)
    (hget : E₀[j] = T.boundary[j])
    (htrunc : List.take (T.boundary.length - 1) (E₀.eraseIdx j) = E₀.eraseIdx j)
    (t : ℕ) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.ideal t :=
  (goingUpInvariant_of_le hres hno T j hj I₀ E₀ s hpr hbal hm hV hlift hE₀ hjE hget htrunc
    t ht).comap_controlledTransform ht

private theorem lowerIdealWithoutBlowup_eq_ideal (T : MarkedIdealWithBoundary.{u}) :
    lowerIdealWithoutBlowup T = T.ideal :=
  Scheme.IdealSheafData.comap_id T.ideal

theorem isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) [AlgebraicGeometry.IsNoetherian T.scheme]
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hbal : ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (_hZ : containedComponentsIdeal T j hj = ⊤)
    (hVlow : (restrictToDivisor T j hj).IsAdmissible)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry : lowerBoundaryWithoutBlowup T = T.boundary := lowerBoundaryWithoutBlowup_eq T
  have hideal : lowerIdealWithoutBlowup T = T.ideal := lowerIdealWithoutBlowup_eq_ideal T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]; exact hj
  have hE₀ : InStrictNormalCrossingPosition T.structMap (lowerBoundaryWithoutBlowup T) := by rw [hbdry]; exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [hbdry, ← hlen1, List.take_length]
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
    rw [hideal]; exact hbal
  have main := isMarked_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE₀ hjE (hgetAll hjE) htrunc
  exact BlowupSequenceData.IsMarked.of_comap_isoObjZero_eq (by simp only [hideal]) (by simp only [hbdry]) main

theorem comap_controlledTransform_of_containedComponentsIdeal_eq_top
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) [AlgebraicGeometry.IsNoetherian T.scheme]
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hbal : ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult)
    (j : ℕ) (hj : j < T.boundary.length)
    (_hZ : containedComponentsIdeal T j hj = ⊤)
    (hVlow : (restrictToDivisor T j hj).IsAdmissible)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t ≤ s.length) :
    ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
        T.ideal T.mult t).comap
      (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t) = s.ideal t := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hbdry : lowerBoundaryWithoutBlowup T = T.boundary := lowerBoundaryWithoutBlowup_eq T
  have hideal : lowerIdealWithoutBlowup T = T.ideal := lowerIdealWithoutBlowup_eq_ideal T
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by rw [hbdry]; exact hj
  have hE₀ : InStrictNormalCrossingPosition T.structMap (lowerBoundaryWithoutBlowup T) := by rw [hbdry]; exact hV.snc
  have hgetAll : ∀ h : j < (lowerBoundaryWithoutBlowup T).length,
      (lowerBoundaryWithoutBlowup T)[j]'h = T.boundary[j] := by
    rw [hbdry]
    intro _
    rfl
  have hlen1 : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [hbdry, ← hlen1, List.take_length]
  have hbal' : IsDerivBalanced T.base T.structMap (lowerIdealWithoutBlowup T) T.mult := by
    rw [hideal]; exact hbal
  have main := comap_controlledTransform_ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
    hbal' hV.one_le_mult hVlow hlift hE₀ hjE (hgetAll hjE) htrunc t ht
  have hc := BlowupSequenceData.controlledTransform_congr
    (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr)
    (lowerIdealWithoutBlowup T) T.ideal (by simp only [hideal]) T.mult t
  rw [← hc]
  exact main

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryPositionInvariance
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁))
    (hV₁ : (T.withBoundary L₁).IsAdmissible) (hV₂ : (T.withBoundary L₂).IsAdmissible) :
    IsStrictPullbackBlowupSeq (𝟙 T.scheme)
      (((canonicalAlgorithmRules hres).divisorFamily L j₂ (T.withBoundary L₂)).toSequenceOfBlowups)
      (((canonicalAlgorithmRules hres).divisorFamily L j₁ (T.withBoundary L₁)).toSequenceOfBlowups) := by
  classical
  by_cases hcs : (orderAtLeastLocus T.ideal T.mult).Nonempty
  · have hN : AlgebraicGeometry.IsNoetherian T.scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
    have hN₁ : AlgebraicGeometry.IsNoetherian (T.withBoundary L₁).scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV₁
    have hN₂ : AlgebraicGeometry.IsNoetherian (T.withBoundary L₂).scheme :=
      DivisorReduction.isNoetherian_scheme_of_isAdmissible _ hV₂
    have hflat : AlgebraicGeometry.Flat (𝟙 T.scheme) := inferInstance
    have hjb₁ : j₁ < (T.withBoundary L₁).boundary.length := hj₁
    have hjb₂ : j₂ < (T.withBoundary L₂).boundary.length := hj₂
    have hpre : DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁ =
        DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂ :=
      DivisorReduction.containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq
    have hs₁ : _ ∨ _ := hshape j₁ (T.withBoundary L₁) hV₁ hjb₁ hdim hO hbal hcs
    have hs₂ : _ ∨ _ := hshape j₂ (T.withBoundary L₂) hV₂ hjb₂ hdim hO hbal hcs
    simp only [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq]
    rcases hs₁ with ⟨hZ₁, hpr₁, hmk₁, he₁⟩ | ⟨hZ₁, hb₁, hpr₁, hmk₁, he₁⟩
    · rcases hs₂ with ⟨hZ₂, hpr₂, hmk₂, he₂⟩ | ⟨hZ₂, hb₂, hpr₂, hmk₂, he₂⟩
      · have hstep : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₂))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₂))
              (L (DivisorReduction.restrictToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₁))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₁))
              (L (DivisorReduction.restrictToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
            ((L₁.get ⟨j₁, hj₁⟩).subscheme) ((L₂.get ⟨j₂, hj₂⟩).subscheme)
            ((L₁.get ⟨j₁, hj₁⟩).subschemeι) ((L₂.get ⟨j₂, hj₂⟩).subschemeι)
            (𝟙 T.scheme) _
            ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealWithoutBlowup (T.withBoundary L₁))
              (DivisorReduction.lowerBoundaryWithoutBlowup (T.withBoundary L₁)) T.scheme (𝟙 T.scheme)
              (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq)).flip)
            _ _ hpr₁ hpr₂
            (IsStrictPullbackBlowupSeq.ofMarkedSequence
              (A := DivisorReduction.restrictToDivisor (T.withBoundary L₂) j₂ hjb₂)
              (B := DivisorReduction.restrictToDivisor (T.withBoundary L₁) j₁ hjb₁) _ _ _
              (DivisorReduction.isStrictPullbackBlowupSeq_restrictToDivisor_of_get_eq_of_eq_top hres hfacts n L O hL hbc hsh
                T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hdim hO hbal hcs hV₂ hdim hO hbal hcs hZ₁))
        rw [he₁, he₂]
        simp only [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hstep
      · exact absurd (hpre.symm.trans hZ₁) hZ₂
    · rcases hs₂ with ⟨hZ₂, hpr₂, hmk₂, he₂⟩ | ⟨hZ₂, hb₂, hpr₂, hmk₂, he₂⟩
      · exact absurd (hpre.trans hZ₂) hZ₁
      · have hcomap : (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
            (𝟙 (T.withBoundary L₁).scheme) =
            DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁ := by
          rw [Scheme.IdealSheafData.comap_id]
        have hZZ : DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂ =
            (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
              (𝟙 (T.withBoundary L₁).scheme) := hpre.symm.trans hcomap.symm
        have hb₁' : Blowup.IsBlowupAlongIdealSheaf (𝟙 (T.withBoundary L₁).scheme)
            ((DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁).comap
              (𝟙 (T.withBoundary L₁).scheme)) := by
          rw [hcomap]
          exact hb₁
        have hstep : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂).toSequenceOfBlowups
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁).toSequenceOfBlowups :=
          hfacts.isStrictPullbackSeq_ambientTower T.scheme T.scheme
            ((L₁.get ⟨j₁, hj₁⟩).subscheme) ((L₂.get ⟨j₂, hj₂⟩).subscheme)
            ((L₁.get ⟨j₁, hj₁⟩).subschemeι) ((L₂.get ⟨j₂, hj₂⟩).subschemeι)
            (𝟙 T.scheme) _
            ((DivisorReduction.isPullback_divisorPullbackMap hbc (T.withBoundary L₁) j₁ hjb₁
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁) T.scheme (𝟙 T.scheme)
              (L₂.get ⟨j₂, hj₂⟩) (get_eq_comap_id L₁ L₂ j₁ j₂ hj₁ hj₂ heq)).flip)
            _ _ hpr₁ hpr₂
            (IsStrictPullbackBlowupSeq.ofMarkedSequence
              (A := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)
              (B := DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁) _ _ _
              (DivisorReduction.isStrictPullbackBlowupSeq_restrictTwistedToDivisor_of_get_eq hres hfacts n L O hL hbc hsh
                T L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hdim hO hbal hcs hV₂ hdim hO hbal hcs hZ₁))
        have hfin : IsStrictPullbackBlowupSeq (𝟙 T.scheme)
            (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal (T.withBoundary L₂) j₂ hjb₂) hb₂
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂
                hjb₂ (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
                (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
                (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂)).toSequenceOfBlowups
            (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal (T.withBoundary L₁) j₁ hjb₁) hb₁
              (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₁) j₁
                hjb₁ (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
                (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hjb₁)
                (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₁) j₁ hjb₁)) hpr₁)).toSequenceOfBlowups := by
          rw [BlowupSequenceData.prepend_toSequenceOfBlowups_congr hZZ hb₂ hb₁'
            (DivisorReduction.ambientBlowupSeq hres blowupPreservesNoetherian (T.withBoundary L₂) j₂ hjb₂
              (DivisorReduction.lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (DivisorReduction.lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hjb₂)
              (L (DivisorReduction.restrictTwistedToDivisor (T.withBoundary L₂) j₂ hjb₂)) hpr₂)]
          exact IsStrictPullbackBlowupSeq.prepend hstep _ hb₁ hb₁'
        rw [he₁, he₂]
        simp only [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
        exact hfin
  · have hcs0 : orderAtLeastLocus T.ideal T.mult = ∅ := Set.not_nonempty_iff_eq_empty.mp hcs
    exact IsStrictPullbackBlowupSeq.of_length_zero _ _ _
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j₂ (T.withBoundary L₂) hV₂ hdim hO hbal
        hj₂ hcs0)
      (divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j₁ (T.withBoundary L₁) hV₁ hdim hO hbal
        hj₁ hcs0)

theorem strictBoundaryReindexingInvariance_of_divisorReductionSeqEqAmbient
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj) :
    DivisorReduction.StrictBoundaryReindexingInvariance hres n L :=
  ⟨fun T hV hdim hO hbal L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hV₂ =>
    isStrictPullbackBlowupSeq_id_divisorFamily_of_get_eq hres hfacts hbc hsh n L O hL hshape T hV hdim hO hbal
      L₁ L₂ j₁ hj₁ j₂ hj₂ heq hBE hV₁ hV₂⟩

theorem isBoundaryPositionInvariant_divisorFamily_of_divisorReductionSeqEqAmbient
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (hbc : DivisorReduction.SmoothPullbackCompatibility.{u}) (hsh : DivisorReduction.BoundaryReindexingInvariance.{u})
    (n : ℕ) (L O : PrincipalizationAssignment.{u}) (hL : IsMaxOrderReduction (fun d => d < n) L O)
    (hshape : ∀ (j : ℕ) (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hj : j < T.boundary.length),
      T.krullDimSucc ≤ n → T.IsOrderBoundedByMult → T.IsBalanced hV.locallyOfFiniteType →
      (orderAtLeastLocus T.ideal T.mult).Nonempty → DivisorReduction.DivisorReductionSeqEqAmbient hres L j T hV hj) :
    IsBoundaryPositionInvariant (fun d => d ≤ n) fun j => (canonicalAlgorithmRules hres).divisorFamily L j :=
  DivisorReduction.isBoundaryPositionInvariant_divisorFamily hres n L
    (strictBoundaryReindexingInvariance_of_divisorReductionSeqEqAmbient hres hfacts hbc hsh n L O hL hshape)

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusFieldBaseChange
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_withBoundary_baseChange_eq_preimage (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (K : Type u) [Field K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal m =
      (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m := by
  haveI : CharZero T.base := hV.charZero
  haveI : CharZero K := (RingHom.charZero_iff f.injective).mp hV.charZero
  haveI : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  exact orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal m

end FunctorialResolution.EmbeddedResolution
end

