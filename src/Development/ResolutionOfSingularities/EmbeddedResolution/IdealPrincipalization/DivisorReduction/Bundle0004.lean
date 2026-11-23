module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0005
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0004
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0006
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformPowers
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

private theorem pow_controlledTransform_le_pow_controlledTransform_of_dvd {X : Scheme.{u}} (d : BlowupSequenceData X)
    (K A : X.IdealSheafData) (m l : ℕ) (hbase : K ^ m ≤ A ^ (m - l)) (t : ℕ)
    (ht : t ≤ d.length)
    (hdivA : ∀ i < t, ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B = (d.controlledTransform A m i).comap (d.map i))
    (hdivK : ∀ i < t, ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ (m - l) * B =
        (d.controlledTransform K (m - l) i).comap (d.map i)) :
    d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l) := by
  revert ht hdivA hdivK
  induction t with
  | zero =>
      intro _ _ _
      rw [BlowupSequenceData.controlledTransform_zero, BlowupSequenceData.controlledTransform_zero,
        ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_pow]
      exact Scheme.IdealSheafData.comap_mono (f := d.isoZero.hom) hbase
  | succ n ih =>
      intro ht hdivA hdivK
      have hn : n < d.length := lt_of_lt_of_le (Nat.lt_succ_self n) ht
      have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (d.map n) (d.center n)) :=
        isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (d.isBlowup n hn)
      exact pow_controlledTransform_le_pow_controlledTransform_succ d K A m l n hcart
        (hdivK n (Nat.lt_succ_self n)) (hdivA n (Nat.lt_succ_self n))
        (ih (le_of_lt hn) (fun i hi => hdivA i (Nat.lt_succ_of_lt hi))
          (fun i hi => hdivK i (Nat.lt_succ_of_lt hi)))

theorem exists_pow_mul_eq_comap_controlledTransform {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (d : BlowupSequenceData X) (p : X ⟶ Spec (CommRingCat.of k)) (A : X.IdealSheafData) (n t : ℕ)
    (ht : t < d.length) [AlgebraicGeometry.IsLocallyNoetherian (d.obj (t + 1))]
    [AlgebraicGeometry.Smooth (d.projectionToBase t ≫ p)]
    (E : List (d.obj t).IdealSheafData)
    (hE : HasStrictNormalCrossingsWith (d.projectionToBase t ≫ p) (d.center t) E)
    (hord : ↑(d.center t).support ⊆ orderAtLeastLocus (d.controlledTransform A n t) n) :
    ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ n * B = (d.controlledTransform A n t).comap (d.map t) := by
  have hle : d.controlledTransform A n t ≤ d.center t ^ n :=
    le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase t ≫ p) (d.center t) (d.controlledTransform A n t) E hE n hord
  obtain ⟨B, hB, -⟩ :=
    existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map t) (d.center t) (d.controlledTransform A n t) n
      (d.isBlowup t ht) hle
  exact ⟨B, hB⟩

end BlowupSequenceData

namespace DivisorReduction

theorem pow_ambientDerivIdeal_le_pow_controlledTransform
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult)
    (l : ℕ) (hl : l < T.mult) (t : ℕ) (ht : t ≤ s.length)
    (hdivA : ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i))
    (hdivD : ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) := by
  have ht' : t ≤ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
    rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
    exact ht
  exact BlowupSequenceData.pow_controlledTransform_le_pow_controlledTransform_of_dvd (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr)
    (derivIdealSheafIterate T.base T.structMap l I₀) I₀ T.mult l
    (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hl) t ht' hdivA hdivD

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem ker_embeddingIntoAmbientBlowupSequence_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0) =
      (AlgebraicGeometry.Scheme.Hom.ker ι).comap
        (ambientBlowupSequence ι s hres hno hcen).isoZero.hom := by
  have h1 : embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι :=
    embeddingIntoAmbientBlowupSequence_zero ι s hres hno hcen
  have h2 : (AlgebraicGeometry.Scheme.Hom.ker ι).comap
      (ambientBlowupSequence ι s hres hno hcen).isoZero.hom
      = AlgebraicGeometry.Scheme.Hom.ker ι := by
    rw [ambientBlowupSequence_isoObjZero]
    exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  rw [h1, h2]
  exact Scheme.Hom.ker_comp_of_isIso s.isoZero.hom ι

private theorem forall_le_ker_embeddingIntoAmbient_eq_boundary_get {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι) :
    ∀ t : ℕ, t ≤ s.length →
      ∀ hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length,
        AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
          ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ := by
  intro t
  induction t with
  | zero =>
      intro _ hjt
      simp only [List.get_eq_getElem] at hE ⊢
      rw [ker_embeddingIntoAmbientBlowupSequence_zero]
      simp only [BlowupSequenceData.boundary_zero, List.getElem_map, hE]
  | succ n ih =>
      intro hn hjt
      have hn' : n < s.length := hn
      have hjn : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E n).length := by
        rw [BlowupSequenceData.boundary_length]; omega
      rw [ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen n hn', ih (le_of_lt hn') hjn]
      simp only [List.get_eq_getElem, BlowupSequenceData.boundary_succ]
      rw [List.getElem_append_left (by simpa using hjn), List.getElem_map]

theorem ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι)
    (t : ℕ) (ht : t ≤ s.length)
    (hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
      ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ :=
  forall_le_ker_embeddingIntoAmbient_eq_boundary_get ι s hres hno hcen E j hj hE t ht hjt

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

theorem ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr 0) =
      (T.boundary.get ⟨j, hj⟩).comap (pushedMarkedSeq hres hno T j hj s hpr hmk).isoZero.hom := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  exact h0

theorem ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr 0) =
      ((T.boundary.get ⟨j, hj⟩).comap
          (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom).comap
        ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0) := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  have hA : (T.boundary.get ⟨j, hj⟩).comap
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom = T.boundary.get ⟨j, hj⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0
      = (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).isoZero.hom := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, BlowupSequenceData.toMarkedBlowupSequenceData_blowupMorphism,
      BlowupSequenceData.prepend_blowupMorphism_zero]
    exact rfl
  rw [hA, hB]
  exact h0

theorem isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hob : T.IsOrderBoundedByMult) (_hbal : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length) (_hpre : containedComponentsIdeal T j hj = ⊤)
    (_hlow : (restrictToDivisor T j hj).IsAdmissible)
    [AlgebraicGeometry.IsNoetherian T.scheme] (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (t : ℕ) (ht : t ≤ s.length) :
    IsSmoothDivisor ((pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t)
      (AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t)) := by
  have hjt : j < ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).length := by
    rw [BlowupSequenceData.boundary_length]; omega
  have htS : t ≤ (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact ht
  have hker : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) =
      ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).get
          ⟨j, hjt⟩ :=
    ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr T.boundary j hj
      (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _).symm t htS hjt
  have hbd : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_boundary, BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
    exact rfl
  have hpl : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).length =
      s.toSequenceOfBlowups.length := by
    have hh := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length] at hh
    exact hh
  have htlen : t ≤ (pushedMarkedSeq hres hno T j hj s hpr hmk).toSequenceOfBlowups.length := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hpl]
    exact ht
  have hsnc := MarkedSequenceOfBlowups.inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hV
    (pushedMarkedSeq hres hno T j hj s hpr hmk) t htlen
  have key : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [hker]
    exact List.getElem_mem _
  have key2 : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t := by
    rw [hbd]
    exact key
  exact ((inStrictNormalCrossingPosition_iff _ _).mp hsnc).1 _ key2

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusComparison
section
universe u

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

section

variable (k : Type u) [Field k] [CharZero k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (ι : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι]
    [AlgebraicGeometry.Smooth (ι ≫ p)]

theorem base_mem_orderAtLeastLocus_of_mem_comap
    (m : ℕ) (hm : 1 ≤ m) (A : X.IdealSheafData) (K : ℕ → X.IdealSheafData)
    (hdom : derivIdealSheafIterate k p (m - 1) A
      ≤ ⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l))
    (hbal : ∀ l < m, K l ^ m ≤ A ^ (m - l))
    (y : S) (hy : y ∈ orderAtLeastLocus (A.comap ι) m) :
    ι.base y ∈ orderAtLeastLocus A m := by
  have hsupp : ι.base y ∈
      (⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)).support := by
    refine mem_support_iSup_le_nat (m - 1)
      (fun l => logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)) (ι.base y) ?_
    intro l hl
    have hlm : l < m := by omega
    have hml : 1 ≤ m - l := by omega
    apply (Scheme.IdealSheafData.mem_support_comap).mp
    refine Scheme.IdealSheafData.support_antitone
      (comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate k p ι (K l) (m - 1 - l)) ?_
    have hpow : ((K l).comap ι) ^ m ≤ (A.comap ι) ^ (m - l) := by
      have h1 : (K l ^ m).comap ι ≤ (A ^ (m - l)).comap ι :=
        Scheme.IdealSheafData.comap_mono ι (hbal l hlm)
      rwa [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow] at h1
    have hy2 : y ∈ orderAtLeastLocus ((K l).comap ι) (m - l) :=
      orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le k (ι ≫ p) ((K l).comap ι) (A.comap ι) l m hlm hpow hy
    have hstep := support_derivIdealSheafIterate_eq_orderAtLeastLocus k (ι ≫ p) ((K l).comap ι) hml
    rw [← hstep] at hy2
    have hexp : m - 1 - l = m - l - 1 := by omega
    rw [hexp]
    exact hy2
  rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p A hm]
  exact Scheme.IdealSheafData.support_antitone hdom hsupp

end

end FunctorialResolution.EmbeddedResolution
end

