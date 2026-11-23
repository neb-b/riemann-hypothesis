module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem noetherianSpace_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme := by
  have := hV.isNoetherian
  exact (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    (T.boundary.get ⟨j, hj⟩).subschemeι).toIsEmbedding.toIsInducing.noetherianSpace

abbrev divisorComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
    connectedComponent x ⊆
      ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}

theorem isClosed_divisorComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsClosed (divisorComponentsInOrderLocus T j hj) := by
  have := noetherianSpace_boundary_subscheme T hV j hj
  exact TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
    ↥(T.boundary.get ⟨j, hj⟩).subscheme
    (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult)

theorem containedComponentsIdeal_eq_openSubschemeKer (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.containedComponentsIdeal T j hj =
      openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩ :=
  DivisorReduction.containedComponentsIdeal_eq_ker T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : ¬ IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.containedComponentsIdeal T j hj = ⊤ :=
  DivisorReduction.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

theorem isSmoothDivisor_boundary_get (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  exact ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem

theorem support_containedComponentsIdeal_subset_orderAtLeastLocus (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) ⊆ orderAtLeastLocus T.ideal T.mult := by
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hcl : IsClosed (((⟨divisorComponentsInOrderLocus T j hj, h⟩ :
        (T.boundary.get ⟨j, hj⟩).subscheme.Opens) :
          Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)) := isClosed_divisorComponentsInOrderLocus T hV j hj
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
      support_openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩ hcl]
    rintro y ⟨x, hx, rfl⟩
    have hx' : connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult := hx
    exact hx' mem_connectedComponent
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    intro x hx
    have hx' : x ∈ (⊤ : T.scheme.IdealSheafData).support := hx
    rw [mem_support_iff_stalkIdeal_ne_top] at hx'
    exact absurd (stalkIdeal_top x) hx'

theorem smooth_subschemeι_containedComponentsIdeal_comp (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Smooth ((DivisorReduction.containedComponentsIdeal T j hj).subschemeι ≫ T.structMap) := by
  have hsmp : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hsm : AlgebraicGeometry.Smooth
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
      ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).1
        (isSmoothDivisor_boundary_get T hV j hj)).2
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
    exact smooth_subschemeι_openSubschemeKer_comp (T.boundary.get ⟨j, hj⟩)
      ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj) T.structMap
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    exact ((isSmoothDivisor_iff T.structMap (⊤ : T.scheme.IdealSheafData)).1
      (isSmoothDivisor_top T.structMap)).2

theorem exists_etaleChart_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (x : ↥T.scheme)
    (hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support) :
    ∃ (U : T.scheme.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart T.structMap U n)
      (a : ℕ → Option (Fin n)) (b : Fin n),
      a j = some b ∧
      (∀ (i : ℕ) (hi : i < T.boundary.length), a i = none →
        restrictIdeal (T.boundary.get ⟨i, hi⟩) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < T.boundary.length) (t : Fin n), a i = some t →
        restrictIdeal (T.boundary.get ⟨i, hi⟩) U = c.coordIdeal {t}) ∧
      (∀ (i i' : ℕ), i < T.boundary.length → i' < T.boundary.length →
        ∀ t : Fin n, a i = some t → a i' = some t → i = i') ∧
      restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) U = c.coordIdeal {b} := by
  classical
  by_cases hopen : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hWclosed : IsClosed (divisorComponentsInOrderLocus T j hj) := isClosed_divisorComponentsInOrderLocus T hV j hj
    have hpre : DivisorReduction.containedComponentsIdeal T j hj =
        openSubschemeKer (T.boundary.get ⟨j, hj⟩)
          (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) :=
      containedComponentsIdeal_eq_openSubschemeKer T j hj hopen
    have h1 : x ∈ ((openSubschemeKer (T.boundary.get ⟨j, hj⟩)
        (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ :
          (T.boundary.get ⟨j, hj⟩).subscheme.Opens)).support : Set ↥T.scheme) := by
      rw [← hpre]
      exact hx
    rw [support_openSubschemeKer (T.boundary.get ⟨j, hj⟩)
      (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) hWclosed] at h1
    obtain ⟨U₀, hxU₀, hU₀⟩ := exists_opens_preimage_subschemeι_le (T.boundary.get ⟨j, hj⟩)
      (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) x h1
    obtain ⟨U₁, hxU₁, n, c, a, hinj, hnone, hsome⟩ :=
      (((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).2 x).exists_etaleChart
    have hUle : U₀ ⊓ U₁ ≤ U₁ := inf_le_right
    have hxU : x ∈ U₀ ⊓ U₁ := ⟨hxU₀, hxU₁⟩
    have hpreU : ((T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹ᵁ (U₀ ⊓ U₁)) ≤
        (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) := by
      intro y hy
      exact hU₀ hy.1
    have hrestr : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (U₀ ⊓ U₁) =
        restrictIdeal (T.boundary.get ⟨j, hj⟩) (U₀ ⊓ U₁) := by
      rw [hpre]
      exact restrictIdeal_openSubschemeKer_of_preimage_le _ _ hWclosed _ hpreU
    have hajne : a j ≠ none := by
      intro haj
      have h2 : restrictIdeal (T.boundary.get ⟨j, hj⟩) U₁ = ⊤ := by
        simpa only [List.get_eq_getElem] using hnone j hj haj
      have h3 : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (U₀ ⊓ U₁) = ⊤ := by
        rw [hrestr]
        exact restrictIdeal_eq_top_of_le _ hUle h2
      exact notMem_support_of_restrictIdeal_eq_top _ _ x hxU h3 hx
    obtain ⟨b, hb⟩ : ∃ b : Fin n, a j = some b := by
      cases h : a j with
      | none => exact absurd h hajne
      | some b => exact ⟨b, rfl⟩
    refine ⟨U₀ ⊓ U₁, hxU, n, c.restrict hUle, a, b, hb, ?_, ?_, ?_, ?_⟩
    · intro i hi hai
      refine restrictIdeal_eq_top_of_le _ hUle ?_
      simpa only [List.get_eq_getElem] using hnone i hi hai
    · intro i hi t hai
      refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {t} ?_
      simpa only [List.get_eq_getElem] using hsome i hi t hai
    · intro i i' hi hi' t h4 h5
      exact hinj i hi i' hi' t h4 h5
    · rw [hrestr]
      refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {b} ?_
      simpa only [List.get_eq_getElem] using hsome j hj b hb
  · exfalso
    rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj hopen] at hx
    exact (mem_support_iff_stalkIdeal_ne_top (⊤ : T.scheme.IdealSheafData) x).1 hx
      (stalkIdeal_top x)

theorem isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (DivisorReduction.containedComponentsIdeal T j hj) := by
  have hsmp : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
    exact isLocallyGeneratedByNonZeroDivisor_openSubschemeKer (T.boundary.get ⟨j, hj⟩)
      ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj)
      (((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).1
        (isSmoothDivisor_boundary_get T hV j hj)).1)
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    exact ((isSmoothDivisor_iff T.structMap (⊤ : T.scheme.IdealSheafData)).1
      (isSmoothDivisor_top T.structMap)).1

theorem hasStrictNormalCrossingsWith_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    HasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.boundary := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZ⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  refine ⟨U, hxU, n, c, a, {b}, ?_, ?_, ?_, hZ⟩
  · intro i hi i' hi' t hti hti'
    exact hinj i i' hi hi' t hti hti'
  · intro i hi hni
    exact hnone i hi hni
  · intro i hi t hti
    exact hsome i hi t hti

theorem isBlowupAlongIdealSheaf_id_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) :=
  Blowup.isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor _ (isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj)

theorem exists_mul_pow_containedComponentsIdeal_eq_ideal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    ∃ J : T.scheme.IdealSheafData,
      DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * J = T.ideal := by
  have := hV.isNoetherian
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hle : T.ideal ≤ DivisorReduction.containedComponentsIdeal T j hj ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.ideal T.boundary
      (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj) T.mult (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
  exact Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq
    ((isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj).pow T.mult) hle

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem iSup_le_zero_nat {Y : Scheme.{u}} (G : ℕ → Y.IdealSheafData) :
    (⨆ l, ⨆ _ : l ≤ 0, G l) = G 0 := by
  simp only [Nat.le_zero]
  exact iSup_iSup_eq_left

namespace BlowupSequenceData

theorem controlledTransform_congr {X : Scheme.{u}} (d : BlowupSequenceData X) (I I' : X.IdealSheafData)
    (h : I.comap (d.projectionToBase 0) = I'.comap (d.projectionToBase 0)) (m t : ℕ) :
    d.controlledTransform I m t = d.controlledTransform I' m t := by
  induction t with
  | zero =>
    rw [controlledTransform_zero, controlledTransform_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [controlledTransform_succ, controlledTransform_succ, ih]

theorem boundary_congr {X : Scheme.{u}} (d : BlowupSequenceData X) (E E' : List X.IdealSheafData)
    (h : List.map (fun D => D.comap (d.projectionToBase 0)) E = List.map (fun D => D.comap (d.projectionToBase 0)) E')
    (t : ℕ) :
    d.boundaryFrom E t = d.boundaryFrom E' t := by
  induction t with
  | zero =>
    rw [boundary_zero, boundary_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [boundary_succ, boundary_succ, ih]

theorem pow_controlledTransform_le_pow_controlledTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (K A : X.IdealSheafData) (m l t : ℕ)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (d.map t) (d.center t)))
    (hK : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ (m - l) * B =
        (d.controlledTransform K (m - l) t).comap (d.map t))
    (hA : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ m * B = (d.controlledTransform A m t).comap (d.map t))
    (hle : d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l)) :
    d.controlledTransform K (m - l) (t + 1) ^ m ≤ d.controlledTransform A m (t + 1) ^ (m - l) := by
  have hpowMul := d.pow_exceptionalIdeal_mul_controlledTransform_succ K (m - l) t hK
  have hAs := d.pow_exceptionalIdeal_mul_controlledTransform_succ A m t hA
  have hcomap : (d.controlledTransform K (m - l) t ^ m).comap (d.map t) ≤
      (d.controlledTransform A m t ^ (m - l)).comap (d.map t) :=
    Scheme.IdealSheafData.comap_mono _ hle
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow, ← hpowMul, ← hAs,
    mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (m - l) m] at hcomap
  exact (hcart.pow (m * (m - l))).le_of_mul_le_mul hcomap

end BlowupSequenceData

theorem orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (K A : Y.IdealSheafData) (l m : ℕ) (hlm : l < m) (h : K ^ m ≤ A ^ (m - l)) :
    orderAtLeastLocus A m ⊆ orderAtLeastLocus K (m - l) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx
  rw [mem_orderAtLeastLocus_iff]
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hml : 1 ≤ m - l := by omega
  have h1 : orderAt (A ^ (m - l)) x ≤ orderAt (K ^ m) x := orderAt_le_of_le h x
  rw [orderAt_pow k p A (m - l) x, orderAt_pow k p K m x] at h1
  have h2 : ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x :=
    (natCast_mul_le_mul_iff hml m (orderAt A x)).mpr hx
  have h3 : ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) * orderAt K x := by
    calc ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞)
        = ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) := mul_comm _ _
      _ ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x := h2
      _ ≤ ((m : ℕ) : ℕ∞) * orderAt K x := h1
  exact (natCast_mul_le_mul_iff hm (m - l) (orderAt K x)).mp h3

theorem comap_iSup_le_nat {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (n : ℕ) (G : ℕ → Y.IdealSheafData) :
    (⨆ l ≤ n, G l).comap f = ⨆ l ≤ n, (G l).comap f := by
  induction n with
  | zero => rw [iSup_le_zero_nat, iSup_le_zero_nat]
  | succ n ih =>
    rw [Nat.iSup_le_succ, Nat.iSup_le_succ, Scheme.IdealSheafData.comap_sup, ih]

theorem mem_support_iSup_le_nat {Y : Scheme.{u}} (n : ℕ) (G : ℕ → Y.IdealSheafData) (y : Y)
    (h : ∀ l ≤ n, y ∈ (G l).support) : y ∈ (⨆ l ≤ n, G l).support := by
  revert h
  induction n with
  | zero =>
    intro h
    rw [iSup_le_zero_nat]
    exact h 0 le_rfl
  | succ n ih =>
    intro h
    rw [Nat.iSup_le_succ, mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_sup]
    refine sup_le ?_ ?_
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp
        (ih fun l hl => h l (hl.trans (Nat.le_succ n)))
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (h (n + 1) le_rfl)

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

noncomputable abbrev divisorEmbedding : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme ⟶ T.scheme :=
  (T.boundary.get ⟨j, hj⟩).subschemeι

noncomputable abbrev ambientBlowupSeqStructureMorphism (t : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t ⟶ Spec (CommRingCat.of T.base) :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap

noncomputable abbrev ambientDerivIdeal [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (l t : ℕ) : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform
    (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t

theorem embeddingIntoAmbient_comp_projectionToBase (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀ := by
  induction t with
  | zero =>
    have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero = Iso.refl T.scheme :=
      ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [BlowupSequenceData.projectionToBase_zero, h0, embeddingIntoAmbient_zero, MarkedSequenceOfBlowups.projectionToBase_zero, Iso.refl_hom]
    exact Category.comp_id _
  | succ t ih =>
    have hmap := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t
    have hstruct : s.transitionMapSucc t ≫ s.projectionToBase t = s.projectionToBase (t + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact SequenceOfBlowups.transitionMap_comp_projectionToBase s.toSequenceOfBlowups (Nat.le_succ t)
    have e1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) =
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      congrArg (fun f => embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ f)
        (BlowupSequenceData.projectionToBase_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) t)
    have e2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      (Category.assoc _ _ _).symm
    have e3 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      congrArg (fun f => f ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) hmap
    have e4 : (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      Category.assoc _ _ _
    have e5 : s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) :=
      congrArg (fun f => s.transitionMapSucc t ≫ f) ih
    have e6 : s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) =
        (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ :=
      (Category.assoc _ _ _).symm
    have e7 : (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ =
        s.projectionToBase (t + 1) ≫ divisorEmbedding T j hj I₀ E₀ :=
      congrArg (fun f => f ≫ divisorEmbedding T j hj I₀ E₀) hstruct
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

