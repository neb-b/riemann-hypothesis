module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorFamilyCenters
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionPushforward
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem isPushforwardBlowupSeq_of_ofSequenceOfBlowups {S X : Scheme.{u}} (ι : S ⟶ X) [IsClosedImmersion ι]
    (B : SequenceOfBlowups S) (B' : SequenceOfBlowups X)
    (h : IsPushforwardBlowupSeq ι (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups B') : IsPushforwardBlowupSeq ι B B' := by
  unfold IsPushforwardBlowupSeq at h ⊢
  simp only [BlowupSequenceData.toSequenceOfBlowups_blowupMorphism] at h
  exact h

private theorem heq_toSequenceOfBlowups_of_eq (L : PrincipalizationAssignment.{u}) {A B : MarkedIdealWithBoundary.{u}} (h : A = B) :
    HEq ((L A).toSequenceOfBlowups) ((L B).toSequenceOfBlowups) := by
  subst h
  rfl

theorem isPushforwardSequenceOfBlowups_of_length_eq_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [IsClosedImmersion ι] (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hlenZero : BS.length = 0) (hB : B.length = 0) :
    IsPushforwardBlowupSeq ι BS B := by
  have key : ∀ i : ℕ, i ≤ BS.length → i = 0 := by
    intro i hi
    omega
  unfold IsPushforwardBlowupSeq
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ ι ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi)).symm, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _
    infer_instance
  · simp
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)

theorem isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    {Y : Scheme.{u}} (ι : T.scheme ⟶ Y) [IsClosedImmersion ι] (B : SequenceOfBlowups Y)
    (h : IsPushforwardBlowupSeq ι (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.toSequenceOfBlowups B) :
    IsPushforwardBlowupSeq ι s.toSequenceOfBlowups B := by
  rw [MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence] at h
  exact isPushforwardBlowupSeq_of_ofSequenceOfBlowups ι s.toSequenceOfBlowups B h

namespace DivisorReduction

theorem comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    (DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
  unfold DivisorReduction.lowerIdealWithoutBlowup
  rw [Scheme.IdealSheafData.comap_id, him]
  exact Blowup.comap_map_of_isClosedImmersion _ J

theorem map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
        (List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j)) =
      List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) (T.boundary.eraseIdx j) := by
  unfold DivisorReduction.lowerBoundaryWithoutBlowup
  have h1 : List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary
      = T.boundary := by
    simp [Scheme.IdealSheafData.comap_id]
  rw [h1]
  have hlen : (T.boundary.eraseIdx j).length = T.boundary.length - 1 := by
    simp [List.length_eraseIdx, hj]
  rw [← hlen, List.take_length]

theorem restrictToDivisor_eq_withSchemeIdealBoundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    DivisorReduction.restrictToDivisor T j hj =
      T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j)) := by
  have h1 := DivisorReduction.comap_lowerIdealWithoutBlowup_of_eq_imageIdealSheaf T j hj J him
  have h2 := DivisorReduction.map_comap_take_eraseIdx_lowerBoundaryWithoutBlowup T j hj
  unfold DivisorReduction.restrictToDivisor DivisorReduction.restrictToBoundaryDivisor MarkedIdealWithBoundary.withSchemeIdealBoundary
  rw [h1, h2]

end DivisorReduction

theorem isPushforwardBlowupSeq_divisorFamily_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian)
    (n : ℕ) (L O : PrincipalizationAssignment.{u})
    (hL : IsMaxOrderReduction (fun d => d < n) L O) (j : ℕ)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hdim : T.krullDimSucc ≤ n) (hO : T.IsOrderBoundedByMult)
    (hD : ∀ hft : AlgebraicGeometry.LocallyOfFiniteType T.structMap, T.IsBalanced hft)
    (hj : j < T.boundary.length) (hm : T.mult = 1)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (hVJ : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hdimJ : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).krullDimSucc < T.krullDimSucc)
    (him : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    IsPushforwardBlowupSeq (T.boundary.get ⟨j, hj⟩).subschemeι
      (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j)))).toSequenceOfBlowups
      ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have : AlgebraicGeometry.IsNoetherian T.scheme :=
    DivisorReduction.isNoetherian_scheme_of_isAdmissible T hV
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = (∅ : Set ↥T.scheme)
  · have hsub : (↑T.ideal.support : Set ↥T.scheme) ⊆ orderAtLeastLocus T.ideal T.mult := by
      intro x hx
      rw [hm]
      exact (mem_orderAtLeastLocus_one_iff T.ideal x).mpr hx
    rw [hcs] at hsub
    have hsupp : (↑T.ideal.support : Set ↥T.scheme) = ∅ := Set.subset_empty_iff.mp hsub
    have hItop : T.ideal = ⊤ :=
      (Scheme.IdealSheafData.eq_top_iff_support_eq_empty T.ideal).mpr hsupp
    have hJtop : J = ⊤ := by
      have h2 : (imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J).comap
          (T.boundary.get ⟨j, hj⟩).subschemeι = J :=
        Blowup.comap_map_of_isClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι J
      rw [← him, hItop] at h2
      rw [← h2]
      simp
    have h0 : orderAtLeastLocus (⊤ : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData) 1
        = (∅ : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := by
      simp [orderAtLeastLocus_top_eq_empty]
    have hcsJ : orderAtLeastLocus
        (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).ideal
        (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).mult =
        (∅ : Set ↥(T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
          ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
          (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
            (T.boundary.eraseIdx j))).scheme) := by
      rw [MarkedIdealWithBoundary.withSchemeIdealBoundary_ideal, MarkedIdealWithBoundary.withSchemeIdealBoundary_mult, hJtop, hm]
      exact h0
    refine isPushforwardSequenceOfBlowups_of_length_eq_zero _ _ _ ?_ ?_
    · exact hL.trivial_of_coSupport_empty _ hVJ (lt_of_lt_of_le hdimJ hdim) hcsJ
    · exact divisorFamily_canonicalAlgorithmRules_length_eq_zero hres n L j T hV hdim hO
        (hD hV.locallyOfFiniteType) hj hcs
  · have hpretop : DivisorReduction.containedComponentsIdeal T j hj = ⊤ :=
      hfacts.preIdeal_eq_top_of_imageIdeal T hV j hj J hm hVJ him
    rcases DivisorReduction.divisorReductionSeq_eq_ambientBlowupSeq_or_prepend hres hfacts L j T hV hj hO
        (hD hV.locallyOfFiniteType) hcs with
      ⟨-, hpr, hmk0, hstep⟩ | ⟨hne, -⟩
    · have hT : DivisorReduction.restrictToDivisor T j hj =
          T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)) :=
        DivisorReduction.restrictToDivisor_eq_withSchemeIdealBoundary T j hj J him
      have hHeq : HEq ((L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups)
          ((L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)))).toSequenceOfBlowups) := heq_toSequenceOfBlowups_of_eq L hT
      have hE : (L (DivisorReduction.restrictToDivisor T j hj)).toSequenceOfBlowups =
          (L (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
            ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
            (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
              (T.boundary.eraseIdx j)))).toSequenceOfBlowups := eq_of_heq hHeq
      rw [divisorFamily_canonicalAlgorithmRules_eq_divisorReductionSeq, hstep hmk0, ← hE,
        BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups]
      have inst : IsClosedImmersion (T.boundary.get ⟨j, hj⟩).subschemeι := inferInstance
      exact @isPushforwardBlowupSeq_toSequenceOfBlowups_of_ofMarkedSequence (DivisorReduction.restrictToDivisor T j hj)
        (L (DivisorReduction.restrictToDivisor T j hj)) T.scheme
        (T.boundary.get ⟨j, hj⟩).subschemeι inst _
        (isPushforwardBlowupSeq_ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence (L (DivisorReduction.restrictToDivisor T j hj))).toBlowupSequenceData
          hres blowupPreservesNoetherian hpr)
    · exact absurd hpretop hne

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictTransformRestriction
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem ker_le_ker_of_comp_eq {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    (h : e ≫ g = f) : g.ker ≤ f.ker := by
  subst h
  exact Scheme.Hom.le_ker_comp e g

theorem comap_strictTransform_of_iso {X X₁ X₁' : Scheme.{u}} (π : X₁ ⟶ X)
    (f : X₁' ≅ X₁) (Z D : X.IdealSheafData) (_hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Z.comap π))
    [QuasiCompact (strictTransformι π Z D)]
    [QuasiCompact (strictTransformι (f.hom ≫ π) Z D)] :
    (Blowup.strictTransform π Z D).comap f.hom = Blowup.strictTransform (f.hom ≫ π) Z D := by
  have hRHS : Blowup.strictTransform (f.hom ≫ π) Z D
      = Blowup.strictTransform f.hom (Z.comap π) (D.comap π) :=
    strictTransform_eq_of_comap_eq (f.hom ≫ π) f.hom Z D (Z.comap π) (D.comap π)
      (by rw [Scheme.IdealSheafData.comap_comp])
      (by rw [Scheme.IdealSheafData.comap_comp])
  obtain ⟨m₀, hiso, hm₀⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso f.hom (D.comap π)
  have := hiso
  have hsupp : ((Z.comap π).comap f.hom).support.compl
      = f.hom ⁻¹ᵁ (Z.comap π).support.compl := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have h1 : m₀ ⁻¹ᵁ strictTransformOpens π Z D
      = ((D.comap π).comap f.hom).subschemeι ⁻¹ᵁ (f.hom ⁻¹ᵁ (Z.comap π).support.compl) :=
    congrArg (fun w => w ⁻¹ᵁ (Z.comap π).support.compl) hm₀
  have hV' : strictTransformOpens f.hom (Z.comap π) (D.comap π)
      = m₀ ⁻¹ᵁ strictTransformOpens π Z D := by
    rw [h1]
    exact congrArg (fun W => ((D.comap π).comap f.hom).subschemeι ⁻¹ᵁ W) hsupp
  have hm₀2 : m₀ ≫ ((D.comap π).subschemeι ≫ inv f.hom)
      = ((D.comap π).comap f.hom).subschemeι := by
    rw [← Category.assoc, hm₀, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hm₀3 : inv m₀ ≫ ((D.comap π).comap f.hom).subschemeι
      = (D.comap π).subschemeι ≫ inv f.hom := by
    rw [IsIso.inv_comp_eq, hm₀2]
  have hinvle : strictTransformOpens π Z D
      ≤ inv m₀ ⁻¹ᵁ strictTransformOpens f.hom (Z.comap π) (D.comap π) := by
    rw [hV']
    have h3 : inv m₀ ⁻¹ᵁ (m₀ ⁻¹ᵁ strictTransformOpens π Z D)
        = (inv m₀ ≫ m₀) ⁻¹ᵁ strictTransformOpens π Z D := rfl
    rw [h3, IsIso.inv_hom_id]
    simp
  have hfac1 : (Scheme.Hom.resLE m₀ (strictTransformOpens π Z D)
        (strictTransformOpens f.hom (Z.comap π) (D.comap π)) (le_of_eq hV'))
      ≫ (strictTransformι π Z D ≫ inv f.hom)
      = strictTransformι f.hom (Z.comap π) (D.comap π) := by
    rw [strictTransformι_eq_ι_comp_subschemeι π Z D,
      strictTransformι_eq_ι_comp_subschemeι f.hom (Z.comap π) (D.comap π),
      ← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Category.assoc, hm₀2]
  have hfac2 : (Scheme.Hom.resLE (inv m₀)
        (strictTransformOpens f.hom (Z.comap π) (D.comap π))
        (strictTransformOpens π Z D) hinvle)
      ≫ strictTransformι f.hom (Z.comap π) (D.comap π)
      = strictTransformι π Z D ≫ inv f.hom := by
    rw [strictTransformι_eq_ι_comp_subschemeι f.hom (Z.comap π) (D.comap π),
      strictTransformι_eq_ι_comp_subschemeι π Z D, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Category.assoc, hm₀3, Category.assoc]
  have hcomp : (strictTransformι π Z D ≫ inv f.hom) ≫ f.hom
      = strictTransformι π Z D := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have : QuasiCompact (strictTransformι π Z D ≫ inv f.hom) := inferInstance
  have : QuasiCompact ((strictTransformι π Z D ≫ inv f.hom) ≫ f.hom) := by
    rw [hcomp]
    infer_instance
  have hL := Blowup.comap_ker_comp_of_isOpenImmersion
    (strictTransformι π Z D ≫ inv f.hom) f.hom
  rw [hcomp] at hL
  rw [hRHS, strictTransform_eq_ker_strictTransformι π Z D, hL,
    strictTransform_eq_ker_strictTransformι f.hom (Z.comap π) (D.comap π)]
  exact le_antisymm (ker_le_ker_of_comp_eq _ _ _ hfac1) (ker_le_ker_of_comp_eq _ _ _ hfac2)

theorem exists_iso_subscheme_of_ker_eq_strictTransform {X X₁ S S₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι)) :
    ∃ (e : S ≅ (Scheme.Hom.ker ι).subscheme)
      (e₁ : S₁ ≅ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subscheme),
      e.hom ≫ (Scheme.Hom.ker ι).subschemeι = ι ∧
        e₁.hom ≫ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι = ι₁ ∧
        e₁.hom ≫ strictTransformSubschemeLift π Z (Scheme.Hom.ker ι) = ρ ≫ e.hom := by
  have hkH : (Scheme.Hom.ker ι).subschemeι.ker = Scheme.Hom.ker ι :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hkT : (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι.ker
      = Blowup.strictTransform π Z (Scheme.Hom.ker ι) :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hu : IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH) ≫
      (Scheme.Hom.ker ι).subschemeι = ι := IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH)) :=
    IsClosedImmersion.isIso_of_ker_eq ι (Scheme.Hom.ker ι).subschemeι _ hu hkH.symm
  have hu₁ : IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
        (le_of_eq (hkT.trans hker.symm)) ≫
      (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι = ι₁ :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
      (le_of_eq (hkT.trans hker.symm))) :=
    IsClosedImmersion.isIso_of_ker_eq ι₁ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι _
      hu₁ (hker.trans hkT.symm)
  refine ⟨asIso (IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH)),
    asIso (IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
      (le_of_eq (hkT.trans hker.symm))), hu, hu₁, ?_⟩
  rw [← cancel_mono (Scheme.Hom.ker ι).subschemeι, Category.assoc,
    strictTransformSubschemeLift_comp_subschemeι π Z (Scheme.Hom.ker ι), ← Category.assoc]
  simp only [asIso_hom]
  rw [hu₁, Category.assoc, hu, hsq]

theorem comap_strictTransform_of_closedImmersion_commSq {X X₁ S S₁ : Scheme.{u}}
    {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    [IsLocallyNoetherian X₁] [IsLocallyNoetherian S₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι))
    (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (Scheme.Hom.ker ι :: E))
    (hHZ : Scheme.Hom.ker ι ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    (Blowup.strictTransform π Z D).comap ι₁ =
      Blowup.strictTransform ρ (Z.comap ι) (D.comap ι) := by
  obtain ⟨e, e₁, he, he₁, hcomm⟩ :=
    exists_iso_subscheme_of_ker_eq_strictTransform π Z ι ι₁ ρ hsq hker
  have : IsLocallyNoetherian (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subscheme :=
    isLocallyNoetherian_subscheme _
  have hq := isBlowupAlongIdealSheaf_strictTransformSubschemeLift π Z (Scheme.Hom.ker ι) hπ
  have hfinal : (e₁.hom ≫ strictTransformSubschemeLift π Z (Scheme.Hom.ker ι)) ≫
      (Scheme.Hom.ker ι).subschemeι = ρ ≫ ι := by
    rw [Category.assoc, strictTransformSubschemeLift_comp_subschemeι, ← Category.assoc, he₁, hsq]
  have hmain := comap_strictTransform_eq_strictTransformSubschemeLift p π Z (Scheme.Hom.ker ι) E hsnc hHZ hπ D hD
  have h1 : (Blowup.strictTransform π Z D).comap ι₁
      = ((Blowup.strictTransform π Z D).comap
          (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι).comap e₁.hom := by
    rw [← he₁, Scheme.IdealSheafData.comap_comp]
  rw [h1, hmain, comap_strictTransform_of_iso
    (strictTransformSubschemeLift π Z (Scheme.Hom.ker ι)) e₁ (Z.comap (Scheme.Hom.ker ι).subschemeι)
    (D.comap (Scheme.Hom.ker ι).subschemeι) hq.1]
  refine strictTransform_eq_of_comap_eq _ ρ _ _ _ _ ?_ ?_
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfinal]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfinal]

theorem comap_exceptionalIdeal_of_commSq {X X₁ S S₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S) (hsq : ι₁ ≫ π = ρ ≫ ι)
    (Z : X.IdealSheafData) :
    (Blowup.exceptionalIdeal π Z).comap ι₁ = Blowup.exceptionalIdeal ρ (Z.comap ι) := by
  rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hsq]

theorem map_comap_strictTransform_append_exceptionalIdeal {X X₁ S S₁ : Scheme.{u}}
    {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    [IsLocallyNoetherian X₁] [IsLocallyNoetherian S₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι))
    (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (Scheme.Hom.ker ι :: E))
    (hHZ : Scheme.Hom.ker ι ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    (List.map (Blowup.strictTransform π Z) E ++ [Blowup.exceptionalIdeal π Z]).map
        (fun A => A.comap ι₁) =
      List.map (Blowup.strictTransform ρ (Z.comap ι)) (List.map (fun D => D.comap ι) E) ++
        [Blowup.exceptionalIdeal ρ (Z.comap ι)] := by
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left ?_
    intro D hD
    exact comap_strictTransform_of_closedImmersion_commSq p π Z ι ι₁ ρ hsq hker E hsnc hHZ hπ D hD
  · rw [comap_exceptionalIdeal_of_commSq π ι ι₁ ρ hsq Z]

end FunctorialResolution.EmbeddedResolution

end
end

