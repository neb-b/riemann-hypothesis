module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequenceBoundary
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem inStrictNormalCrossingPositionAt_comap_iso {X X₀ : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (e : X₀ ≅ X) (E : List X.IdealSheafData) (x₀ : X₀)
    (h : InStrictNormalCrossingPositionAt p E (e.hom.base x₀)) :
    InStrictNormalCrossingPositionAt (e.hom ≫ p) (E.map (fun D => D.comap e.hom)) x₀ := by
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := h.exists_etaleChart
  have hiso : IsIso (e.hom.resLE U (e.hom ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have hcet : AlgebraicGeometry.Etale c.map := c.isEtale
  have hAet : AlgebraicGeometry.Etale (e.hom.resLE U (e.hom ⁻¹ᵁ U) le_rfl) := inferInstance
  have hmem : x₀ ∈ e.hom ⁻¹ᵁ U := hxU
  refine inStrictNormalCrossingPositionAt_of_exists_etaleChart
    ⟨e.hom ⁻¹ᵁ U, hmem, m,
      ⟨e.hom.resLE U (e.hom ⁻¹ᵁ U) le_rfl ≫ c.map, ?_, inferInstance⟩, a, ?_, ?_, ?_⟩
  · rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  · intro i hi j hj t hit hjt
    exact h1 i (by simpa using hi) j (by simpa using hj) t hit hjt
  · intro i hi hnone
    have hi' : i < E.length := by simpa using hi
    have hget : (E.map (fun D => D.comap e.hom))[i]'hi = (E[i]'hi').comap e.hom := by simp
    rw [hget,
      restrictIdeal_comap_eq_comap_resLE_restrictIdeal e.hom (E[i]'hi') U (e.hom ⁻¹ᵁ U) le_rfl,
      h2 i hi' hnone]
    simp
  · intro i hi t hit
    have hi' : i < E.length := by simpa using hi
    have key : restrictIdeal ((E[i]'hi').comap e.hom) (e.hom ⁻¹ᵁ U)
        = (coordSubspaceIdeal k m {t}).comap
            (e.hom.resLE U (e.hom ⁻¹ᵁ U) le_rfl ≫ c.map) := by
      rw [restrictIdeal_comap_eq_comap_resLE_restrictIdeal e.hom (E[i]'hi') U (e.hom ⁻¹ᵁ U) le_rfl,
        h3 i hi' t hit, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← Scheme.IdealSheafData.comap_comp]
    have hget : (E.map (fun D => D.comap e.hom))[i]'hi = (E[i]'hi').comap e.hom := by simp
    rw [hget]
    exact key

theorem inStrictNormalCrossingPosition_comp_iso_hom {X X₀ : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (e : X₀ ≅ X) (E : List X.IdealSheafData)
    (h : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition (e.hom ≫ p) (E.map (fun D => D.comap e.hom)) := by
  obtain ⟨-, hpt⟩ := (inStrictNormalCrossingPosition_iff p E).mp h
  refine (inStrictNormalCrossingPosition_iff _ _).mpr
    ⟨?_, fun x₀ => inStrictNormalCrossingPositionAt_comap_iso p e E x₀ (hpt (e.hom.base x₀))⟩
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
  refine isSmoothDivisor_of_locally_coordIdeal _ ?_
  intro x
  obtain ⟨U₀, hxU₀, n, c₀, a, k1, k2, k3⟩ :=
    (inStrictNormalCrossingPositionAt_comap_iso p e E x (hpt (e.hom.base x))).exists_etaleChart
  refine ⟨U₀, hxU₀, n, c₀, ?_⟩
  rcases hai : a i with _ | t
  · exact Or.inl (k2 i hi hai)
  · exact Or.inr ⟨t, k3 i hi t hai⟩

namespace IdealBlowupSequence

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

theorem structureMorphism_zero (s : IdealBlowupSequence p I E) :
    s.structureMorphism 0 = s.toSequenceOfBlowups.isoZero.hom ≫ p := by
  rw [structureMorphism_def, SequenceOfBlowups.projectionToBase_zero]

theorem structureMorphism_succ (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.structureMorphism (i + 1) = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.structureMorphism i := by
  rw [structureMorphism_def, structureMorphism_def, SequenceOfBlowups.blowupMorphism_eq_transitionMap, ← Category.assoc,
    SequenceOfBlowups.transitionMap_comp_projectionToBase]

theorem smooth_structureMorphism [AlgebraicGeometry.Smooth p] (s : IdealBlowupSequence p I E) (i : ℕ)
    (hi : i ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.Smooth (s.structureMorphism i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    rw [structureMorphism_zero]
    infer_instance
  | succ n ih =>
    intro hi
    have hn : n < s.toSequenceOfBlowups.length := hi
    have := ih (le_of_lt hn)
    rw [structureMorphism_succ]
    exact smooth_comp_of_isBlowupAlongIdealSheaf (s.hasStrictNormalCrossingsWith_center n hn)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem inStrictNormalCrossingPosition_boundary [AlgebraicGeometry.Smooth p] (s : IdealBlowupSequence p I E)
    (hE : InStrictNormalCrossingPosition p E)
    (hN : ∀ i, i ≤ s.toSequenceOfBlowups.length → NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt i)) :
    ∀ i, i ≤ s.toSequenceOfBlowups.length → InStrictNormalCrossingPosition (s.structureMorphism i) (s.boundary i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hb : s.boundary 0 = E.map (fun D => D.comap s.toSequenceOfBlowups.isoZero.hom) := by
      rw [s.boundary_zero, SequenceOfBlowups.projectionToBase_zero]
    rw [hb, structureMorphism_zero]
    exact inStrictNormalCrossingPosition_comp_iso_hom p s.toSequenceOfBlowups.isoZero E hE
  | succ n ih =>
    intro hi
    have hn : n < s.toSequenceOfBlowups.length := hi
    have : NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt (n + 1)) := hN (n + 1) hi
    have key := inStrictNormalCrossingPosition_strictTransform_append (s.structureMorphism n)
      (s.toSequenceOfBlowups.transitionMapSucc n) (s.toSequenceOfBlowups.center n) (s.boundary n)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn) (ih (le_of_lt hn))
      (s.hasStrictNormalCrossingsWith_center n hn)
    rw [structureMorphism_succ, s.boundary_succ_eq_map_strictTransform_append n hn]
    exact key

theorem isNoetherian_schemeAt [AlgebraicGeometry.IsNoetherian X] (s : IdealBlowupSequence p I E) (i : ℕ)
    (hi : i ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt i) :=
  EmbeddedResolution.isNoetherian_schemeAt s.toSequenceOfBlowups i hi

theorem inStrictNormalCrossingPosition_boundary_of_isNoetherian [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.IsNoetherian X] (s : IdealBlowupSequence p I E) (hE : InStrictNormalCrossingPosition p E) :
    ∀ i, i ≤ s.toSequenceOfBlowups.length → InStrictNormalCrossingPosition (s.structureMorphism i) (s.boundary i) := by
  refine inStrictNormalCrossingPosition_boundary s hE ?_
  intro i hi
  have := s.isNoetherian_schemeAt i hi
  infer_instance

end IdealBlowupSequence

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem inStrictNormalCrossingPosition_comap_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) (e : X ≅ Y) (L : List Y.IdealSheafData)
    (h : InStrictNormalCrossingPosition q L) :
    InStrictNormalCrossingPosition (e.hom ≫ q) (L.map (fun D => D.comap e.hom)) := by
  rw [inStrictNormalCrossingPosition_iff] at h ⊢
  refine ⟨?_, ?_⟩
  · intro D hD
    rw [List.mem_map] at hD
    obtain ⟨D', hD', rfl⟩ := hD
    exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso q e D' (h.1 D' hD')
  · intro x
    obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := h.2 (e.hom.base x)
    refine ⟨(TopologicalSpace.Opens.map e.hom.base).obj U, hxU, m,
      EtaleChart.ofIso q e c, a, ?_, ?_, ?_⟩
    · intro i hi j hj t hti htj
      exact hinj i (by simpa using hi) j (by simpa using hj) t hti htj
    · intro i hi ha
      have hi' : i < L.length := by simpa using hi
      simp only [List.getElem_map]
      rw [restrictIdeal_comap, hnone i hi' ha, Scheme.IdealSheafData.comap_top]
    · intro i hi t ht
      have hi' : i < L.length := by simpa using hi
      simp only [List.getElem_map]
      rw [restrictIdeal_comap, hsome i hi' t ht, EtaleChart.ofIso_coordIdeal]

namespace MarkedSequenceOfBlowups

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}

theorem projectionToSpec_zero (s : MarkedSequenceOfBlowups p I m E) :
    s.projectionToSpec 0 = s.toSequenceOfBlowups.isoZero.hom ≫ p := by
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToBase_zero]

theorem projectionToSpec_succ (s : MarkedSequenceOfBlowups p I m E) (i : ℕ) :
    s.projectionToSpec (i + 1) = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.projectionToSpec i := by
  have h : s.toSequenceOfBlowups.transitionMapSucc i ≫ s.toSequenceOfBlowups.projectionToBase i
      = s.toSequenceOfBlowups.projectionToBase (i + 1) := by
    rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap i]
    exact s.toSequenceOfBlowups.transitionMap_comp_projectionToBase (Nat.le_succ i)
  rw [MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedSequenceOfBlowups.projectionToSpec_eq, ← h, Category.assoc]

theorem isNoetherian_schemeAt (_hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt i) := by
  induction i with
  | zero =>
      have : AlgebraicGeometry.IsNoetherian T.scheme := hT.isNoetherian
      exact isNoetherian_of_iso s.toSequenceOfBlowups.isoZero.symm
  | succ n ih =>
      have hn : n < s.toSequenceOfBlowups.length := hi
      have : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt n) := ih (le_of_lt hn)
      exact isNoetherian_of_isBlowupAlongIdealSheaf (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

end MarkedSequenceOfBlowups

private theorem smooth_and_inStrictNormalCrossingPosition_projectionToSpec (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ i : ℕ, i ≤ s.toSequenceOfBlowups.length →
      AlgebraicGeometry.Smooth (s.projectionToSpec i) ∧ InStrictNormalCrossingPosition (s.projectionToSpec i) (s.boundary i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
      refine ⟨?_, ?_⟩
      · rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
        infer_instance
      · rw [MarkedSequenceOfBlowups.projectionToSpec_zero, s.boundary_zero]
        exact inStrictNormalCrossingPosition_comap_iso T.structMap s.toSequenceOfBlowups.isoZero T.boundary hT.snc
  | succ n ih =>
      intro hn
      have hn' : n < s.toSequenceOfBlowups.length := hn
      obtain ⟨hsm, hsnc⟩ := ih (le_of_lt hn')
      have : AlgebraicGeometry.Smooth (s.projectionToSpec n) := hsm
      have : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (n + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s (n + 1) hn
      have : TopologicalSpace.NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt (n + 1)) := inferInstance
      have hπ := s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn'
      have hZE : HasStrictNormalCrossingsWith (s.projectionToSpec n) (s.toSequenceOfBlowups.center n) (s.boundary n) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc n hn'
      refine ⟨?_, ?_⟩
      · rw [MarkedSequenceOfBlowups.projectionToSpec_succ]
        exact smooth_comp_of_isBlowupAlongIdealSheaf hZE hπ
      · rw [MarkedSequenceOfBlowups.projectionToSpec_succ, s.boundary_succ n hn']
        exact inStrictNormalCrossingPosition_strictTransform_append (s.projectionToSpec n) (s.toSequenceOfBlowups.transitionMapSucc n)
          (s.toSequenceOfBlowups.center n) (s.boundary n) hπ hsnc hZE

namespace MarkedSequenceOfBlowups

theorem smooth_projectionToSpec (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.Smooth (s.projectionToSpec i) :=
  (smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi).1

theorem inStrictNormalCrossingPosition_projectionToSpec_boundary (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    InStrictNormalCrossingPosition (s.projectionToSpec i) (s.boundary i) :=
  (smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi).2

end MarkedSequenceOfBlowups

def DimensionNonincreasingAlongBlowups : Prop :=
  ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
    krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc

namespace MarkedIdealWithBoundary

def transformAt (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) : MarkedIdealWithBoundary.{u} where
  base := T.base
  instField := T.instField
  scheme := s.toSequenceOfBlowups.schemeAt i
  structMap := s.projectionToSpec i
  ideal := s.ideal i
  mult := T.mult
  boundary := s.boundary i

@[simp]
theorem transformAt_structureMorphism (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).structMap = s.projectionToSpec i := rfl

@[simp]
theorem transformAt_boundary (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).boundary = s.boundary i := rfl

@[simp]
theorem transformAt_dim (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ) :
    (T.transformAt s i).krullDimSucc = EmbeddedResolution.krullDimSucc (s.toSequenceOfBlowups.schemeAt i) := rfl

theorem IsAdmissible.transformAt (hcart : EffectiveCartierSupportContainsNoComponent.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hT : T.IsAdmissible) (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (T.transformAt s i).IsAdmissible := by
  obtain ⟨hsm, hsnc⟩ := smooth_and_inStrictNormalCrossingPosition_projectionToSpec hcart hT s i hi
  have : AlgebraicGeometry.Smooth (s.projectionToSpec i) := hsm
  have : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt hcart hT s i hi
  have : TopologicalSpace.NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt i) := inferInstance
  refine
    { charZero := hT.charZero
      locallyOfFiniteType := ?_
      nonzeroOnComponents := MarkedSequenceOfBlowups.nonzeroOnComponents_ideal_of_isAdmissible hcart hT s i hi
      one_le_mult := hT.one_le_mult
      quasiCompact := ?_
      smooth := hsm
      snc := hsnc }
  · show AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec i)
    infer_instance
  · show AlgebraicGeometry.QuasiCompact (s.projectionToSpec i)
    exact ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩

theorem transformAt_dim_le (hdim : DimensionNonincreasingAlongBlowups.{u}) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.toSequenceOfBlowups.length) :
    (T.transformAt s i).krullDimSucc ≤ T.krullDimSucc :=
  hdim T hT s i hi

end MarkedIdealWithBoundary

end FunctorialResolution.EmbeddedResolution

end
end

