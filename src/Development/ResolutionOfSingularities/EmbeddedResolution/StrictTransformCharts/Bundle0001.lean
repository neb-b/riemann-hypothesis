module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0005
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0002

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

universe u

structure BlowupChart {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) (s : Fin m) where
  domain : X₁.Opens
  domain_le : domain ≤ π ⁻¹ᵁ U
  chart : EtaleChart (π ≫ p) domain m
  comm : chart.map ≫ coordBlowupSubstMap k m S s = π.resLE U domain domain_le ≫ c.map

private theorem exists_opens_isPullback_of_opens {X₁ M : Scheme.{u}} (V : X₁.Opens)
    (q : V.toScheme ⟶ M) (W : M.Opens) :
    ∃ (dom : X₁.Opens) (_hle : dom ≤ V) (g : dom.toScheme ⟶ W.toScheme)
      (r : dom.toScheme ⟶ V.toScheme),
      IsPullback g r W.ι q ∧ r ≫ V.ι = dom.ι ∧
        ∀ y, q.base y ∈ W → V.ι.base y ∈ dom := by
  classical
  have hdle : Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι) ≤ V := by
    rintro x ⟨y, rfl⟩
    have h1 : V.ι.base ((q ⁻¹ᵁ W).ι.base y) ∈ Set.range V.ι.base := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h1
    exact h1
  obtain ⟨e, he⟩ : ∃ e : (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).toScheme ≅
      (q ⁻¹ᵁ W).toScheme,
      e.hom ≫ ((q ⁻¹ᵁ W).ι ≫ V.ι) = (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).ι :=
    ⟨IsOpenImmersion.isoOfRangeEq (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).ι
        ((q ⁻¹ᵁ W).ι ≫ V.ι) (Scheme.Opens.range_ι _),
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  refine ⟨Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι), hdle, e.hom ≫ (q ∣_ W),
    e.hom ≫ (q ⁻¹ᵁ W).ι, ?_, ?_, ?_⟩
  · have h1 : IsPullback e.hom (e.hom ≫ (q ⁻¹ᵁ W).ι) ((q ⁻¹ᵁ W).ι) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    have h2 := h1.paste_horiz (isPullback_morphismRestrict q W)
    rwa [Category.id_comp] at h2
  · rw [Category.assoc]
    exact he
  · intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩

theorem exists_blowupChart_family_isPullback_covering {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) (Z : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    ∃ F : ∀ s : Fin m, s ∈ S → BlowupChart π c S s,
      (∀ (s : Fin m) (hs : s ∈ S),
          IsPullback (F s hs).chart.map
            (π.resLE U (F s hs).domain (F s hs).domain_le)
            (coordBlowupSubstMap k m S s) c.map) ∧
      (∀ x : ↥X₁, x ∈ π ⁻¹ᵁ U → ∃ (s : Fin m) (hs : s ∈ S), x ∈ (F s hs).domain) := by
  classical
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : AlgebraicGeometry.Flat c.map := inferInstance
  have hcomap : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, hZ, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  have hres : Blowup.IsBlowupAlongIdealSheaf (π ∣_ U) ((coordSubspaceIdeal k m S).comap c.map) := by
    have h1 := hπ.restrict U
    rwa [hcomap] at h1
  obtain ⟨q, -, hq⟩ := (isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap k m S).exists_isPullback_of_flat c.map hres
  have key : ∀ (s : Fin m) (hs : s ∈ S), ∃ B : BlowupChart π c S s,
      IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map ∧
        ∀ y, q.base y ∈ Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs) →
          (π ⁻¹ᵁ U).ι.base y ∈ B.domain := by
    intro s hs
    obtain ⟨dom, hle, g, r, hpb, hrι, hmem⟩ :=
      exists_opens_isPullback_of_opens (π ⁻¹ᵁ U) q (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs))
    have hrange : Set.range (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι.base
        = Set.range (affineSpaceCoordBlowupChart k m S s hs).base :=
      Scheme.Opens.range_ι (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs))
    obtain ⟨eW, heW⟩ : ∃ e : (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).toScheme ≅
        affineSpaceFin k m,
        e.hom ≫ coordBlowupSubstMap k m S s =
          (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι ≫ affineSpaceCoordBlowupMap k m S := by
      refine ⟨IsOpenImmersion.isoOfRangeEq
          (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
          (affineSpaceCoordBlowupChart k m S s hs) hrange ≪≫ specCoordBlowupChartRingIsoAffineSpace k m S s hs, ?_⟩
      have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
        (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
        (affineSpaceCoordBlowupChart k m S s hs) hrange
      rw [Iso.trans_hom, Category.assoc, ← affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap,
        ← Category.assoc, hfac]
    have heW' : eW.inv ≫ (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι ≫
        affineSpaceCoordBlowupMap k m S = coordBlowupSubstMap k m S s := by
      rw [← heW, Iso.inv_hom_id_assoc]
    have hleft : r ≫ (π ∣_ U) = π.resLE U dom hle := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι,
        ← Category.assoc, hrι]
    have hsq : IsPullback (g ≫ eW.hom) (π.resLE U dom hle) (coordBlowupSubstMap k m S s) c.map := by
      have h1 : IsPullback (g ≫ eW.hom) (𝟙 _) eW.inv g :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      have h2 := h1.paste_vert (hpb.paste_vert hq)
      rwa [Category.id_comp, hleft, heW'] at h2
    have hetale : AlgebraicGeometry.Etale (g ≫ eW.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip c.isEtale
    refine ⟨⟨dom, hle, ⟨g ≫ eW.hom, ?_, hetale⟩, hsq.w⟩, hsq, hmem⟩
    calc (g ≫ eW.hom) ≫ affineSpaceFinToSpec k m
        = (g ≫ eW.hom) ≫ coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m := by
          rw [coordBlowupSubstMap_comp_affineSpaceFinToSpec]
      _ = ((g ≫ eW.hom) ≫ coordBlowupSubstMap k m S s) ≫ affineSpaceFinToSpec k m := by
          simp only [Category.assoc]
      _ = (π.resLE U dom hle ≫ c.map) ≫ affineSpaceFinToSpec k m := by rw [hsq.w]
      _ = π.resLE U dom hle ≫ c.map ≫ affineSpaceFinToSpec k m := by simp only [Category.assoc]
      _ = π.resLE U dom hle ≫ U.ι ≫ p := by rw [c.comp_struct]
      _ = (π.resLE U dom hle ≫ U.ι) ≫ p := by simp only [Category.assoc]
      _ = (dom.ι ≫ π) ≫ p := by rw [Scheme.Hom.resLE_comp_ι]
      _ = dom.ι ≫ π ≫ p := by simp only [Category.assoc]
  choose F hF1 hF2 using key
  refine ⟨F, hF1, ?_⟩
  intro x hx
  have hx' : x ∈ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  have hy : q.base y ∈
      (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2)) := by
    rw [iSup_opensRange_affineSpaceCoordBlowupChart k m S]
    simp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i.1, i.2, hF2 i.1 i.2 y hi⟩

def blowupChartOfIsBlowup {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (s : Fin m) (hs : s ∈ S) : BlowupChart π c S s :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose s hs

theorem isPullback_blowupChart_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (s : Fin m) (hs : s ∈ S) :
    IsPullback (blowupChartOfIsBlowup π c S hπ hZ s hs).chart.map
      (π.resLE U (blowupChartOfIsBlowup π c S hπ hZ s hs).domain
        (blowupChartOfIsBlowup π c S hπ hZ s hs).domain_le)
      (coordBlowupSubstMap k m S s) c.map :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose_spec.1 s hs

theorem exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (x : ↥X₁) (hx : x ∈ π ⁻¹ᵁ U) :
    ∃ (s : Fin m) (hs : s ∈ S), x ∈ (blowupChartOfIsBlowup π c S hπ hZ s hs).domain :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose_spec.2 x hx

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDimensionBound
section
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}

private theorem nontrivial_sections_of_mem (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    Nontrivial Γ(X, U) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hs
  have := hs
  have h1 : (1 : Γ(X, U)) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [Subsingleton.elim (1 : Γ(X, U)) 0]
    exact Ideal.zero_mem _
  exact (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

private theorem ideal_le_primeIdealOf_of_mem_support (I : X.IdealSheafData)
    (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) (hxI : x ∈ I.support) :
    I.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := ⟨U, hU⟩) hx).mp hxI
  rw [Scheme.mem_zeroLocus_iff] at h1
  intro f hf
  rw [← germ_mem_maximalIdeal_iff hU x hx f, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact h1 f hf ((X.mem_basicOpen f x hx).mpr hu)

private theorem coord_injective (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) : Function.Injective c.coord := by
  let inst : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra_etale hU
  have : Nontrivial Γ(X, U) := nontrivial_sections_of_mem hU x hx
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := inferInstance
  have := Module.Flat.isTorsionFree (R := MvPolynomial (ULift.{u} (Fin m)) k) (M := Γ(X, U))
  have hinj0 : Function.Injective
      (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hinj : Function.Injective ⇑c.coordRingHom := hinj0
  intro a b hab
  have h1 : (MvPolynomial.X (ULift.up a) : MvPolynomial (ULift.{u} (Fin m)) k)
      = MvPolynomial.X (ULift.up b) := by
    apply hinj
    rw [EtaleChart.coordRingHom_X, EtaleChart.coordRingHom_X, hab]
  have h2 : (ULift.up a : ULift.{u} (Fin m)) = ULift.up b := MvPolynomial.X_injective h1
  exact congrArg ULift.down h2

theorem card_le_ringKrullDim_stalk (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    (J.card : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  classical
  obtain ⟨d, f, -, hf2, -, hd⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ j hj))
  rw [← hd]
  rcases Finset.eq_empty_or_nonempty J with rfl | hJne
  · simp only [Finset.card_empty]
    exact_mod_cast Nat.zero_le d
  · obtain ⟨j₀, hj₀⟩ := hJne
    obtain ⟨i₀, -⟩ := hf2 j₀ hj₀
    have hch : ∀ j : Fin m, ∃ i : Fin d, j ∈ J → f i = c.coord j := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨i, hi⟩ := hf2 j hj
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h => absurd h hj⟩
    choose g hg using hch
    have hmap : ∀ a ∈ J, g a ∈ (Finset.univ : Finset (Fin d)) := fun a _ => Finset.mem_univ _
    have hinjOn : Set.InjOn g (J : Set (Fin m)) := by
      intro a ha b hb hab
      have h1 : c.coord a = c.coord b := by
        rw [← hg a (Finset.mem_coe.mp ha), ← hg b (Finset.mem_coe.mp hb), hab]
      exact coord_injective hU c x hx h1
    have hcard : J.card ≤ (Finset.univ : Finset (Fin d)).card :=
      Finset.card_le_card_of_injOn g hmap hinjOn
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    exact_mod_cast hcard

theorem coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton
    (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (j : Fin m) (D : X.IdealSheafData) (hD : restrictIdeal D U = c.coordIdeal {j})
    (x : X) (hx : x ∈ U) (hxD : x ∈ D.support) :
    c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  have h1 : D.ideal ⟨U, hU⟩ = Ideal.span (c.coord '' ((({j} : Finset (Fin m))) : Set (Fin m))) :=
    EtaleChart.ideal_eq_span_coord c hU D {j} hD
  have h2 : D.ideal ⟨U, hU⟩ ≤ (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    ideal_le_primeIdealOf_of_mem_support D hU hx hxD
  refine h2 ?_
  rw [h1]
  exact Ideal.subset_span ⟨j, by simp, rfl⟩

end FunctorialResolution.EmbeddedResolution
end
end

