module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0002
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0002

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {Z : X.IdealSheafData}
  {E : List X.IdealSheafData}

theorem hasStrictNormalCrossingsWith_exceptionalIdeal (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    HasStrictNormalCrossingsWith (π ≫ p) (Blowup.exceptionalIdeal π Z) [] := by
  rw [hasStrictNormalCrossingsWith_iff]
  intro x hx
  rw [Blowup.exceptionalIdeal_eq_comap] at hx
  have hy : π.base x ∈ Z.support := by
    simp only [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hy
  have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
  obtain ⟨s, hs, hxs⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
  refine ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxs, m,
    (blowupChartOfIsBlowup π c S hπ hZU s hs).chart, fun _ => none, {s}, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · intro i hi
    exact absurd hi (Nat.not_lt_zero i)
  · exact BlowupChart.restrictIdeal_exceptionalIdeal
      (blowupChartOfIsBlowup π c S hπ hZU s hs) Z hs hZU

theorem isSmoothDivisor_exceptionalIdeal (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    IsSmoothDivisor (π ≫ p) (Blowup.exceptionalIdeal π Z) := by
  have hsmooth : Smooth ((Blowup.exceptionalIdeal π Z).subschemeι ≫ (π ≫ p)) :=
    smooth_subschemeι_comp_of_hasStrictNormalCrossingsWith (Blowup.exceptionalIdeal π Z) []
      (hasStrictNormalCrossingsWith_exceptionalIdeal hZ hπ)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := by
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact hπ.1
  exact (isSmoothDivisor_iff (π ≫ p) (Blowup.exceptionalIdeal π Z)).mpr ⟨hcart, hsmooth⟩

private theorem smooth_ι_comp_of_etaleChart {Y : Scheme.{u}} {K : Type u}
    [Field K] {q : Y ⟶ Spec (CommRingCat.of K)} {V : Y.Opens} {n : ℕ} (c : EtaleChart q V n) :
    Smooth (V.ι ≫ q) := by
  have := c.isEtale
  have hsm : Smooth c.map := inferInstance
  have hsa : Smooth (affineSpaceFinToSpec K n) := affineSpaceIsSmooth K n
  rw [← c.comp_struct]
  infer_instance

theorem smooth_comp_of_isBlowupAlongIdealSheaf [Smooth p] (hZ : HasStrictNormalCrossingsWith p Z E) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    Smooth (π ≫ p) := by
  have key : ∀ x : ↥X₁, ∃ V : X₁.Opens, x ∈ V ∧ Smooth (V.ι ≫ (π ≫ p)) := by
    intro x
    by_cases hxs : π.base x ∈ Z.support
    · obtain ⟨U, hyU, m, c, a, S, -, -, -, hZU⟩ := hZ.exists_etaleChart hxs
      have hxU : x ∈ (TopologicalSpace.Opens.map π.base).obj U := hyU
      obtain ⟨s, hs, hxB⟩ := exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf π c S hπ hZU x hxU
      exact ⟨(blowupChartOfIsBlowup π c S hπ hZU s hs).domain, hxB,
        smooth_ι_comp_of_etaleChart (blowupChartOfIsBlowup π c S hπ hZU s hs).chart⟩
    · refine ⟨π ⁻¹ᵁ Z.support.compl, hxs, ?_⟩
      have : IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl) :=
        Blowup.blowupIsIsoOffCenter X X₁ π Z hπ
      have h1 : (π ⁻¹ᵁ Z.support.compl).ι ≫ (π ≫ p) =
          AlgebraicGeometry.morphismRestrict π Z.support.compl ≫
            (Scheme.Opens.ι Z.support.compl ≫ p) := by
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      rw [h1]
      infer_instance
  choose U hU hsm using key
  have hUtop : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hU x⟩
  exact smooth_of_iSup_eq_top (π ≫ p) U hUtop hsm

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
section
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem etaleChart_restrictOpens_map_comp_affineSpaceFinToSpec {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) :
    (V.ι ≫ c.map) ≫ affineSpaceFinToSpec k m = V.ι ≫ (U.ι ≫ p) := by
  rw [Category.assoc, c.comp_struct]

theorem etaleChart_restrictOpens_map_etale {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) :
    AlgebraicGeometry.Etale (V.ι ≫ c.map) := by
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  infer_instance

def EtaleChart.restrictOpens {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) : EtaleChart (U.ι ≫ p) V m where
  map := V.ι ≫ c.map
  comp_struct := etaleChart_restrictOpens_map_comp_affineSpaceFinToSpec c V
  isEtale := etaleChart_restrictOpens_map_etale c V

@[simp]
theorem EtaleChart.restrictOpens_map {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) :
    (c.restrictOpens V).map = V.ι ≫ c.map := rfl

theorem EtaleChart.restrictIdeal_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (V : U.toScheme.Opens) (T : Finset (Fin m)) :
    restrictIdeal (c.coordIdeal T) V = (c.restrictOpens V).coordIdeal T := by
  simp only [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrictOpens_map,
    Scheme.IdealSheafData.comap_comp]

theorem EtaleChart.coordIdeal_ideal_eq_span {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : U.toScheme.Opens} (hV : IsAffineOpen V) (T : Finset (Fin m)) :
    (c.coordIdeal T).ideal ⟨V, hV⟩ = Ideal.span ((c.restrictOpens V).coord '' ↑T) :=
  EtaleChart.ideal_eq_span_coord (c.restrictOpens V) hV (c.coordIdeal T) T
    (c.restrictIdeal_coordIdeal V T)

theorem EtaleChart.coordIdeal_singleton_ideal_eq_span {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    {V : U.toScheme.Opens} (hV : IsAffineOpen V) (i : Fin m) :
    (c.coordIdeal {i}).ideal ⟨V, hV⟩ = Ideal.span {(c.restrictOpens V).coord i} := by
  rw [c.coordIdeal_ideal_eq_span hV {i}, Finset.coe_singleton, Set.image_singleton]

theorem EtaleChart.saturation_mul_coordIdeal {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (j s : Fin m) (hjs : j ≠ s)
    [QuasiCompact (saturationι (c.coordIdeal {s})
      (c.coordIdeal {j} * c.coordIdeal {s}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {j} * c.coordIdeal {s}) = c.coordIdeal {j} := by
  have key : ∀ V : U.toScheme.affineOpens,
      (saturation (c.coordIdeal {s}) (c.coordIdeal {j} * c.coordIdeal {s})).ideal V =
        (c.coordIdeal {j}).ideal V := by
    intro V
    have ht : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 s
    have hu : (c.coordIdeal {j}).ideal V = Ideal.span {(c.restrictOpens V.1).coord j} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 j
    have hfactor : (c.coordIdeal {j} * c.coordIdeal {s}).ideal V =
        Ideal.span {(c.restrictOpens V.1).coord s} * (c.coordIdeal {j}).ideal V := by
      rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ht]
      exact mul_comm _ _
    have hJ : ∀ g : Γ(U.toScheme, V.1),
        (c.restrictOpens V.1).coord s * g ∈ (c.coordIdeal {j}).ideal V →
          g ∈ (c.coordIdeal {j}).ideal V := by
      intro g hg
      rw [hu] at hg ⊢
      exact mem_span_coord_of_coord_mul_mem V.2 (c.restrictOpens V.1) hjs g hg
    exact saturation_ideal_eq_of_eq_mul _ _ V _ ht _ hfactor hJ
  exact Scheme.IdealSheafData.ext (funext key)

theorem EtaleChart.saturation_coordIdeal_self {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m) (s : Fin m)
    [QuasiCompact (saturationι (c.coordIdeal {s}) (c.coordIdeal {s}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {s}) = ⊤ := by
  have key : ∀ V : U.toScheme.affineOpens,
      (saturation (c.coordIdeal {s}) (c.coordIdeal {s})).ideal V = ⊤ := by
    intro V
    have ht : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
      c.coordIdeal_singleton_ideal_eq_span V.2 s
    exact saturation_ideal_eq_top_of_span_pow_le (c.coordIdeal {s}) (c.coordIdeal {s}) V
      ((c.restrictOpens V.1).coord s) ht 1 (by simp [ht])
  ext V
  simp [key V, Scheme.IdealSheafData.ideal_top, Pi.top_apply]

private theorem mem_span_coord_of_coord_pow_mul_mem {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ}
    (hU : IsAffineOpen U) (c : EtaleChart p U m) {j s : Fin m} (hjs : j ≠ s) :
    ∀ (n : ℕ) (x : ↑(X.presheaf.obj (op U))),
      c.coord s ^ n * x ∈ Ideal.span {c.coord j} → x ∈ Ideal.span {c.coord j} := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simpa using hx
  | succ n ih =>
      intro x hx
      refine mem_span_coord_of_coord_mul_mem hU c hjs x (ih (c.coord s * x) ?_)
      have h : c.coord s ^ n * (c.coord s * x) = c.coord s ^ (n + 1) * x := by ring
      rw [h]
      exact hx

theorem EtaleChart.saturation_coordIdeal_of_ne {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U : X.Opens} {m : ℕ} (c : EtaleChart p U m)
    (j s : Fin m) (hjs : j ≠ s)
    [QuasiCompact (saturationι (c.coordIdeal {s}) (c.coordIdeal {j}))] :
    saturation (c.coordIdeal {s}) (c.coordIdeal {j}) = c.coordIdeal {j} := by
  ext V f
  have hVs : (c.coordIdeal {s}).ideal V = Ideal.span {(c.restrictOpens V.1).coord s} :=
    c.coordIdeal_singleton_ideal_eq_span V.2 s
  have hVj : (c.coordIdeal {j}).ideal V = Ideal.span {(c.restrictOpens V.1).coord j} :=
    c.coordIdeal_singleton_ideal_eq_span V.2 j
  rw [mem_saturation_ideal_iff (c.coordIdeal {s}) (c.coordIdeal {j}) V
      ((c.restrictOpens V.1).coord s) hVs f, hVj]
  constructor
  · rintro ⟨n, hn⟩
    exact mem_span_coord_of_coord_pow_mul_mem V.2 (c.restrictOpens V.1) hjs n f hn
  · intro hf
    exact ⟨0, by simpa using hf⟩

namespace BlowupChart

variable {X X₁ : Scheme.{u}} {k : Type u} [Field k]
  {p : X ⟶ Spec (CommRingCat.of k)} {π : X₁ ⟶ X} {U : X.Opens} {m : ℕ}
  {c : EtaleChart p U m} {S : Finset (Fin m)} {s : Fin m}

theorem restrictIdeal_strictTransform_of_mem_of_ne (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (j : Fin m) (hj : j ∈ S) (hjs : j ≠ s)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = B.chart.coordIdeal {j} := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain =
      B.chart.coordIdeal {j} * B.chart.coordIdeal {s} :=
    B.restrictIdeal_comap_coordIdeal_of_mem D j hj hjs hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_mul_coordIdeal j s hjs

theorem restrictIdeal_strictTransform_coordIdeal_self (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (hD : restrictIdeal D U = c.coordIdeal {s}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = ⊤ := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {s} :=
    B.restrictIdeal_comap_coordIdeal_self D hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_coordIdeal_self s

theorem restrictIdeal_strictTransform_coordIdeal_of_notMem (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (j : Fin m) (hj : j ∉ S)
    (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = B.chart.coordIdeal {j} := by
  have hqc : QuasiCompact (saturationι (Z.comap π) (D.comap π)) :=
    inferInstanceAs (QuasiCompact (strictTransformι π Z D))
  have hjs : j ≠ s := by
    rintro rfl
    exact hj hs
  have hE : restrictIdeal (Z.comap π) B.domain = B.chart.coordIdeal {s} := by
    have h := B.restrictIdeal_exceptionalIdeal Z hs hZ
    rwa [Blowup.exceptionalIdeal_eq_comap] at h
  have hDrestrict : restrictIdeal (D.comap π) B.domain = B.chart.coordIdeal {j} :=
    B.restrictIdeal_comap_coordIdeal_of_not_mem D j hj hD
  have hq := quasiCompact_saturationι_restrictIdeal (Z.comap π) (D.comap π) B.domain
  rw [hE, hDrestrict] at hq
  have := hq
  rw [strictTransform_eq_saturation, restrictIdeal_saturation (Z.comap π) (D.comap π) B.domain,
    hE, hDrestrict]
  exact B.chart.saturation_coordIdeal_of_ne j s hjs

theorem restrictIdeal_strictTransform_coordIdeal (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) [QuasiCompact (strictTransformι π Z D)]
    (hs : s ∈ S) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (j : Fin m) (hD : restrictIdeal D U = c.coordIdeal {j}) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain =
      if j = s then ⊤ else B.chart.coordIdeal {j} := by
  by_cases hj : j = s
  · rw [if_pos hj]
    have hD' : restrictIdeal D U = c.coordIdeal {s} := by rw [hD, hj]
    exact B.restrictIdeal_strictTransform_coordIdeal_self Z D hs hZ hD'
  · rw [if_neg hj]
    by_cases hjS : j ∈ S
    · exact B.restrictIdeal_strictTransform_of_mem_of_ne Z D hs hZ j hjS hj hD
    · exact B.restrictIdeal_strictTransform_coordIdeal_of_notMem Z D hs hZ j hjS hD

theorem restrictIdeal_strictTransform_of_eq_top (B : BlowupChart π c S s)
    (Z D : X.IdealSheafData) (hD : restrictIdeal D U = ⊤) :
    restrictIdeal (Blowup.strictTransform π Z D) B.domain = ⊤ := by
  have h1 : restrictIdeal (D.comap π) B.domain = ⊤ := B.restrictIdeal_comap_top D hD
  have h2 : D.comap π ≤ Blowup.strictTransform π Z D := comap_le_strictTransform π Z D
  have h3 : restrictIdeal (D.comap π) B.domain ≤
      restrictIdeal (Blowup.strictTransform π Z D) B.domain := by
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι]
    exact Scheme.IdealSheafData.comap_mono (Scheme.Opens.ι B.domain) h2
  rw [h1] at h3
  exact le_antisymm le_top h3

end BlowupChart

end FunctorialResolution.EmbeddedResolution

end
end

