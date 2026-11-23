module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.StrictTransformLogDerivativeIdealSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupLogDerivativeIdealBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0004
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChartComputations
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformChart
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.AffineSpaceCoordinateBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PartialDerivativeIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsEraseMember
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LogDerivIdealEstimate
section
universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private noncomputable def iSupIdealSheaf {Y : Scheme.{u}} {ι : Sort v} (J : ι → Y.IdealSheafData) :
    Y.IdealSheafData where
  ideal U := ⨆ i, (J i).ideal U
  map_ideal_basicOpen := by
    intro U f
    simp only [Ideal.map_iSup]
    exact iSup_congr fun i => (J i).map_ideal_basicOpen U f

private theorem pointwiseSup_ideal {Y : Scheme.{u}} {ι : Sort v} (J : ι → Y.IdealSheafData)
    (U : Y.affineOpens) : (iSupIdealSheaf J).ideal U = ⨆ i, (J i).ideal U := rfl

private theorem ideal_iSup_le_iSup_ideal {Y : Scheme.{u}} {ι : Sort v} (J : ι → Y.IdealSheafData)
    (U : Y.affineOpens) : (⨆ i, J i).ideal U ≤ ⨆ i, (J i).ideal U := by
  have h : (⨆ i, J i) ≤ iSupIdealSheaf J := by
    refine iSup_le fun i => Scheme.IdealSheafData.le_def.mpr fun V => ?_
    rw [pointwiseSup_ideal J V]
    exact le_iSup (fun i' => (J i').ideal V) i
  have h2 := Scheme.IdealSheafData.le_def.mp h U
  rwa [pointwiseSup_ideal J U] at h2

private theorem idealSheafData_mul_le_mul_left {Y : Scheme.{u}} (F : Y.IdealSheafData)
    {A B : Y.IdealSheafData} (h : A ≤ B) : F * A ≤ F * B := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  have e1 : (F * A).ideal U = F.ideal U * A.ideal U := rfl
  have e2 : (F * B).ideal U = F.ideal U * B.ideal U := rfl
  rw [e1, e2]
  exact Ideal.mul_mono le_rfl (Scheme.IdealSheafData.le_def.mp h U)

theorem logDerivIdealSheaf_iSup_le (k : Type u) [CommRing k] [IsNoetherianRing k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (P : Y.IdealSheafData)
    {ι : Sort v} (J : ι → Y.IdealSheafData) :
    logDerivIdealSheaf k p P (⨆ i, J i) ≤ ⨆ i, logDerivIdealSheaf k p P (J i) := by
  refine Scheme.IdealSheafData.le_def.mpr fun U => ?_
  refine le_trans (@logDerivIdeal_mono k _ _ _ (sectionsAlgebra k p U.1) (P.ideal U) _ _
    (ideal_iSup_le_iSup_ideal J U)) ?_
  refine le_trans (@logDerivIdeal_iSup_le k _ _ _ (sectionsAlgebra k p U.1) ι (P.ideal U)
    (fun i => (J i).ideal U)) ?_
  exact iSup_le fun i =>
    Scheme.IdealSheafData.le_def.mp (le_iSup (fun i' => logDerivIdealSheaf k p P (J i')) i) U

theorem logDerivIdealSheafIterate_iSup_le (k : Type u) [CommRing k] [IsNoetherianRing k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (P : Y.IdealSheafData) (r : ℕ)
    {ι : Sort v} (J : ι → Y.IdealSheafData) :
    logDerivIdealSheafIterate k p P r (⨆ i, J i) ≤ ⨆ i, logDerivIdealSheafIterate k p P r (J i) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      have h1 : logDerivIdealSheafIterate k p P (r + 1) (⨆ i, J i)
          ≤ ⨆ i, logDerivIdealSheaf k p P (logDerivIdealSheafIterate k p P r (J i)) := by
        rw [logDerivIdealSheafIterate_succ]
        exact le_trans (logDerivIdealSheaf_mono k p P ih)
          (logDerivIdealSheaf_iSup_le k p P
            (fun i => logDerivIdealSheafIterate k p P r (J i)))
      refine h1.trans (iSup_le fun i => le_iSup_of_le i ?_)
      exact le_of_eq (logDerivIdealSheafIterate_succ k p P r (J i)).symm

theorem logDerivIdealSheafIterate_biSup_le (k : Type u) [CommRing k] [IsNoetherianRing k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (P : Y.IdealSheafData) (r n : ℕ)
    (J : ℕ → Y.IdealSheafData) :
    logDerivIdealSheafIterate k p P r (⨆ l, ⨆ _ : l ≤ n, J l) ≤
      ⨆ l, ⨆ _ : l ≤ n, logDerivIdealSheafIterate k p P r (J l) := by
  refine le_trans (logDerivIdealSheafIterate_iSup_le k p P r
    (fun l => ⨆ _ : l ≤ n, J l)) ?_
  refine iSup_le fun l => ?_
  refine le_trans (logDerivIdealSheafIterate_iSup_le k p P r (fun _ : l ≤ n => J l)) ?_
  exact iSup_le fun h => le_iSup_of_le l (le_iSup_of_le h le_rfl)

theorem derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_of_blowup
    (k : Type u) [Field k] [CharZero k] {X X₁ : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (π : X₁ ⟶ X) [IsLocallyNoetherian X₁]
    (Z H : X.IdealSheafData) (E : List X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z H)]
    (hsnc : HasStrictNormalCrossingsWith p Z (H :: E)) (hHZ : H ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (m : ℕ) (K : ℕ → X.IdealSheafData) (hK : ∀ l ≤ m, K l ≤ Z ^ (m - l))
    (hest : ∀ n < m,
      derivIdealSheafIterate k p n (K 0) ≤
        ⨆ l, ⨆ _ : l ≤ n, logDerivIdealSheafIterate k p H (n - l) (K l))
    (K' : ℕ → X₁.IdealSheafData)
    (hK' : ∀ l ≤ m, Blowup.exceptionalIdeal π Z ^ (m - l) * K' l = (K l).comap π)
    (n : ℕ) (hn : n < m) :
    letI : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
    derivIdealSheafIterate k (π ≫ p) n (K' 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (K' l) := by
  have hsm : AlgebraicGeometry.Smooth (π ≫ p) := smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
  show derivIdealSheafIterate k (π ≫ p) n (K' 0) ≤
      ⨆ l, ⨆ _ : l ≤ n,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (n - l) (K' l)
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal π Z) := hπ.1
  have hK0 : K 0 ≤ Z ^ m := by simpa using hK 0 (Nat.zero_le m)
  have hA : ∀ l : ℕ, derivIdealSheafIterate k p l (K 0) ≤ Z ^ (m - l) := fun l =>
    derivIdealSheafIterate_le_pow_of_hasStrictNormalCrossingsWith k p Z (K 0) (H :: E) hsnc m hK0 l
  obtain ⟨L, hLspec⟩ : ∃ L : ℕ → X₁.IdealSheafData, ∀ l : ℕ,
      Blowup.exceptionalIdeal π Z ^ (m - l) * L l = (derivIdealSheafIterate k p l (K 0)).comap π :=
    ⟨fun l => controlledTransform π Z (derivIdealSheafIterate k p l (K 0)) (m - l) hπ (hA l),
      fun l => exceptionalIdeal_pow_mul_controlledTransform π Z (derivIdealSheafIterate k p l (K 0)) (m - l) hπ (hA l)⟩
  have hL0 : L 0 = K' 0 := by
    refine Blowup.IsLocallyGeneratedByNonZeroDivisor.eq_of_mul_eq_mul (hcart.pow (m - 0)) ?_
    rw [hLspec 0, hK' 0 (Nat.zero_le m), derivIdealSheafIterate_zero]
  have hstep : ∀ l, l ≤ n → L l ≤
      ⨆ j, ⨆ _ : j ≤ l,
        logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j) := by
    intro l hl
    have hlm : l < m := lt_of_le_of_lt hl hn
    have key : ∀ j, j ≤ l → (logDerivIdealSheafIterate k p H (l - j) (K j)).comap π ≤
        Blowup.exceptionalIdeal π Z ^ (m - l) *
          logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j) := by
      intro j hj
      have hjm : j ≤ m := by omega
      have ha : l - j ≤ m - j := by omega
      have h3 := comap_logDerivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z H E hsnc hHZ hπ
        (K j) (m - j) (hK j hjm) (l - j) ha
      have h4 : K' j = controlledTransform π Z (K j) (m - j) hπ (hK j hjm) :=
        eq_controlledTransform_of_mul_eq_comap π Z (K j) (m - j) hπ (hK j hjm) (K' j) (hK' j hjm)
      have harith : m - j - (l - j) = m - l := by omega
      rw [h4, ← harith]
      exact h3
    refine Blowup.IsLocallyGeneratedByNonZeroDivisor.le_of_mul_le_mul (hcart.pow (m - l)) ?_
    rw [hLspec l]
    refine le_trans (Scheme.IdealSheafData.comap_mono π (hest l hlm)) ?_
    refine le_trans (le_of_eq (comap_iSup_le_nat π l
      (fun j => logDerivIdealSheafIterate k p H (l - j) (K j)))) ?_
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact le_trans (key j hj) (idealSheafData_mul_le_mul_left _
      (le_iSup_of_le j (le_iSup_of_le hj le_rfl)))
  have hmain := derivIdealSheafIterate_le_biSup_logDerivIdealSheafIterate_strictTransform
    k p π Z H E hsnc hHZ hπ (K 0) m L (fun l _ => hLspec l) n hn.le
  rw [hL0] at hmain
  refine le_trans hmain (iSup_le fun l => iSup_le fun hl => ?_)
  refine le_trans (logDerivIdealSheafIterate_mono k (π ≫ p) (Blowup.strictTransform π Z H) (n - l)
    (hstep l hl)) ?_
  refine le_trans (logDerivIdealSheafIterate_biSup_le k (π ≫ p) (Blowup.strictTransform π Z H)
    (n - l) l
    (fun j => logDerivIdealSheafIterate k (π ≫ p) (Blowup.strictTransform π Z H) (l - j) (K' j))) ?_
  refine iSup_le fun j => iSup_le fun hj => ?_
  rw [← logDerivIdealSheafIterate_add]
  have harith3 : n - l + (l - j) = n - j := by omega
  rw [harith3]
  exact le_iSup_of_le j (le_iSup_of_le (le_trans hj hl) le_rfl)

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryAfterBlowup
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionBoundary

private theorem mem_closeds_compl {α : Type u} [TopologicalSpace α]
    (S : TopologicalSpace.Closeds α) (x : α) : x ∈ S.compl ↔ x ∉ S := Iff.rfl

private theorem saturation_top_eq_top {Y : Scheme.{u}} (F : Y.IdealSheafData) :
    saturation F (⊤ : Y.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform (𝟙 Y) F (⊤ : Y.IdealSheafData)
  rw [strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.comap_id] at h
  exact top_le_iff.mp h

private theorem restrictIdeal_mul {X : Scheme.{u}} (A B : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (A * B) U = restrictIdeal A U * restrictIdeal B U :=
  Scheme.IdealSheafData.comap_mul A B U.ι

private theorem restrictIdeal_strictTransform_id {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z D : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (Blowup.strictTransform (𝟙 X) Z D) U =
      saturation (restrictIdeal Z U) (restrictIdeal D U) := by
  have h1 := restrictIdeal_strictTransform (𝟙 X) Z D U
  have h2 := strictTransform_comp_ι U (𝟙 U.toScheme) Z D
  rw [Category.id_comp] at h2
  rw [h1, Category.comp_id, h2, strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.comap_id]

private theorem map_eq_self_of_getElem {α : Type u} (g : α → α) : ∀ l : List α,
    (∀ (i : ℕ) (h : i < l.length), g (l[i]'h) = l[i]'h) → l.map g = l := by
  intro l h
  refine List.ext_getElem (List.length_map _) ?_
  intro i _ hi
  simpa only [List.getElem_map] using h i hi

private theorem eraseIdx_map_eq {α : Type u} (g : α → α) : ∀ (l : List α) (j : ℕ),
    (∀ (i : ℕ) (h : i < l.length), i ≠ j → g (l[i]'h) = l[i]'h) →
    (l.map g).eraseIdx j = l.eraseIdx j := by
  intro l j h
  rw [List.eraseIdx_map]
  apply map_eq_self_of_getElem
  intro k hk
  obtain ⟨i, hi, hij, heq⟩ := List.mem_eraseIdx_iff_getElem.mp (List.getElem_mem hk)
  rw [← heq]
  exact h i hi hij

theorem strictTransform_comap_boundary_of_ne (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (i : ℕ) (hi : i < T.boundary.length) (hij : i ≠ j) :
    Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨i, hi⟩).comap (𝟙 T.scheme)) = T.boundary.get ⟨i, hi⟩ := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support
  · obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
      exists_etaleChart_containedComponentsIdeal T hV j hj x hx
    refine ⟨U, hxU, ?_⟩
    rw [restrictIdeal_strictTransform_id, hZU]
    cases hai : a i with
    | none =>
        rw [hnone i hi hai]
        exact saturation_top_eq_top _
    | some t =>
        have htb : t ≠ b := by
          intro e
          apply hij
          refine hinj i j hi hj b ?_ hab
          rw [hai, e]
        have ht := hsome i hi t hai
        have hq1 : QuasiCompact
            (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩)) :=
          quasiCompact_saturationι_of_isLocallyNoetherian _ _
        have hq2 := quasiCompact_saturationι_restrictIdeal
          (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩) U
        rw [hZU, ht] at hq2
        have := hq2
        rw [ht]
        exact c.saturation_coordIdeal_of_ne t b htb
  · refine ⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl,
      (mem_closeds_compl _ _).mpr hx, ?_⟩
    have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩)
      (DivisorReduction.containedComponentsIdeal T j hj).support.compl
      (fun y hy => by
        have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
          (mem_closeds_compl _ y).mp hy
        simpa using h')
    rw [hst, Scheme.IdealSheafData.comap_id]

theorem isSmoothDivisor_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsSmoothDivisor T.structMap (DivisorReduction.containedComponentsIdeal T j hj) :=
  ⟨isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj, smooth_subschemeι_containedComponentsIdeal_comp T hV j hj⟩

theorem strictTransform_mul_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
          ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme)) *
        DivisorReduction.containedComponentsIdeal T j hj =
      T.boundary.get ⟨j, hj⟩ := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support
  · obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
      exists_etaleChart_containedComponentsIdeal T hV j hj x hx
    refine ⟨U, hxU, ?_⟩
    have hDj := hsome j hj b hab
    have hq1 : QuasiCompact
        (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) :=
      quasiCompact_saturationι_of_isLocallyNoetherian _ _
    have hq2 := quasiCompact_saturationι_restrictIdeal
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U
    rw [hZU, hDj] at hq2
    have := hq2
    rw [restrictIdeal_mul, restrictIdeal_strictTransform_id, hZU, hDj,
      c.saturation_coordIdeal_self b, Scheme.IdealSheafData.top_mul]
  · refine ⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl,
      (mem_closeds_compl _ _).mpr hx, ?_⟩
    have hZtop : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj)
        (DivisorReduction.containedComponentsIdeal T j hj).support.compl = ⊤ := by
      have h := restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support (𝟙 T.scheme)
        (DivisorReduction.containedComponentsIdeal T j hj) (DivisorReduction.containedComponentsIdeal T j hj).support.compl
        (fun y hy => by
          have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
            (mem_closeds_compl _ y).mp hy
          simpa using h')
      rwa [exceptionalIdeal_id] at h
    have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)
      (DivisorReduction.containedComponentsIdeal T j hj).support.compl
      (fun y hy => by
        have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
          (mem_closeds_compl _ y).mp hy
        simpa using h')
    rw [restrictIdeal_mul, hst, Scheme.IdealSheafData.comap_id, hZtop,
      Scheme.IdealSheafData.mul_top]

theorem disjoint_support_strictTransform_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Disjoint
      ((Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
          ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme))).support : Set ↥T.scheme)
      (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id, Set.disjoint_right]
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  have hDj := hsome j hj b hab
  have hq1 : QuasiCompact
      (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) :=
    quasiCompact_saturationι_of_isLocallyNoetherian _ _
  have hq2 := quasiCompact_saturationι_restrictIdeal
    (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U
  rw [hZU, hDj] at hq2
  have := hq2
  have hres : restrictIdeal (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
      (T.boundary.get ⟨j, hj⟩)) U = ⊤ := by
    rw [restrictIdeal_strictTransform_id, hZU, hDj]
    exact c.saturation_coordIdeal_self b
  exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U hres x hxU

theorem take_eraseIdx_lowerBoundaryAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    ((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1) =
      T.boundary.eraseIdx j := by
  have hlist : (T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
        (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) =
      T.boundary.map (fun D =>
        Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme))) := by
    simp only [List.map_map, Function.comp_def]
  have key := eraseIdx_map_eq
    (fun D : T.scheme.IdealSheafData =>
      Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme)))
    T.boundary j
    (fun i h hij => strictTransform_comap_boundary_of_ne T hV j hj i h hij)
  have hlen : j < (T.boundary.map (fun D =>
      Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
        (D.comap (𝟙 T.scheme)))).length := by
    simpa using hj
  show ((((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
        (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))) ++
      [Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)]).eraseIdx j).take
      (T.boundary.length - 1) = T.boundary.eraseIdx j
  rw [hlist, List.eraseIdx_append_of_lt_length hlen, key]
  exact List.take_left' (List.length_eraseIdx_of_lt hj)

theorem inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) :
    InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      ((((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1)).map
        fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  rw [take_eraseIdx_lowerBoundaryAfterBlowup T hV j hj]
  exact inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq T.structMap T.boundary hV.snc j hj
    (T.boundary.get ⟨j, hj⟩) rfl

end DivisorReductionBoundary

end FunctorialResolution.EmbeddedResolution

end
end

