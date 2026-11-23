module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.CoordinateIdealOrderOne
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StalkKrullDimension
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.Bundle0001

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
section
universe u v

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialChart

theorem comap_biSup_finset {X Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y)
    (I : ι → Y.IdealSheafData) (S : Finset ι) :
    (⨆ j ∈ S, I j).comap f = ⨆ j ∈ S, (I j).comap f := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.iSup_insert, Finset.iSup_insert, Scheme.IdealSheafData.comap_sup, ih]

theorem restrictIdeal_biSup_finset {X : Scheme.{u}} {ι : Type v} (U : X.Opens)
    (I : ι → X.IdealSheafData) (S : Finset ι) :
    restrictIdeal (⨆ j ∈ S, I j) U = ⨆ j ∈ S, restrictIdeal (I j) U :=
  comap_biSup_finset U.ι I S

private theorem ofIdealTop_sup {X : Scheme.{u}} [IsAffine X] (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I ⊔ J) =
      Scheme.IdealSheafData.ofIdealTop I ⊔ Scheme.IdealSheafData.ofIdealTop J := by
  ext U : 2
  simp [Scheme.IdealSheafData.ofIdealTop, Ideal.map_sup]

theorem coordSubspaceIdeal_insert (k : Type u) [Field k] (m : ℕ) (j : Fin m)
    (S : Finset (Fin m)) :
    coordSubspaceIdeal k m (insert j S) =
      coordSubspaceIdeal k m {j} ⊔ coordSubspaceIdeal k m S := by
  classical
  rw [coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord, coordSubspaceIdeal_eq_ofIdealTop_span_coord,
    Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert, Finset.coe_singleton,
    Set.image_singleton, ofIdealTop_sup]

theorem coordSubspaceIdeal_eq_biSup_singleton (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    coordSubspaceIdeal k m S = ⨆ j ∈ S, coordSubspaceIdeal k m {j} := by
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [coordSubspaceIdeal_empty]
  · intro a s _ ih
    rw [coordSubspaceIdeal_insert, ih, Finset.iSup_insert]

theorem coordIdeal_eq_biSup_singleton {X : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) (m : ℕ) (c : EtaleChart p U m)
    (S : Finset (Fin m)) :
    c.coordIdeal S = ⨆ j ∈ S, c.coordIdeal {j} := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_biSup_singleton, comap_biSup_finset]
  exact iSup_congr fun j => iSup_congr fun _ => (c.coordIdeal_eq_comap_coordSubspaceIdeal {j}).symm

theorem orderAt_boundary_eq_one : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ D ∈ T.boundary, ∀ x : ↥T.scheme, x ∈ D.support → orderAt D x = 1 := by
  intro T hT D hD x hx
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  obtain ⟨i, hi, hDi⟩ := List.mem_iff_getElem.1 hD
  cases hai : a i with
  | none =>
      refine absurd hx (notMem_support_of_mem_opens_of_restrictIdeal_eq_top D U ?_ x hxU)
      rw [← hDi]
      exact hnone i hi hai
  | some t =>
      obtain ⟨V, m', hxV, hVU', hV, -⟩ := exists_etaleChart_le T.structMap x U hxU
      have hDU : restrictIdeal D U = c.coordIdeal {t} := by
        rw [← hDi]
        exact hsome i hi t hai
      have hDV : restrictIdeal D V = (c.restrict hVU').coordIdeal {t} :=
        restrictIdeal_eq_restrict_coordIdeal_of_le hVU' c D {t} hDU
      exact orderAt_eq_one_of_restrictIdeal_eq_coordIdeal_singleton T.structMap hV
        (c.restrict hVU') t D hDV x hxV hx

theorem smooth_intersectionIdeal_subscheme : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ J : Finset (Fin T.boundary.length),
      AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap) := by
  classical
  intro T hT J
  refine smooth_subschemeι_comp_of_locally_eq_coordIdeal (p := T.structMap) (intersectionIdeal T.boundary J) ?_
  intro x hx
  obtain ⟨_, hpos⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hT.snc
  obtain ⟨U, hxU, m, c, a, _, hnone, hsome⟩ := (hpos x).exists_etaleChart
  have hle : ∀ j ∈ J, T.boundary.get j ≤ intersectionIdeal T.boundary J := by
    intro j hj
    rw [intersectionIdeal_eq_iSup]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => T.boundary.get j) j hj
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro hcon
    have h2 := stalkIdeal_mono (hle j hj) x
    rw [hcon] at h2
    exact (mem_support_iff_stalkIdeal_ne_top _ _).1 hx (top_le_iff.1 h2)
  have hsomej : ∀ j ∈ J, ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    cases haj : a (j : ℕ) with
    | none =>
        refine absurd (hxj j hj)
          (notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U ?_ x hxU)
        rw [List.get_eq_getElem]
        exact hnone (j : ℕ) j.isLt haj
    | some t => exact ⟨t, rfl⟩
  refine ⟨U, hxU, m, c, J.biUnion (fun j => (a (j : ℕ)).toFinset), ?_⟩
  have h1 : restrictIdeal (intersectionIdeal T.boundary J) U
      = ⨆ j ∈ J, restrictIdeal (T.boundary.get j) U := by
    rw [intersectionIdeal_eq_iSup]
    exact restrictIdeal_biSup_finset U (fun j => T.boundary.get j) J
  have h2 : c.coordIdeal (J.biUnion (fun j => (a (j : ℕ)).toFinset))
      = ⨆ t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset), c.coordIdeal {t} :=
    coordIdeal_eq_biSup_singleton T.structMap U m c _
  rw [h1, h2]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j => iSup_le fun hj => ?_
    obtain ⟨t, ht⟩ := hsomej j hj
    have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
      rw [List.get_eq_getElem]
      exact hsome (j : ℕ) j.isLt t ht
    have htS : t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset) :=
      Finset.mem_biUnion.2 ⟨j, hj, by simp [ht]⟩
    rw [hres]
    exact le_iSup₂
      (f := fun t (_ : t ∈ J.biUnion (fun j => (a (j : ℕ)).toFinset)) =>
        c.coordIdeal ({t} : Finset (Fin m))) t htS
  · refine iSup_le fun t => iSup_le fun htS => ?_
    obtain ⟨j, hj, htj⟩ := Finset.mem_biUnion.1 htS
    have ht : a (j : ℕ) = some t := Option.mem_def.1 (Option.mem_toFinset.1 htj)
    have hres : restrictIdeal (T.boundary.get j) U = c.coordIdeal {t} := by
      rw [List.get_eq_getElem]
      exact hsome (j : ℕ) j.isLt t ht
    rw [← hres]
    exact le_iSup₂ (f := fun j (_ : j ∈ J) => restrictIdeal (T.boundary.get j) U) j hj

end MonomialChart

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentCodimension
section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCodimension

theorem lt_krullDimSucc_of_le_ringKrullDim_stalk (X : Scheme.{u}) (x : ↥X) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hfin : topologicalKrullDim ↥X ≠ ⊤) : n < krullDimSucc X := by
  have hn' : ((n : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := hn
  have hle : ((n : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim ↥X :=
    le_trans hn' (ringKrullDim_stalk_le_topologicalKrullDim X x)
  rw [krullDimSucc_eq_withBotSuccToNat_topologicalKrullDim]
  by_cases hb : topologicalKrullDim ↥X = ⊥
  · rw [hb] at hle
    exact absurd (le_bot_iff.mp hle) WithBot.coe_ne_bot
  · obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hb
    rw [← he] at hle hfin ⊢
    have he' : e ≠ ⊤ := by
      intro hcon
      apply hfin
      rw [hcon]
      simp
    lift e to ℕ using he' with m
    rw [withBotSuccToNat_coe]
    have hmm : ((m : ℕ∞)).toNat = m := by simp
    rw [hmm]
    have hnm : n ≤ m := by exact_mod_cast hle
    omega

theorem card_lt_krullDimSucc_of_mem_intersectionComponents : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (J : Finset (Fin T.boundary.length)) (C : Set ↥T.scheme),
      C ∈ intersectionComponents T.boundary J → J.card < krullDimSucc T.scheme := by
  classical
  intro T hT J C hC
  have hC' : IsIrreducible C ∧ C ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) ∧
      ∀ C' : Set ↥T.scheme, IsIrreducible C' → C ⊆ C' →
        C' ⊆ (↑(intersectionIdeal T.boundary J).support : Set ↥T.scheme) → C' = C :=
    (mem_intersectionComponents_iff T.boundary J C).mp hC
  obtain ⟨hirr, hsub, -⟩ := hC'
  obtain ⟨x, hxC⟩ := hirr.nonempty
  have hxsupp : x ∈ (intersectionIdeal T.boundary J).support := hsub hxC
  have hxj : ∀ j ∈ J, x ∈ (T.boundary.get j).support := by
    intro j hj
    rw [mem_support_iff_stalkIdeal_ne_top]
    intro htop
    rw [mem_support_iff_stalkIdeal_ne_top] at hxsupp
    have hle : T.boundary.get j ≤ intersectionIdeal T.boundary J := by
      rw [intersectionIdeal_eq_iSup]
      exact le_iSup₂ (f := fun (i : Fin T.boundary.length) (_ : i ∈ J) => T.boundary.get i) j hj
    have h1 := stalkIdeal_mono hle x
    rw [htop] at h1
    exact hxsupp (top_le_iff.mp h1)
  obtain ⟨-, hsnc⟩ := (inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hT.snc
  obtain ⟨U, hxU, m, c, a, hinj, hnone, hsome⟩ := (hsnc x).exists_etaleChart
  obtain ⟨V, hVB, hxV, hVU⟩ :=
    Opens.isBasis_iff_nbhd.mp T.scheme.isBasis_affineOpens hxU
  have hV : IsAffineOpen V := hVB
  have hex : ∀ j : Fin T.boundary.length, j ∈ J → ∃ t : Fin m, a (j : ℕ) = some t := by
    intro j hj
    have hne : a (j : ℕ) ≠ none := by
      intro hj'
      have htop := hnone (j : ℕ) j.isLt hj'
      have hx' := hxj j hj
      rw [List.get_eq_getElem] at hx'
      exact Scheme.IdealSheafData.notMem_support_of_comap_ι_eq_top _ htop hxU hx'
    exact Option.ne_none_iff_exists'.mp hne
  choose F hFspec using hex
  have hGinj : Function.Injective
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2) := by
    intro p q h
    have h1 : a (q.1 : ℕ) = some (F p.1 p.2) := by
      rw [hFspec q.1 q.2]
      exact congrArg Option.some h.symm
    have h2 := hinj (p.1 : ℕ) p.1.isLt (q.1 : ℕ) q.1.isLt (F p.1 p.2) (hFspec p.1 p.2) h1
    exact Subtype.ext (Fin.val_injective h2)
  have hcard : (J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)).card = J.card := by
    rw [Finset.card_image_of_injective _ hGinj, Finset.card_attach]
  let d : EtaleChart T.structMap V m := {
    map := T.scheme.homOfLE hVU ≫ c.map
    comp_struct := by rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.homOfLE_ι]
    isEtale := by
      have := c.isEtale
      infer_instance }
  have hmem : ∀ t ∈ J.attach.image
      (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2),
      d.coord t ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    intro t ht
    obtain ⟨p, -, hpt⟩ := Finset.mem_image.mp ht
    have hat : a (p.1 : ℕ) = some t := by
      rw [hFspec p.1 p.2]
      exact congrArg Option.some hpt
    have hU' := hsome (p.1 : ℕ) p.1.isLt t hat
    have hV' : restrictIdeal T.boundary[p.1.val] V = d.coordIdeal {t} := by
      have h' : T.boundary[p.1.val].comap U.ι =
          (coordSubspaceIdeal _ m {t}).comap c.map := by
        rw [← restrictIdeal_eq_comap_ι, hU', EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
      rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
      change _ = (coordSubspaceIdeal _ m {t}).comap (T.scheme.homOfLE hVU ≫ c.map)
      rw [Scheme.IdealSheafData.comap_comp, ← h', ← Scheme.IdealSheafData.comap_comp,
        Scheme.homOfLE_ι]
    have hx' := hxj p.1 p.2
    rw [List.get_eq_getElem] at hx'
    exact coord_mem_primeIdealOf_of_restrictIdeal_eq_coordIdeal_singleton hV
      d t _ hV' x hxV hx'
  have hle2 := card_le_ringKrullDim_stalk hV d x hxV
    (J.attach.image (fun p : {j : Fin T.boundary.length // j ∈ J} => F p.1 p.2)) hmem
  have hfin : topologicalKrullDim ↥T.scheme ≠ ⊤ := ne_of_lt hT.topologicalKrullDim_lt_top
  have hlt := lt_krullDimSucc_of_le_ringKrullDim_stalk T.scheme x _ hle2 hfin
  rwa [hcard] at hlt

theorem card_lt_krullDimSucc_of_nonempty (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : Finset (Fin T.boundary.length)) (hJ : (intersectionComponents T.boundary J).Nonempty) :
    J.card < krullDimSucc T.scheme := by
  obtain ⟨C, hC⟩ := hJ
  exact card_lt_krullDimSucc_of_mem_intersectionComponents T hT J C hC

end MonomialCodimension

end FunctorialResolution.EmbeddedResolution
end

