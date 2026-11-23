module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SubschemeMapFlatness
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0006
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.UntwistedDivisorRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.Bundle0008
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsFunctoriality
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isIrreducible_connectedComponent_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (z : ↥(T.boundary.get ⟨j, hj⟩).subscheme) :
    IsIrreducible (connectedComponent z) := by
  have : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hsd : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    isSmoothDivisor_boundary_get T hV j hj
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp hsd).2
  have hsep := irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
    ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have h1 : connectedComponent z ⊆ irreducibleComponent z :=
    connectedComponent_subset_of_mem_irreducibleComponents hsep
      (irreducibleComponent_mem_irreducibleComponents z) mem_irreducibleComponent
  have h2 : irreducibleComponent z ⊆ connectedComponent z :=
    (isIrreducible_irreducibleComponent (x := z)).2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent

theorem openSubschemeKer_comap_of_flat_of_noetherian {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (D : X.IdealSheafData) (A : Set X) (hA : IsClosed A)
    (hirr : ∀ w : ↥D.subscheme, IsIrreducible (connectedComponent w))
    (hN : TopologicalSpace.NoetherianSpace ↥D.subscheme)
    (hN' : TopologicalSpace.NoetherianSpace ↥(D.comap g).subscheme)
    (hopen : IsOpen {w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A})
    (hopen' : IsOpen {w : ↥(D.comap g).subscheme |
      connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}) :
    openSubschemeKer (D.comap g)
        ⟨{w : ↥(D.comap g).subscheme |
            connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}, hopen'⟩ =
      (openSubschemeKer D
        ⟨{w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A}, hopen⟩).comap g := by
  have := hN
  have := hN'
  exact openSubschemeKer_comap g D A hA ⟨_, hopen⟩ ⟨_, hopen'⟩ rfl rfl
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset ↥D.subscheme
      (⇑D.subschemeι.base ⁻¹' A))
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
      ↥(D.comap g).subscheme
      (⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A))) hirr

private theorem get_eq_comap_get_of_eq_map {X Y : Scheme.{u}} (g : Y ⟶ X) (E : List X.IdealSheafData)
    (F : List Y.IdealSheafData) (hF : F = E.map (fun D => D.comap g)) (j : ℕ)
    (hj : j < E.length) (hj' : j < F.length) :
    F.get ⟨j, hj'⟩ = (E.get ⟨j, hj⟩).comap g := by
  subst hF
  simp [List.get_eq_getElem]

private theorem containedComponentsIdeal_comap_of_flat (T T' : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hV' : T'.IsAdmissible) (g : T'.scheme ⟶ T.scheme) (hflat : AlgebraicGeometry.Flat g) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < T'.boundary.length)
    (hD : T'.boundary.get ⟨j, hj'⟩ = (T.boundary.get ⟨j, hj⟩).comap g)
    (hcs : orderAtLeastLocus T'.ideal T'.mult = ⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)
    (hcl : IsClosed (orderAtLeastLocus T.ideal T.mult)) :
    DivisorReduction.containedComponentsIdeal T' j hj' = (DivisorReduction.containedComponentsIdeal T j hj).comap g := by
  have := hflat
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  have hopen' := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T' hV' j hj'
  have hirr : ∀ w : ↥(T.boundary.get ⟨j, hj⟩).subscheme, IsIrreducible (connectedComponent w) :=
    fun w => isIrreducible_connectedComponent_boundary_subscheme T hV j hj w
  have hN : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hN' : TopologicalSpace.NoetherianSpace ↥(T'.boundary.get ⟨j, hj'⟩).subscheme :=
    noetherianSpace_boundary_subscheme T' hV' j hj'
  have key : ∀ (D' : T'.scheme.IdealSheafData), D' = (T.boundary.get ⟨j, hj⟩).comap g →
      ∀ (S' : Set ↥D'.subscheme),
        S' = {w : ↥D'.subscheme | connectedComponent w ⊆
            ⇑D'.subschemeι.base ⁻¹' (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} →
        ∀ (hop' : IsOpen S'), TopologicalSpace.NoetherianSpace ↥D'.subscheme →
          openSubschemeKer D' ⟨S', hop'⟩ =
            (openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, hopen⟩).comap g := by
    rintro D' rfl S' rfl hop' hNN
    exact openSubschemeKer_comap_of_flat_of_noetherian g (T.boundary.get ⟨j, hj⟩)
      (orderAtLeastLocus T.ideal T.mult) hcl hirr hN hNN hopen hop'
  have hset : divisorComponentsInOrderLocus T' j hj' =
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹'
          (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} :=
    congrArg (fun A : Set ↥T'.scheme =>
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹' A}) hcs
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen, containedComponentsIdeal_eq_openSubschemeKer T' j hj' hopen']
  exact key _ hD _ hset hopen' hN'

theorem containedComponentsIdeal_pullbackAlong_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    (hq : h ≫ T.structMap = q) (hV' : (T.pullbackAlong Y q h).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.pullbackAlong Y q h).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap h := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hfl : AlgebraicGeometry.Flat h := inferInstance
  have hD : (T.pullbackAlong Y q h).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_of_eq_map h T.boundary (T.pullbackAlong Y q h).boundary
      (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h) j hj hj'
  have hcs : orderAtLeastLocus (T.pullbackAlong Y q h).ideal (T.pullbackAlong Y q h).mult =
      ⇑h.base ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat T (T.pullbackAlong Y q h) hV hV' h hfl j hj hj' hD hcs hcl

theorem containedComponentsIdeal_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) (hV' : (T.baseChange L f).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.baseChange L f).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap
        (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hfl : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    flat_fieldBaseChangeProjection T L f
  have hD : (T.baseChange L f).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    get_eq_comap_get_of_eq_map (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) T.boundary
      (T.baseChange L f).boundary (MarkedIdealWithBoundary.baseChange_boundary T L f) j hj hj'
  have hcs : orderAtLeastLocus (T.baseChange L f).ideal (T.baseChange L f).mult =
      ⇑(pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base ⁻¹'
        orderAtLeastLocus T.ideal T.mult :=
    orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat T (T.baseChange L f) hV hV'
    (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hfl j hj hj' hD hcs hcl

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem filter_map_eq_of_filter_eq {α : Type*} (p : α → Bool) (g : α → α)
    (hpg : ∀ a, p a = false → p (g a) = false) {A B : List α}
    (hAB : List.filter p A = List.filter p B) :
    List.filter p (A.map g) = List.filter p (B.map g) := by
  have key : ∀ L : List α,
      List.filter p (L.map g) = List.filter p ((List.filter p L).map g) := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        have hga : p (g a) = false := hpg a ha'
        simp [ha', hga, ih]
  rw [key A, key B, hAB]

private theorem sameNontrivialBoundary_map {X : Scheme.{u}} (g : X.IdealSheafData → X.IdealSheafData)
    (hg : g ⊤ = ⊤) {A B : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (A.map g) (B.map g) := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  unfold MarkedIdealWithBoundary.nontrivialPart at h ⊢
  refine filter_map_eq_of_filter_eq _ g ?_ h
  intro a ha
  have ha' : a = ⊤ := by simpa using ha
  subst ha'
  simp [hg]

private theorem sameNontrivialBoundary_take_eraseIdx_strictTransform {X : Scheme.{u}} (Z : X.IdealSheafData)
    (A B : List X.IdealSheafData) (a b : ℕ) (ha : a < A.length) (hb : b < B.length)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary (A.eraseIdx a) (B.eraseIdx b)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (A.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) A)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx a))
      (List.take (B.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx b)) := by
  have hcomap : ∀ I : X.IdealSheafData, I.comap (𝟙 X) = I := by
    intro I
    simp
  have hgtop : (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) ⊤
      = (⊤ : X.IdealSheafData) := by
    show Blowup.strictTransform (𝟙 X) Z ((⊤ : X.IdealSheafData).comap (𝟙 X)) = ⊤
    rw [hcomap]
    have h1 := comap_le_strictTransform (𝟙 X) Z (⊤ : X.IdealSheafData)
    rw [hcomap] at h1
    exact le_antisymm le_top h1
  have key : ∀ (C : List X.IdealSheafData) (c : ℕ), c < C.length →
      List.take (C.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) C)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx c)
        = List.map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
            (C.eraseIdx c) := by
    intro C c hc
    have hlen : (List.map (fun D : X.IdealSheafData =>
        Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) (C.eraseIdx c)).length = C.length - 1 := by
      rw [List.length_map]
      exact List.length_eraseIdx_of_lt hc
    have hmap : ∀ f : X.IdealSheafData → X.IdealSheafData, c < (C.map f).length := by
      intro f
      rw [List.length_map]
      exact hc
    simp only [List.map_map, Function.comp_def]
    rw [List.eraseIdx_append_of_lt_length (hmap _)]
    rw [List.eraseIdx_map, ← hlen, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  rw [key A a ha, key B b hb]
  exact sameNontrivialBoundary_map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
    hgtop h

theorem lowerIdealAfterBlowup_withBoundary_eq_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩) :
    lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂ = lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁ := by
  unfold lowerIdealAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  rfl

theorem sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂).eraseIdx j₂))
      (List.take (L₁.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁).eraseIdx j₁)) := by
  unfold lowerBoundaryAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  exact sameNontrivialBoundary_take_eraseIdx_strictTransform
    (containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂) L₂ L₁ j₂ j₁ hj₂ hj₁ hBE

theorem boundaryReindexingInvariance : BoundaryReindexingInvariance.{u} :=
  ⟨smooth_id, surjective_id, lowerIdealAfterBlowup_withBoundary_eq_of_get_eq, sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

