module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.InvarianceUnderIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure PrincipalizationGeometryHypotheses : Prop where
  maxContactTransport : OrderCertificateIsoInvariantOfMaxContact.{u}
  exceptional_components_not_subset : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
      (∀ x : ↥T.scheme, x ∈ Z.support → orderAt J x = (c : ℕ∞)) →
    ∀ J' : X'.IdealSheafData,
      Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
    ∀ C' : Set ↥X', IsIrreducibleComponentOf C' (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X') →
      ¬ C' ⊆ (↑J'.support : Set ↥X')
  orderAt_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L)
      (I : T.scheme.IdealSheafData) (y : ↥(T.baseChange L f).scheme),
      orderAt (I.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f))) y =
        orderAt I ((pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base y)
  controlledTransform_orderAt_le : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
      (∀ x : ↥T.scheme, x ∈ Z.support → orderAt J x = (c : ℕ∞)) →
    ∀ J' : X'.IdealSheafData,
      Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
    ∀ x' : ↥X', x' ∈ (Blowup.exceptionalIdeal π Z).support → orderAt J' x' ≤ (c : ℕ∞)
  splitting_baseChange : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
      (T.baseChange L f).IsAdmissible →
    ∀ M N : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting (T.baseChange L f).boundary (T.baseChange L f).ideal
        (M.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
        (N.comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
  splitting_smooth_pullback : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
      (T.pullbackAlong Y q h).IsAdmissible →
    ∀ M N : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting (T.pullbackAlong Y q h).boundary (T.pullbackAlong Y q h).ideal
        (M.comap h) (N.comap h)
  splitting_exists : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∃ M N : T.scheme.IdealSheafData, IsMonomialSplitting T.boundary T.ideal M N
  splitting_unique : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ M N M' N' : T.scheme.IdealSheafData,
      IsMonomialSplitting T.boundary T.ideal M N →
      IsMonomialSplitting T.boundary T.ideal M' N' →
      M = M' ∧ N = N'
  strictTransform_components : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ Z : T.scheme.IdealSheafData,
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
      HasStrictNormalCrossingsWith T.structMap Z T.boundary →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
    ∀ D ∈ T.boundary,
    ∀ C' : Set ↥X', IsIrreducibleComponentOf C' (↑(Blowup.strictTransform π Z D).support : Set ↥X') →
      ∃ (η' : ↥X') (C : Set ↥T.scheme),
        C' = closure {η'} ∧
        η' ∉ (Blowup.exceptionalIdeal π Z).support ∧
        IsIrreducibleComponentOf C (↑D.support : Set ↥T.scheme) ∧
        ¬ C ⊆ (↑Z.support : Set ↥T.scheme) ∧
        C = closure {π.base η'}
  monomialInputs : MonomialGeometryHypotheses.{u}

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

def OrderAtComapOffExceptionalLocus : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ x' : ↥X', x' ∉ (Blowup.exceptionalIdeal π Z).support →
        ∀ A : T.scheme.IdealSheafData, orderAt (A.comap π) x' = orderAt A (π x')

theorem orderAtComapOffExceptionalLocus_of_monomialGeometryHypotheses (h : MonomialGeometryHypotheses.{u}) :
    OrderAtComapOffExceptionalLocus.{u} :=
  h.orderAt_comap_off_exceptional

theorem orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (hgeom : OrderAtComapOffExceptionalLocus.{u})
    (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (J : T.scheme.IdealSheafData) (μ : ℕ)
    (hZ : (↑Z.support : Set ↥T.scheme) ⊆ orderAtLeastLocus J μ)
    (J' : X'.IdealSheafData)
    (hJ' : Blowup.exceptionalIdeal π Z ^ μ * J' = J.comap π)
    (c : ℕ) (hc : c ≤ μ) :
    orderAtLeastLocus J' c ⊆ ⇑π ⁻¹' orderAtLeastLocus J c := by
  intro x' hx'
  rw [Set.mem_preimage, mem_orderAtLeastLocus_iff]
  by_cases hE : x' ∈ (Blowup.exceptionalIdeal π Z).support
  · have hmem : x' ∈ (↑(Z.comap π).support : Set ↥X') := by
      rw [← Blowup.exceptionalIdeal_eq_comap π Z]
      exact hE
    have hπx : π x' ∈ (↑Z.support : Set ↥T.scheme) := by
      simpa [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap] using hmem
    have h2 : (μ : ℕ∞) ≤ orderAt J (π x') := (mem_orderAtLeastLocus_iff J μ (π x')).1 (hZ hπx)
    exact le_trans (by exact_mod_cast hc) h2
  · have h1 : orderAt (J.comap π) x' = orderAt J (π x') := hgeom T hT X' π Z hπ x' hE J
    have h2 := add_orderAt_le_orderAt_mul (Blowup.exceptionalIdeal π Z ^ μ) J' x'
    rw [hJ', h1] at h2
    have h3 : (c : ℕ∞) ≤ orderAt J' x' := (mem_orderAtLeastLocus_iff J' c x').1 hx'
    exact le_trans h3 (le_trans le_add_self h2)

private theorem transitionMap_refl_apply {X : Scheme.{u}} (s : SequenceOfBlowups X) {i : ℕ} (h : i ≤ i)
    (x : ↥(s.schemeAt i)) : s.transitionMap h x = x :=
  congrFun (congrArg (fun f : s.schemeAt i ⟶ s.schemeAt i => (f : ↥(s.schemeAt i) → ↥(s.schemeAt i)))
    (s.transitionMap_self h)) x

private theorem transitionMap_comp_apply {X : Scheme.{u}} (s : SequenceOfBlowups X) {i j l : ℕ} (hij : i ≤ j)
    (hjl : j ≤ l) (x : ↥(s.schemeAt l)) :
    s.transitionMap hij (s.transitionMap hjl x) = s.transitionMap (hij.trans hjl) x := by
  have h := s.transitionMap_trans hij hjl
  calc s.transitionMap hij (s.transitionMap hjl x) = (s.transitionMap hjl ≫ s.transitionMap hij) x := rfl
    _ = s.transitionMap (hij.trans hjl) x := by rw [h]

namespace MarkedSequenceOfBlowups

theorem orderAtLeastLocus_succ_subset_preimage_blowupMorphism (hgeom : OrderAtComapOffExceptionalLocus.{u})
    (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    (hval : ∀ i ≤ s.toSequenceOfBlowups.length, (T.transformAt s i).IsAdmissible)
    (i : ℕ) (hi : i < s.toSequenceOfBlowups.length) (c : ℕ) (hc : c ≤ T.mult) :
    orderAtLeastLocus (s.ideal (i + 1)) c ⊆
      ⇑(s.toSequenceOfBlowups.transitionMapSucc i) ⁻¹' orderAtLeastLocus (s.ideal i) c := by
  have hvi := hval i (le_of_lt hi)
  exact orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf hgeom (T.transformAt s i) hvi
    (s.toSequenceOfBlowups.center i) (s.toSequenceOfBlowups.schemeAt (i + 1)) (s.toSequenceOfBlowups.transitionMapSucc i)
    (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) (s.ideal i) T.mult (s.center_order i hi)
    (s.ideal (i + 1)) (s.ideal_succ i hi) c hc

theorem orderAtLeastLocus_subset_preimage_transitionMap (hgeom : OrderAtComapOffExceptionalLocus.{u})
    (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups)
    (hval : ∀ i ≤ s.toSequenceOfBlowups.length, (T.transformAt s i).IsAdmissible)
    (c : ℕ) (hc : c ≤ T.mult) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ s.toSequenceOfBlowups.length) :
    orderAtLeastLocus (s.ideal j) c ⊆ ⇑(s.toSequenceOfBlowups.transitionMap hij) ⁻¹' orderAtLeastLocus (s.ideal i) c := by
  revert hj
  induction j, hij using Nat.le_induction with
  | base =>
      intro _ x hx
      rw [Set.mem_preimage, transitionMap_refl_apply]
      exact hx
  | succ j hij ih =>
      intro hj1
      have hjlt : j < s.toSequenceOfBlowups.length := Nat.lt_of_succ_le hj1
      have hstep := orderAtLeastLocus_succ_subset_preimage_blowupMorphism hgeom T s hval j hjlt c hc
      have hih := ih (le_of_lt hjlt)
      intro x hx
      rw [Set.mem_preimage]
      have h1 : s.toSequenceOfBlowups.transitionMapSucc j x ∈ orderAtLeastLocus (s.ideal j) c := hstep hx
      have h2 : s.toSequenceOfBlowups.transitionMap hij (s.toSequenceOfBlowups.transitionMapSucc j x) ∈
          orderAtLeastLocus (s.ideal i) c := hih h1
      rw [s.toSequenceOfBlowups.blowupMorphism_eq_transitionMap j, transitionMap_comp_apply] at h2
      exact h2

end MarkedSequenceOfBlowups

end FunctorialResolution.EmbeddedResolution
end

