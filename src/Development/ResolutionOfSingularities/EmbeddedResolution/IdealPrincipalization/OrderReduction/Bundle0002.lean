module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Bundle0001
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0005
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0009
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupLiftCongruence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.WeakTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.RadicalCenterIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

structure MaxContactCoverProperties : Prop where
  strictTransform_admissible :
    ∀ (k : Type u) [Field k] [CharZero k] {P P₁ : Scheme.{u}}
      (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.IsLocallyNoetherian P₁]
      (π : P₁ ⟶ P) [AlgebraicGeometry.LocallyOfFiniteType (π ≫ p)]
      (Z : P.IdealSheafData) (E : List P.IdealSheafData),
      HasStrictNormalCrossingsWith p Z E → Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ), 1 ≤ μ →
        (∀ x : ↥P, orderAt A x ≤ (μ : ℕ∞)) →
        (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ →
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        ∀ H : P.IdealSheafData, IsMaxContactHypersurface k p A μ H →
          IsMaxContactHypersurface k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H)
  coSupport_le_preimage :
    ∀ {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ (A : X.IdealSheafData) (A₁ : X₁.IdealSheafData) (μ : ℕ),
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        (Z.support : Set ↥X) ⊆ orderAtLeastLocus A μ →
        orderAtLeastLocus A₁ μ ⊆ (⇑π.base) ⁻¹' orderAtLeastLocus A μ
  schemeDim_level_le :
    ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc
  exists_goodCover :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
        MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType
          (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)
  hasSNCWith_cons :
    ∀ (k : Type u) [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] (Z H : P.IdealSheafData) (N : List P.IdealSheafData),
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) →
      InStrictNormalCrossingPosition p (H :: N) → HasStrictNormalCrossingsWith p Z N → H ≤ Z →
      HasStrictNormalCrossingsWith p Z (H :: N)
  valid_level :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      (T.transformAt s i).IsAdmissible
  orderAt_level_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
        ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞)
  coverTriple_dim_le :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      krullDimSucc (MaxContactCoverData.coverTriple T hv).scheme ≤ T.krullDimSucc
  coverTriple_valid :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      (MaxContactCoverData.coverTriple T hv).IsAdmissible
  coverContact_admissible :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      ∀ [AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
          (MaxContactCoverData.coverTriple T hv).structMap
          (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T)
          (MaxContactCoverData.coverMaxContactIdeal T hv)
  coverContact_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
        [MaxContactCoverData.coverMaxContactIdeal T hv]
  tuning : TunedSheafProperties.{u}

theorem MaxContactCoverProperties.krullDimSucc_schemeAt_le_dim (hf : MaxContactCoverProperties.{u}) {S : MarkedIdealWithBoundary.{u}} (hv : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (i : ℕ) (hi : i ≤ s.length) :
    krullDimSucc (s.obj i) ≤ S.krullDimSucc :=
  hf.schemeDim_level_le S hv s.toMarkedSequenceOfBlowups i (by simpa using hi)

theorem MaxContactCoverProperties.derivedTriple_dim_le (hf : MaxContactCoverProperties.{u}) {T S : MarkedIdealWithBoundary.{u}} (hv : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (hdim : S.krullDimSucc ≤ T.krullDimSucc) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc :=
  le_trans (hf.krullDimSucc_schemeAt_le_dim hv s s.length le_rfl) hdim

private theorem isMaxContactHypersurface_of_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p q : X ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.LocallyOfFiniteType q] (h : p = q) {A : X.IdealSheafData} {m : ℕ}
    {H : X.IdealSheafData} (hH : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface k q A m H := by
  subst h
  exact hH

theorem MaxContactCoverProperties.isMaxContactHypersurface_strictTransform_succ (hf : MaxContactCoverProperties.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hv : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec i)]
    [AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec (i + 1))]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hH : IsMaxContactHypersurface T.base (s.projectionToSpec i) (s.ideal i) T.mult H) :
    IsMaxContactHypersurface T.base (s.projectionToSpec (i + 1)) (s.ideal (i + 1)) T.mult
      (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) H) := by
  have hi' : i ≤ s.toSequenceOfBlowups.length := le_of_lt hi
  have hvi := hf.valid_level T hv s i hi'
  have hvi1 := hf.valid_level T hv s (i + 1) hi
  have : CharZero T.base := hv.charZero
  have : AlgebraicGeometry.Smooth (s.projectionToSpec i) := hvi.smooth
  have hno : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (i + 1)) := hvi1.isNoetherian
  have : AlgebraicGeometry.IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (i + 1)) := inferInstance
  have : AlgebraicGeometry.LocallyOfFiniteType
      (s.toSequenceOfBlowups.transitionMapSucc i ≫ s.projectionToSpec i) := by
    rw [← MarkedSequenceOfBlowups.projectionToSpec_succ]
    infer_instance
  have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (s.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc i hi
  have key := hf.strictTransform_admissible T.base (s.projectionToSpec i)
    (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) (s.boundary i) hsnc
    (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) (s.ideal i) (s.ideal (i + 1)) T.mult
    hv.one_le_mult (hf.orderAt_level_le T hv hord s i hi') (s.center_order i hi)
    (s.ideal_succ i hi) H hH
  exact isMaxContactHypersurface_of_eq (MarkedSequenceOfBlowups.projectionToSpec_succ s i).symm key

theorem MaxContactCoverProperties.hasStrictNormalCrossingsWith_cons_of_le_center (hf : MaxContactCoverProperties.{u}) {T : MarkedIdealWithBoundary.{u}}
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [AlgebraicGeometry.Smooth (s.projectionToSpec i)]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (N : List (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hsnc : InStrictNormalCrossingPosition (s.projectionToSpec i) (H :: N))
    (hZN : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) N)
    (hHZ : H ≤ s.toSequenceOfBlowups.center i) :
    HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (H :: N) := by
  have hsm : AlgebraicGeometry.Smooth
      ((s.toSequenceOfBlowups.center i).subschemeι ≫ s.projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_smooth i hi
  exact hf.hasSNCWith_cons T.base (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) H N hsm hsnc hZN hHZ

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometry
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OrderReductionCorrectness

theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform.{u} := EmbeddedResolution.blowupLiftEqOnControlledTransform

theorem le_of_support_subset_of_smooth : ∀ (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData),
    AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) →
    ∀ J : X.IdealSheafData,
      (((Z.support : Set ↥X)) ⊆ ((J.support : Set ↥X))) → J ≤ Z :=
  smoothSubschemeIdealIsRadical

theorem isLocallyNoetherian_schemeAt : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → AlgebraicGeometry.IsLocallyNoetherian (s.schemeAt i) := by
  intro T hT s i hi
  have : AlgebraicGeometry.IsNoetherian (s.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s i hi
  infer_instance

theorem isBalanced_comap_of_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
    ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
      [AlgebraicGeometry.LocallyOfFiniteType q],
    IsDerivBalanced T.base T.structMap T.ideal T.mult →
    IsDerivBalanced T.base q (T.ideal.comap h) T.mult := by
  intro T hT Y q f _ hq _ _ hbal
  subst hq
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  refine isDerivBalanced_of_pow_le T.base (f ≫ T.structMap) ?_
  intro i hi
  rw [derivIdealSheafIterate_comap T.base T.structMap f i T.ideal,
    ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_pow]
  exact Scheme.IdealSheafData.comap_mono f (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hi)

theorem maxContactIdealComapLeControlled : MaxContactIdealComapLeControlled.{u} := by
  intro k _ _ X X₁ p _ _ π Z E hZ hπ _ _ _ A μ hμ hA A₁ hA₁
  have hct : A₁ = controlledTransform π Z A μ hπ hA :=
    eq_controlledTransform_of_mul_eq_comap π Z A μ hπ hA A₁ hA₁
  have key := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A μ hA
    (μ - 1) (Nat.sub_le μ 1)
  have hsub : μ - (μ - 1) = 1 := by omega
  rw [hsub, pow_one] at key
  simp only [maxContactIdeal_eq_derivIdealSheafIterate]
  rw [hct]
  exact key

theorem existsMaxContactControlledTransforms : ExistsMaxContactControlledTransforms.{u} :=
  existsMaxContactControlledTransforms_of_comapLeControlled maxContactIdealComapLeControlled

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_ideal :
    ∀ (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ orderAtLeastLocus (s.ideal i) T.mult →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T s i
  induction i with
  | zero =>
      intro _ x hx
      rw [s.ideal_zero, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hx
      rw [SequenceOfBlowups.projectionToBase_zero]
      exact hx
  | succ n ih =>
      intro hn x hx
      have hn' : n < s.length := hn
      have h1 : (s.transitionMapSucc n).base x ∈ orderAtLeastLocus (s.ideal n) T.mult :=
        OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n)
          (s.isBlowupAlongIdealSheaf_blowupMorphism n hn') (s.ideal n) (s.ideal (n + 1)) T.mult
          (s.ideal_succ n hn') (s.center_order n hn') hx
      have h2 := ih (le_of_lt hn') _ h1
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      exact h2

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_center : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : Set ↥(s.schemeAt i))) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T hT s i hi x hx
  exact projectionToBase_mem_orderAtLeastLocus_of_mem_ideal T s i (le_of_lt hi) x (s.center_order i hi hx)

theorem isStrictPullback_of_isPullback_of_center_nonempty : ∀ (X' X : Scheme.{u}) (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X), IsPullbackBlowupSequence φ s' s →
    (∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty) →
    (∀ i : ℕ, i < s.length → ∀ x ∈ (((s.center i).support : Set ↥(s.schemeAt i))),
      (s.projectionToBase i).base x ∈ Set.range φ.base) →
    IsStrictPullbackBlowupSeq φ s' s := by
  intro X' X φ s' s hpb hne hran
  exact hpb.isStrictPullback_of_support_comap_center_nonempty (support_comap_center_nonempty_of_mem_range φ s hne hran)

end OrderReductionCorrectness

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderBoundAlongSequence
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAt_ideal_le_mult_along_sequence (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (s : T.SequenceOfBlowups) :
    ∀ (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞) := by
  have : CharZero T.base := hT.charZero
  intro i
  induction i with
  | zero =>
      intro _ x
      have : AlgebraicGeometry.IsOpenImmersion s.toSequenceOfBlowups.isoZero.hom := inferInstance
      rw [s.ideal_zero, orderAt_comap_of_isOpenImmersion]
      exact hord _
  | succ k ih =>
      intro hk x
      have hlt : k < s.toSequenceOfBlowups.length := hk
      have hprev := ih (le_of_lt hlt)
      have hnoeth : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (k + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s (k + 1) hk
      have : AlgebraicGeometry.IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (k + 1)) := inferInstance
      have hsmooth : AlgebraicGeometry.Smooth (s.projectionToSpec k) :=
        MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hT s k (le_of_lt hlt)
      have hS : HasStrictNormalCrossingsWith (s.projectionToSpec k) (s.toSequenceOfBlowups.center k) (s.boundary k) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc k hlt
      have hI : s.ideal k ≤ s.toSequenceOfBlowups.center k ^ T.mult :=
        le_pow_of_hasStrictNormalCrossingsWith (s.projectionToSpec k) (s.toSequenceOfBlowups.center k) (s.ideal k)
          (s.boundary k) hS T.mult (s.center_order k hlt)
      have hEq : s.ideal (k + 1) =
          controlledTransform (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k)
            (s.ideal k) T.mult (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) hI :=
        eq_controlledTransform_of_mul_eq_comap (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k)
          (s.ideal k) T.mult (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) hI
          (s.ideal (k + 1)) (s.ideal_succ k hlt)
      rw [hEq]
      exact orderAt_controlledTransform_le_of_forall_le T.base (s.projectionToSpec k)
        (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k) (s.boundary k) hS
        (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) (s.ideal k) T.mult hI hprev x

end FunctorialResolution.EmbeddedResolution
end

