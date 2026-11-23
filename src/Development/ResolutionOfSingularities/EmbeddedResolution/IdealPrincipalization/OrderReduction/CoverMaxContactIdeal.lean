module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0006
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0005
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.Bundle0002
public import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.FormallyEtaleCoordinates
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.JacobianCriterion
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.LocalParameters
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem local_chart_comp (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    ((MaxContactOpenCover.coverPieceIso T hv i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n =
      (MaxContactOpenCover.coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) := by
  have h1 : c.map ≫ affineSpaceFinToSpec T.base n =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap := c.comp_struct
  have h2 := MaxContactOpenCover.coverTripleOpen_ι_comp_coverMap T hv i
  calc ((MaxContactOpenCover.coverPieceIso T hv i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n
      = (MaxContactOpenCover.coverPieceIso T hv i).inv ≫ (c.map ≫ affineSpaceFinToSpec T.base n) := Category.assoc _ _ _
    _ = (MaxContactOpenCover.coverPieceIso T hv i).inv ≫ (((MaxContactCoverData.chosenCoverData T hv).opens i).ι ≫ T.structMap) := by
        rw [h1]
    _ = ((MaxContactOpenCover.coverPieceIso T hv i).inv ≫ ((MaxContactCoverData.chosenCoverData T hv).opens i).ι) ≫ T.structMap :=
        (Category.assoc _ _ _).symm
    _ = ((MaxContactOpenCover.coverTripleOpen T hv i).ι ≫ MaxContactCoverData.coverMap T hv) ≫ T.structMap := by rw [h2]
    _ = (MaxContactOpenCover.coverTripleOpen T hv i).ι ≫ (MaxContactCoverData.coverMap T hv ≫ T.structMap) :=
        Category.assoc _ _ _

private theorem local_chart_etale (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    AlgebraicGeometry.Etale ((MaxContactOpenCover.coverPieceIso T hv i).inv ≫ c.map) := by
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : IsIso (MaxContactOpenCover.coverPieceIso T hv i).inv := inferInstance
  have : IsOpenImmersion (MaxContactOpenCover.coverPieceIso T hv i).inv := inferInstance
  have : AlgebraicGeometry.Etale (MaxContactOpenCover.coverPieceIso T hv i).inv := inferInstance
  infer_instance

private def localCoverEtaleChart (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n) :
    EtaleChart (MaxContactCoverData.coverMap T hv ≫ T.structMap) (MaxContactOpenCover.coverTripleOpen T hv i) n where
  map := (MaxContactOpenCover.coverPieceIso T hv i).inv ≫ c.map
  comp_struct := by
    exact local_chart_comp T hv i c
  isEtale := local_chart_etale T hv i c

private theorem localCoverEtaleChart_coordIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) {n : ℕ}
    (c : EtaleChart T.structMap ((MaxContactCoverData.chosenCoverData T hv).opens i) n)
    (S : Finset (Fin n)) :
    (localCoverEtaleChart T hv i c).coordIdeal S = (c.coordIdeal S).comap (MaxContactOpenCover.coverPieceIso T hv i).inv := by
  have key : (coordSubspaceIdeal T.base n S).comap ((MaxContactOpenCover.coverPieceIso T hv i).inv ≫ c.map)
      = ((coordSubspaceIdeal T.base n S).comap c.map).comap (MaxContactOpenCover.coverPieceIso T hv i).inv := by
    rw [Scheme.IdealSheafData.comap_comp]
  have h1 : (localCoverEtaleChart T hv i c).coordIdeal S
      = (coordSubspaceIdeal T.base n S).comap ((MaxContactOpenCover.coverPieceIso T hv i).inv ≫ c.map) :=
    EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal (localCoverEtaleChart T hv i c) S
  have h2 : (c.coordIdeal S).comap (MaxContactOpenCover.coverPieceIso T hv i).inv
      = ((coordSubspaceIdeal T.base n S).comap c.map).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
    congrArg (fun J => J.comap (MaxContactOpenCover.coverPieceIso T hv i).inv) (EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal c S)
  exact h1.trans (key.trans h2.symm)

private theorem range_ι_base_subset {X : Scheme.{u}} (U : X.Opens) :
    Set.range U.ι.base ⊆ (U : Set ↥X) :=
  (Scheme.Opens.range_ι U).subset

private theorem comap_comap_eq_of_comp_eq {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : X ⟶ Z) (a' : W ⟶ Y)
    (b' : Y ⟶ Z) (hsq : a ≫ b = a' ≫ b') (I : Z.IdealSheafData) :
    (I.comap b).comap a = (I.comap b').comap a' := by
  have h1 : (I.comap b).comap a = I.comap (a ≫ b) := by
    simp [Scheme.IdealSheafData.comap_comp]
  have h2 : (I.comap b').comap a' = I.comap (a' ≫ b') := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [h1, h2, hsq]

private theorem restrictIdeal_coverTripleOpen_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    @restrictIdeal (MaxContactCoverData.coverTriple T hv).scheme
        (MaxContactCoverData.coverMaxContactIdeal T hv) (MaxContactOpenCover.coverTripleOpen T hv i) =
      ((MaxContactCoverData.chosenCoverData T hv).localIdeal i).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
  (MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)).trans
    (congrArg (fun J : (MaxContactOpenCover.coverPiece T hv i).IdealSheafData =>
      J.comap (MaxContactOpenCover.coverPieceIso T hv i).inv) (hres i))

theorem isMaxContactHypersurface_coverMaxContactIdeal_of_comap_eq (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    [AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap]
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i) :
    IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
      (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal
      (MaxContactCoverData.tunedMult T) (MaxContactCoverData.coverMaxContactIdeal T hv) := by
  have := hv.charZero
  have := hv.smooth
  have := hv.locallyOfFiniteType
  have hftc : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverMap T hv ≫ T.structMap) :=
    (inferInstance : AlgebraicGeometry.LocallyOfFiniteType
      (MaxContactCoverData.coverTriple T hv).structMap)
  intro x
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have hAff0 : AlgebraicGeometry.IsAffine (MaxContactOpenCover.coverPiece T hv i) := hgood.isAffine i
  have haffineOpen : IsAffineOpen (MaxContactOpenCover.coverTripleOpen T hv i) :=
    isAffineOpen_opensRange (MaxContactOpenCover.coverPieceι T hv i)
  refine ⟨MaxContactOpenCover.coverTripleOpen T hv i, haffineOpen, hxi, ?_⟩
  have hcompι : MaxContactOpenCover.coverPieceι T hv i ≫ MaxContactCoverData.coverMap T hv =
      ((MaxContactCoverData.chosenCoverData T hv).opens i).ι :=
    sigma_ι_sigmaOpensDesc T.scheme (MaxContactCoverData.chosenCoverData T hv).opens i
  have hsub : ∀ y : ↥(MaxContactCoverData.coverTriple T hv).scheme,
      y ∈ (↑(MaxContactOpenCover.coverTripleOpen T hv i) :
        Set ↥(MaxContactCoverData.coverTriple T hv).scheme) →
      (MaxContactCoverData.coverMap T hv).base y ∈
        (↑((MaxContactCoverData.chosenCoverData T hv).opens i) : Set ↥T.scheme) := by
    intro y hy
    have hy' : y ∈ Set.range (MaxContactOpenCover.coverPieceι T hv i).base := hy
    obtain ⟨z, rfl⟩ := hy'
    have hz : (MaxContactCoverData.coverMap T hv).base ((MaxContactOpenCover.coverPieceι T hv i).base z) =
        ((MaxContactCoverData.chosenCoverData T hv).opens i).ι.base z := by
      rw [← hcompι]
      rfl
    rw [hz]
    exact range_ι_base_subset _ ⟨z, rfl⟩
  rcases hgood.dichotomy i with ⟨hdisj, htop⟩ | ⟨n, c, j, hloc, hmc⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro y hy hy2
      have hy3 : y ∈ orderAtLeastLocus
          ((MaxContactCoverData.balancedTunedIdeal T hv).comap (MaxContactCoverData.coverMap T hv))
          (MaxContactCoverData.tunedMult T) := hy
      rw [orderAtLeastLocus_comap T.base T.structMap (MaxContactCoverData.coverMap T hv)
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)] at hy3
      have hy4 : (MaxContactCoverData.coverMap T hv).base y ∈
          orderAtLeastLocus (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) := hy3
      exact (Set.disjoint_left.mp hdisj) hy4 (hsub y hy2)
    · rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, htop]
      exact Scheme.IdealSheafData.comap_top _
  · right
    refine ⟨n, localCoverEtaleChart T hv i c, j, ?_, ?_⟩
    · rw [restrictIdeal_coverTripleOpen_coverMaxContactIdeal T hv hres i, hloc]
      exact (localCoverEtaleChart_coordIdeal T hv i c {j}).symm
    · have hmc' : c.coordIdeal {j} ≤
          (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap
            ((MaxContactCoverData.chosenCoverData T hv).opens i).ι := hmc
      have hmax : maxContactIdeal (MaxContactCoverData.coverTriple T hv).base
            (MaxContactCoverData.coverTriple T hv).structMap
            (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T) =
          (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap (MaxContactCoverData.coverMap T hv) :=
        derivIdealSheafIterate_comap T.base T.structMap (MaxContactCoverData.coverMap T hv)
          (MaxContactCoverData.tunedMult T - 1) (MaxContactCoverData.balancedTunedIdeal T hv)
      have h1 : (localCoverEtaleChart T hv i c).coordIdeal {j}
          = (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv :=
        localCoverEtaleChart_coordIdeal T hv i c {j}
      have h2 := comap_comap_eq_of_comp_eq (MaxContactOpenCover.coverTripleOpen T hv i).ι
        (MaxContactCoverData.coverMap T hv)
        (MaxContactOpenCover.coverPieceIso T hv i).inv ((MaxContactCoverData.chosenCoverData T hv).opens i).ι
        (MaxContactOpenCover.coverTripleOpen_ι_comp_coverMap T hv i)
        (maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
          (MaxContactCoverData.tunedMult T))
      have h3 : (c.coordIdeal {j}).comap (MaxContactOpenCover.coverPieceIso T hv i).inv ≤
          ((maxContactIdeal T.base T.structMap (MaxContactCoverData.balancedTunedIdeal T hv)
            (MaxContactCoverData.tunedMult T)).comap
              ((MaxContactCoverData.chosenCoverData T hv).opens i).ι).comap
            (MaxContactOpenCover.coverPieceIso T hv i).inv :=
        Scheme.IdealSheafData.comap_mono _ hmc'
      show (localCoverEtaleChart T hv i c).coordIdeal {j} ≤
        restrictIdeal (maxContactIdeal (MaxContactCoverData.coverTriple T hv).base
          (MaxContactCoverData.coverTriple T hv).structMap
          (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T))
          (MaxContactOpenCover.coverTripleOpen T hv i)
      rw [hmax]
      exact (le_of_eq h1).trans (le_of_le_of_eq h3 h2.symm)

theorem inStrictNormalCrossingPositionAt_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] x := by
  obtain ⟨i, hxi⟩ := MaxContactOpenCover.exists_mem_coverTripleOpen T hv x
  have h1 := MaxContactOpenCover.restrictIdeal_coverTripleOpen T hv i (MaxContactCoverData.coverMaxContactIdeal T hv)
  rcases hgood.dichotomy i with ⟨_hdisj, htop⟩ | ⟨n, c, j, hlocal, _hmc⟩
  · have h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap
        (MaxContactOpenCover.coverPieceIso T hv i).inv = ⊤ := by
      rw [hres i, htop]
      exact Scheme.IdealSheafData.comap_top _
    have key := h1.trans h2
    have hsm : AlgebraicGeometry.Smooth (MaxContactCoverData.coverTriple T hv).structMap := by
      have := MaxContactCoverData.smooth_coverMap_of_isAdmissible T hv
      have := hv.smooth
      exact (inferInstance : AlgebraicGeometry.Smooth
        (MaxContactCoverData.coverMap T hv ≫ T.structMap))
    obtain ⟨U, m, hxU, hUle, -, ⟨ch⟩⟩ :=
      exists_etaleChart_le (MaxContactCoverData.coverTriple T hv).structMap x
        (MaxContactOpenCover.coverTripleOpen T hv i) hxi
    have keyU : restrictIdeal (MaxContactCoverData.coverMaxContactIdeal T hv) U = ⊤ := by
      apply restrictIdeal_eq_top_of_le <;> assumption
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart ⟨U, hxU, m, ch, fun _ => none, ?_, ?_, ?_⟩
    · intro r _hr s _hs t hrt _hst
      simp at hrt
    · intro r hr _hnone
      have hr1 : r < 1 := hr
      have hr0 : r = 0 := by omega
      subst hr0
      exact keyU
    · intro r _hr t hrt
      simp at hrt
  · have h2 : ((MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i)).comap
        (MaxContactOpenCover.coverPieceIso T hv i).inv = (localCoverEtaleChart T hv i c).coordIdeal {j} := by
      rw [hres i, hlocal, localCoverEtaleChart_coordIdeal]
    have key := h1.trans h2
    refine inStrictNormalCrossingPositionAt_of_exists_etaleChart
      ⟨MaxContactOpenCover.coverTripleOpen T hv i, hxi, n, localCoverEtaleChart T hv i c, fun _ => some j,
        ?_, ?_, ?_⟩
    · intro r hr s hs t _hrt _hst
      have hr1 : r < 1 := hr
      have hs1 : s < 1 := hs
      omega
    · intro r _hr hnone
      simp at hnone
    · intro r hr t hrt
      have hr1 : r < 1 := hr
      have hr0 : r = 0 := by omega
      subst hr0
      obtain rfl : j = t := Option.some.inj hrt
      exact key

theorem inStrictNormalCrossingPosition_coverMaxContactIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hres : ∀ i : (MaxContactCoverData.chosenCoverData T hv).idx,
      (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
        (MaxContactCoverData.chosenCoverData T hv).localIdeal i)
    (hsm : IsSmoothDivisor (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverMaxContactIdeal T hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] := by
  refine (inStrictNormalCrossingPosition_iff _ _).mpr
    ⟨?_, fun x => inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood hres x⟩
  intro D hD
  have hD' : D = MaxContactCoverData.coverMaxContactIdeal T hv := List.mem_singleton.mp hD
  subst hD'
  exact hsm

end FunctorialResolution.EmbeddedResolution

end
