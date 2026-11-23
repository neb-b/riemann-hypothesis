module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedLocusFlatBaseChange

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceChartPresentation
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem affineSpace_reindex_symm_comp_reindex {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace.reindex (e.symm : m → n) S ≫ AffineSpace.reindex (e : n → m) S =
      𝟙 (AffineSpace n S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

theorem affineSpace_reindex_comp_reindex_symm {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace.reindex (e : n → m) S ≫ AffineSpace.reindex (e.symm : m → n) S =
      𝟙 (AffineSpace m S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

def affineSpaceIsoOfEquiv {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace n S ≅ AffineSpace m S where
  hom := AffineSpace.reindex (e.symm : m → n) S
  inv := AffineSpace.reindex (e : n → m) S
  hom_inv_id := affineSpace_reindex_symm_comp_reindex e S
  inv_hom_id := affineSpace_reindex_comp_reindex_symm e S

theorem affineSpaceIsoOfEquiv_hom_comp_over {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).hom ≫ (AffineSpace m S ↘ S) = (AffineSpace n S ↘ S) := by
  simp [affineSpaceIsoOfEquiv, AffineSpace.reindex]

theorem affineSpaceIsoOfEquiv_hom_comp_toSpec (k : Type u) [Field k] {n m : Type u} (e : n ≃ m) :
    (affineSpaceIsoOfEquiv e (Spec (CommRingCat.of k))).hom ≫ affineSpaceIndexedByToSpec k m =
      affineSpaceIndexedByToSpec k n := by
  exact affineSpaceIsoOfEquiv_hom_comp_over e (Spec (CommRingCat.of k))

def uliftFinSumOneEquiv (n : ℕ) : ULift.{u, 0} (Fin n ⊕ Fin 1) ≃ ULift.{u, 0} (Fin (n + 1)) :=
  Equiv.ulift.trans (finSumFinEquiv.trans Equiv.ulift.symm)

def toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    G.ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (n + 1))) :=
  φ.hom ≫ affineSpaceInl k n 1 ≫
    (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom

theorem isClosedImmersion_toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    AlgebraicGeometry.IsClosedImmersion (toAffineSpaceOfAmbientIso G n φ) := by
  have h : AlgebraicGeometry.IsClosedImmersion
      (φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) :=
    inferInstance
  exact h

theorem toAffineSpaceOfAmbientIso_comp_toSpec {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    toAffineSpaceOfAmbientIso G n φ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))) =
      G.ambientStruct := by
  have h : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [h]
  simp only [Category.assoc]
  rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, hφ]

theorem hasSmoothCoordCodim_toAffineSpaceOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u}
    [Field k] [CharZero k] {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (toAffineSpaceOfAmbientIso G n φ) 1 := by
  have h1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin 1)))
      (affineSpaceInl k n 1) 1 := hasSmoothCoordCodim_affineSpaceInl hsm k n 1
  have h2 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) 1 :=
    h1.comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumOneEquiv.{u} n))
  have hdef : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [hdef]
  exact h2.iso_hom_comp φ

def presentationOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    ClosedEmbeddingIntoAffineSpace G where
  codimBound := 1
  dim := n + 1
  toAffine := toAffineSpaceOfAmbientIso G n φ
  one_le_codimBound := le_rfl
  one_le_dim := Nat.succ_le_succ (Nat.zero_le n)
  isClosedImmersion_toAffine := isClosedImmersion_toAffineSpaceOfAmbientIso G n φ
  toAffine_comp := toAffineSpaceOfAmbientIso_comp_toSpec G n φ hφ
  locallyConstCodim := hasSmoothCoordCodim_toAffineSpaceOfAmbientIso hsm G n φ

def affineSpaceChartPresentation (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    ClosedEmbeddingIntoAffineSpace (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) :=
  presentationOfAmbientIso hsm (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) ((hemb k Y pY).choose)
    (Iso.refl _) (by exact Category.id_comp _)

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.DetachedCenterFlatBaseChange
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace ChartFlatBaseChange

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']
  {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

private theorem map_eq_ker_subschemeι_comp {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) :
    I.map f = Scheme.Hom.ker (I.subschemeι ≫ f) := rfl

theorem comapAmbientCenter_eq_comap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    S'.comapAmbientCenter j =
      (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have h1 : S'.ambientCenter j
      = (S.ambientCenter (F.reindex j)).comap (F.levelMap j hj.le) := F.center_eq j hj
  have h2 : F.strictTransformComparison j hj.le ≫ S.strictTransformι (F.reindex j)
      = S'.strictTransformι j ≫ F.levelMap j hj.le := F.strictTransformComparison_comp_strictTransformι j hj.le
  calc S'.comapAmbientCenter j = (S'.ambientCenter j).comap (S'.strictTransformι j) := rfl
    _ = ((S.ambientCenter (F.reindex j)).comap (F.levelMap j hj.le)).comap (S'.strictTransformι j) := by
        rw [h1]
    _ = (S.ambientCenter (F.reindex j)).comap (S'.strictTransformι j ≫ F.levelMap j hj.le) := by
        simp [Scheme.IdealSheafData.comap_comp]
    _ = (S.ambientCenter (F.reindex j)).comap
          (F.strictTransformComparison j hj.le ≫ S.strictTransformι (F.reindex j)) := by rw [h2]
    _ = ((S.ambientCenter (F.reindex j)).comap (S.strictTransformι (F.reindex j))).comap
          (F.strictTransformComparison j hj.le) := by simp [Scheme.IdealSheafData.comap_comp]
    _ = (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) := rfl

theorem centerOffDetached_eq_comap (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    S'.centerOffDetached j =
      (S.centerOffDetached (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have hflat : AlgebraicGeometry.Flat (F.strictTransformComparison j hj.le) := F.flat_strictTransformComparison j hj.le
  have hnoe : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have hqc : AlgebraicGeometry.QuasiCompact (S.detachedClosureCompl (F.reindex j)).ι :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hpb : IsPullback (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j))
      ((F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F.reindex j)).ι)
      (S.detachedClosureCompl (F.reindex j)).ι (F.strictTransformComparison j hj.le) :=
    AlgebraicGeometry.isPullback_morphismRestrict _ _
  have key := comap_map_eq_map_comap_of_isPullback hpb
      ((S.comapAmbientCenter (F.reindex j)).comap (S.detachedClosureCompl (F.reindex j)).ι)
  have htrace : S'.comapAmbientCenter j
      = (S.comapAmbientCenter (F.reindex j)).comap (F.strictTransformComparison j hj.le) :=
    F.comapAmbientCenter_eq_comap j hj
  have hcomap :
      ((S.comapAmbientCenter (F.reindex j)).comap (S.detachedClosureCompl (F.reindex j)).ι).comap
          (F.strictTransformComparison j hj.le ∣_ S.detachedClosureCompl (F.reindex j))
        = (S'.comapAmbientCenter j).comap
            ((F.strictTransformComparison j hj.le ⁻¹ᵁ S.detachedClosureCompl (F.reindex j)).ι) := by
    rw [htrace, ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hpb.w]
  rw [S'.centerOffDetached_eq j, S.centerOffDetached_eq (F.reindex j),
    ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeι_comp (S'.detachedClosureCompl j).ι, ← _root_.FunctorialResolution.EmbeddedResolution.ChartFlatBaseChange.map_eq_ker_subschemeι_comp (S.detachedClosureCompl (F.reindex j)).ι,
    F.detachedClosureCompl_eq_preimage j hj, key, hcomap]

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
end

