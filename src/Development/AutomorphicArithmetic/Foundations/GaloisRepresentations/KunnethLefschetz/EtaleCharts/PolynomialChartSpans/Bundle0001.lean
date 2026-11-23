module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0002
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0002
public import Development.AutomorphicArithmetic.WhittakerHecke.Bundle0001
public import Development.AutomorphicArithmetic.WhittakerHecke.IdealSheafComapEqSpecIdealSheafOfEqMap
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BChartEx
section
open CategoryTheory Limits AlgebraicGeometry TensorProduct
open FunctorialResolution.Blowup FunctorialResolution.EmbeddedResolution

theorem UpperTheory.Gal.KunnethLefschetz.G.bChartEx :
    UpperTheory.Gal.KunnethLefschetz.G.BChartEx := by
  intro R _ X W π I hπ N D A _ φ hφ hI
  classical
  set J : Ideal (MvPolynomial (Fin D) A) := coordIdeal A Finset.univ with hJ
  have hIJ : I.ideal N = Ideal.map φ J := by
    rw [show I.ideal N = _ from hI, hJ, coordIdeal_eq_span, Ideal.map_span, Finset.coe_univ,
      Set.image_univ, ← Set.range_comp]
    rfl
  have hcomap := UpperTheory.idealSheaf_comap_eq_specIdealSheaf_of_eq_map I N J φ hIJ
  haveI hfl : Flat ((IsAffineOpen.isoSpec N.2).hom ≫ Spec.map (CommRingCat.ofHom φ)) := by
    have h2 : Flat (Spec.map (CommRingCat.ofHom φ)) := Flat.SpecMap_iff.2 hφ
    exact MorphismProperty.comp_mem @Flat _ _ inferInstance h2
  have hres := hπ.restrict N.1
  rw [hcomap] at hres
  obtain ⟨q, -, hpb⟩ :=
    (isBlowupAlongIdealSheaf_affineBlowup_toSpec J).exists_isPullback_of_flat _ hres
  obtain ⟨c, hc, hcomp, hcov, hint⟩ := UpperTheory.exists_affineBlowup_coordinate_chart_cover A D
  haveI := hc
  have key := fun j => UpperTheory.isAffineOpen_image_pullback_openImmersion_chart (Over.Hom.left π) N.1 N.2 φ (AffineBlowup.toSpec J) q hpb
      (coordBlowupSubst A Finset.univ j).toRingHom (c j) (hcomp j)
  choose haff hle ρ hpush hbo using key
  have hy : ∀ j, (fun k => ρ j (if k = j then 1 else MvPolynomial.X k)) =
      fun k => if k = j then 1 else ρ j (MvPolynomial.X k) := by
    intro j
    funext k
    split_ifs <;> simp
  have alg := fun j => UpperTheory.surjective_eval_coordBlowupSubst_pushout_of_flat φ hφ j (Scheme.Hom.appLE (Over.Hom.left π) N.1 _ (hle j)).hom
    (ρ j) (hpush j)
  refine ⟨{ V := fun j => (Over.Hom.left π ⁻¹ᵁ N.1).ι ''ᵁ q ⁻¹ᵁ (c j).opensRange
            aff := haff
            le := hle
            cov := ?_
            y := fun j k => ρ j (if k = j then 1 else MvPolynomial.X k)
            surj := fun j => ?_
            ker := fun j => ?_
            inter := fun j k => hbo j _ _ (hint j k)
            nzd := fun j => (alg j).2.2 }⟩
  · apply le_antisymm (iSup_le hle)
    intro x hx
    have hmem : q ⟨x, hx⟩ ∈ ⨆ j, (c j).opensRange := by
      rw [hcov]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, ⟨x, hx⟩, hj, rfl⟩
  · rw [hy j]
    exact (alg j).1
  · rw [hy j]
    exact (alg j).2.1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.BlowUpOff
section
open CategoryTheory Limits AlgebraicGeometry

theorem UpperTheory.Gal.KunnethLefschetz.G.blOff :
    UpperTheory.Gal.KunnethLefschetz.G.BlowUpOff := by
  intro R _ _ Z W _ _ π hπ
  have hdg : IsClosedImmersion (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)) := by
    change IsClosedImmersion (pullback.diagonal (Over.hom Z))
    infer_instance
  have hft : LocallyOfFiniteType (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) := by
    change LocallyOfFiniteType (pullback.fst (Over.hom Z) (Over.hom Z) ≫ Over.hom Z)
    infer_instance
  have hln : IsLocallyNoetherian (Over.left (UpperTheory.Gal.KunnethLefschetz.G.XX Z)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Over.hom (UpperTheory.Gal.KunnethLefschetz.G.XX Z))
  have hsupp : ((Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support : Set _) =
      Set.range (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)) := by
    rw [Scheme.Hom.support_ker]
    exact (Scheme.Hom.isClosedEmbedding (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).isClosed_range.closure_eq
  refine ⟨FunctorialResolution.Blowup.isProper_of_isBlowupAlongIdealSheaf hπ, ?_, ?_⟩
  · change IsClosedImmersion (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z)))
    infer_instance
  · intro U hU
    have hUeq : U = (Scheme.Hom.ker (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))).support.compl := by
      apply SetLike.coe_injective
      rw [hU]
      simp [hsupp]
    subst hUeq
    refine ⟨FunctorialResolution.Blowup.blowupIsIsoOffCenter _ _ _ _ hπ, ?_⟩
    change _ = (Set.range (pullback.fst (Over.Hom.left π) (Over.Hom.left (UpperTheory.Gal.KunnethLefschetz.G.dg Z))))ᶜ
    rw [Scheme.Pullback.range_fst]
    simp [hsupp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.CoordEx
section
noncomputable section
open CategoryTheory AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections

namespace UpperTheory.Gal.KunnethLefschetz.G

theorem coordEx : CoordEx := by
  intro R _ Z D _ z
  obtain ⟨-, -, V, hV, hzV, -, -⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := D) (f := Z.hom) z
  obtain ⟨s, hs, hsQ⟩ := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) Z.hom inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)
  have hz : z ∈ ⨆ f : s, Z.left.basicOpen f.1 := (hV.self_le_iSup_basicOpen_iff.mpr hs) hzV
  rw [TopologicalSpace.Opens.mem_iSup] at hz
  obtain ⟨⟨t, ht⟩, hzt⟩ := hz
  have hQ : RingHom.IsStandardSmoothOfRelativeDimension D _ := hsQ t ht
  have hle : Z.left.basicOpen t ≤ Z.hom ⁻¹ᵁ ⊤ := by simp
  have hVle : V ≤ Z.hom ⁻¹ᵁ ⊤ := by simp
  have key : RingHom.IsStandardSmoothOfRelativeDimension D
      (Z.hom.appLE ⊤ (Z.left.basicOpen t) hle).hom := by
    have := hV.isLocalization_basicOpen t
    let e := IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t)
      Γ(Z.left, Z.left.basicOpen t)
    have h1 : (Z.hom.appLE ⊤ (Z.left.basicOpen t) hle).hom =
        (e : Localization.Away t ≃+* Γ(Z.left, Z.left.basicOpen t)).toRingHom.comp
          ((algebraMap _ (Localization.Away t)).comp (Z.hom.appLE ⊤ V hVle).hom) := by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
      rw [RingHom.algebraMap_toAlgebra]
      show _ = (Z.hom.appLE ⊤ V hVle ≫
        Z.left.presheaf.map (homOfLE (Z.left.basicOpen_le t)).op).hom x
      rw [Scheme.Hom.appLE_map]
    rw [h1]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _ _ hQ
  have hR : RingHom.IsStandardSmoothOfRelativeDimension D
      (algebraMap R (Sec Z (Z.left.basicOpen t))) :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv key
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap] at hR
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial D R
    (Sec Z (Z.left.basicOpen t))
  refine ⟨Z.left.basicOpen t, fun i ↦ g (MvPolynomial.X i), hzt, hV.basicOpen t, ?_⟩
  rwa [← Function.comp_def g MvPolynomial.X, ← MvPolynomial.aeval_unique]

end UpperTheory.Gal.KunnethLefschetz.G
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.PolynomialChartSpans.DCoord
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.DifferentialFormSections
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz.G

section Alg
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {D : ℕ}

private def shear (u : Fin D → B) : MvPolynomial (Fin D) B ≃ₐ[B] MvPolynomial (Fin D) B :=
  AlgEquiv.ofAlgHom (MvPolynomial.aeval fun k => MvPolynomial.X k - MvPolynomial.C (u k))
    (MvPolynomial.aeval fun k => MvPolynomial.X k + MvPolynomial.C (u k))
    (by ext k; simp) (by ext k; simp)

private theorem shear_X (u : Fin D → B) (k : Fin D) :
    shear u (MvPolynomial.X k) = MvPolynomial.X k - MvPolynomial.C (u k) := by
  simp [shear]

private theorem shear_C (u : Fin D → B) (b : B) : shear u (MvPolynomial.C b) = MvPolynomial.C b :=
  (shear u).commutes b

private theorem etale_diff (u : Fin D → B)
    (h : (MvPolynomial.aeval u : MvPolynomial (Fin D) R →ₐ[R] B).toRingHom.Etale) :
    (MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)
      (fun k => (1 : B) ⊗ₜ[R] u k - u k ⊗ₜ[R] (1 : B))).Etale := by
  classical
  letI algA : Algebra (MvPolynomial (Fin D) R) B := (MvPolynomial.aeval u).toRingHom.toAlgebra
  letI algP : Algebra (MvPolynomial (Fin D) R) (MvPolynomial (Fin D) B) :=
    MvPolynomial.algebraMvPolynomial
  letI smP : SMul (MvPolynomial (Fin D) R) (MvPolynomial (Fin D) B) := algP.toSMul
  letI modP : Module (MvPolynomial (Fin D) R) (MvPolynomial (Fin D) B) := algP.toModule
  have t1 : IsScalarTower R (MvPolynomial (Fin D) R) B :=
    IsScalarTower.of_algebraMap_eq fun r => by
      simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  let hm : MvPolynomial (Fin D) B →+* B ⊗[R] B :=
    MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B).toRingHom
      (fun k => u k ⊗ₜ[R] (1 : B))
  letI algPT : Algebra (MvPolynomial (Fin D) B) (B ⊗[R] B) := hm.toAlgebra
  have t2 : IsScalarTower (MvPolynomial (Fin D) R) B (B ⊗[R] B) := inferInstance
  have hcomp : (algebraMap (MvPolynomial (Fin D) R) (B ⊗[R] B)) =
      hm.comp (MvPolynomial.map (algebraMap R B)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [hm, Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra,
        Algebra.TensorProduct.tmul_one_eq_one_tmul]
    · intro i
      simp [hm, Algebra.TensorProduct.algebraMap_apply, RingHom.algebraMap_toAlgebra]
  have t3 : IsScalarTower (MvPolynomial (Fin D) R) (MvPolynomial (Fin D) B) (B ⊗[R] B) :=
    IsScalarTower.of_algebraMap_eq fun p => by
      have := congrArg (fun f => f p) hcomp
      simpa [RingHom.algebraMap_toAlgebra] using this
  have t4 : IsScalarTower R (MvPolynomial (Fin D) R) (B ⊗[R] B) := inferInstance
  have hf : IsBaseChange (MvPolynomial (Fin D) R)
      (IsScalarTower.toAlgHom R B (MvPolynomial (Fin D) B)).toLinearMap :=
    (inferInstance : Algebra.IsPushout R (MvPolynomial (Fin D) R) B (MvPolynomial (Fin D) B)).out
  have hpush : Algebra.IsPushout (MvPolynomial (Fin D) R) B (MvPolynomial (Fin D) B) (B ⊗[R] B) := by
    constructor
    refine IsBaseChange.of_comp (T := B) hf ?_
    convert TensorProduct.isBaseChange R B B using 1
    all_goals try rfl
    all_goals try (apply LinearMap.ext; intro b; simp [hm, RingHom.algebraMap_toAlgebra])
  have hE : hm.Etale :=
    RingHom.Etale.isStableUnderBaseChange (MvPolynomial (Fin D) R) B (MvPolynomial (Fin D) B)
      (B ⊗[R] B) h
  have heq : MvPolynomial.eval₂Hom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] B)
      (fun k => (1 : B) ⊗ₜ[R] u k - u k ⊗ₜ[R] (1 : B)) =
      (Algebra.TensorProduct.comm R B B).toAlgHom.toRingHom.comp
        (hm.comp (shear u).toAlgHom.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [hm, shear_C]
    · intro i
      simp [hm, shear_X]
  rw [heq]
  refine RingHom.Etale.stableUnderComposition _ _ ?_ (RingHom.Etale.of_bijective
    (Algebra.TensorProduct.comm R B B).bijective)
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective
    (shear u).bijective) hE
end Alg

section Geo
variable {R : Type} [CommRing R]

private theorem fromSpec_hom (Z : Sch R) {U : Z.left.Opens} (hU : IsAffineOpen U) :
    (show Spec (CommRingCat.of (Sec Z U)) ⟶ Z.left from hU.fromSpec) ≫ Z.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (Sec Z U))) := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec Z.hom (isAffineOpen_top (Spec (CommRingCat.of R))) hU
    (by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at e
  show hU.fromSpec ≫ Z.hom = _
  rw [← e]
  rfl

private theorem etale_prod (Z : Sch R) {U : Z.left.Opens} (hU : IsAffineOpen U) {N : (XX Z).left.Opens}
    (hN : IsAffineOpen N) (h1 : N ≤ (p1 Z).left ⁻¹ᵁ U) (h2 : N ≤ (p2 Z).left ⁻¹ᵁ U) :
    (Algebra.TensorProduct.productMap (secMap (p1 Z) h1) (secMap (p2 Z) h2)).toRingHom.Etale := by
  let sA : Spec (CommRingCat.of (Sec Z U)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Sec Z U)))
  let a : Spec (CommRingCat.of (Sec Z U)) ⟶ Z.left := hU.fromSpec
  have ha : a ≫ Z.hom = sA := fromSpec_hom Z hU
  haveI : IsOpenImmersion a := IsAffineOpen.isOpenImmersion_fromSpec hU
  let m : pullback sA sA ⟶ pullback Z.hom Z.hom :=
    pullback.map sA sA Z.hom Z.hom a a (𝟙 _) (by rw [Category.comp_id, ha])
      (by rw [Category.comp_id, ha])
  let fN : Spec Γ((XX Z).left, N) ⟶ pullback Z.hom Z.hom := hN.fromSpec
  let g1 : Spec Γ((XX Z).left, N) ⟶ Spec (CommRingCat.of (Sec Z U)) :=
    Spec.map ((p1 Z).left.appLE U N h1)
  let g2 : Spec Γ((XX Z).left, N) ⟶ Spec (CommRingCat.of (Sec Z U)) :=
    Spec.map ((p2 Z).left.appLE U N h2)
  have e1 : g1 ≫ a = fN ≫ pullback.fst Z.hom Z.hom :=
    IsAffineOpen.SpecMap_appLE_fromSpec (p1 Z).left hU hN h1
  have e2 : g2 ≫ a = fN ≫ pullback.snd Z.hom Z.hom :=
    IsAffineOpen.SpecMap_appLE_fromSpec (p2 Z).left hU hN h2
  have w : g1 ≫ sA = g2 ≫ sA := by
    rw [← ha, ← Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc,
      pullback.condition]
  let g : Spec Γ((XX Z).left, N) ⟶ pullback sA sA := pullback.lift g1 g2 w
  have hgm : g ≫ m = fN := by
    apply pullback.hom_ext
    · simp only [g, m, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, e1]
    · simp only [g, m, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, e2]
  haveI : IsOpenImmersion fN := IsAffineOpen.isOpenImmersion_fromSpec hN
  haveI : Etale (g ≫ m) := by rw [hgm]; infer_instance
  haveI : Etale g := Etale.of_comp g m
  let φ : Sec Z U ⊗[R] Sec Z U →+* Sec (XX Z) N :=
    (Algebra.TensorProduct.productMap (secMap (p1 Z) h1) (secMap (p2 Z) h2)).toRingHom
  let g' : Spec (CommRingCat.of (Sec (XX Z) N)) ⟶ pullback sA sA := g
  haveI : Etale g' := inferInstanceAs (Etale g)
  have key : Spec.map (CommRingCat.ofHom φ) ≫ (pullbackSpecIso R (Sec Z U) (Sec Z U)).inv = g' := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
      refine Eq.trans ?_ (pullback.lift_fst g1 g2 w).symm
      congr 1
      ext x
      simp [φ, secMap]
      rfl
    · rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
      refine Eq.trans ?_ (pullback.lift_snd g1 g2 w).symm
      congr 1
      ext x
      simp [φ, secMap]
      rfl
  have key' : Spec.map (CommRingCat.ofHom φ) = g' ≫ (pullbackSpecIso R (Sec Z U) (Sec Z U)).hom := by
    rw [← key, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hE : Etale (Spec.map (CommRingCat.ofHom φ)) := by rw [key']; infer_instance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hE
end Geo

theorem dCoord : DCoord := by
  intro R _ Z D c
  have h := etale_diff (R := R) c.u c.coord.2
  have h' := etale_prod Z c.coord.1 c.aff c.h1 c.h2
  have h3 := RingHom.Etale.stableUnderComposition _ _ h h'
  convert h3 using 1
  refine MvPolynomial.ringHom_ext (fun b => ?_) fun k => ?_
  · simp [MvPolynomial.coe_eval₂Hom]
  · simp [DChart.s, MvPolynomial.coe_eval₂Hom]

end UpperTheory.Gal.KunnethLefschetz.G
end
end

