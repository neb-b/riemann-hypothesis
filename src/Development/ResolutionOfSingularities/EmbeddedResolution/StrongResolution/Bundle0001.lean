module

public import Mathlib
public import Development.ResolutionOfSingularities.Foundations.Blowup.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0003
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionData
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineEmbeddingIntoAffineSpace
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private noncomputable def extendAlgHomLastVarZero {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) :
    MvPolynomial (ULift.{u} (Fin (n + 1))) k →ₐ[k] A :=
  MvPolynomial.aeval fun i : ULift.{u} (Fin (n + 1)) =>
    Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down

private theorem extension_X_last_eq_zero {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) :
    extendAlgHomLastVarZero f (MvPolynomial.X (ULift.up (Fin.last n))) = 0 := by
  simp [extendAlgHomLastVarZero]

private theorem extension_surjective {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
    {n : ℕ} (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f) :
    Function.Surjective (extendAlgHomLastVarZero f) := by
  intro a
  obtain ⟨q, rfl⟩ := hf a
  refine ⟨MvPolynomial.rename
    (fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1)))) q, ?_⟩
  show MvPolynomial.aeval (fun i : ULift.{u} (Fin (n + 1)) =>
      Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down)
      (MvPolynomial.rename (fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1)))) q)
      = f q
  rw [MvPolynomial.aeval_rename]
  have h : ((fun i : ULift.{u} (Fin (n + 1)) =>
      Fin.lastCases (motive := fun _ => A) 0 (fun j => f (MvPolynomial.X j)) i.down) ∘
      fun j : Fin n => (ULift.up j.castSucc : ULift.{u} (Fin (n + 1))))
      = fun j : Fin n => f (MvPolynomial.X j) := by
    funext j
    simp
  rw [h]
  exact DFunLike.congr_fun (MvPolynomial.aeval_unique f).symm q

private noncomputable def toAffineSpaceOfAlgHom {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤)) :
    Y ⟶ affineSpaceIndexedBy k m :=
  Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    (AffineSpace.SpecIso m (CommRingCat.of k)).inv

private theorem isoSpec_hom_comp_spec_map_appTop {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) :
    Y.isoSpec.hom ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop) = p := by
  have h2 : Y.isoSpec.hom = Y.toSpecΓ := rfl
  rw [h2, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality p,
    ← SpecMap_ΓSpecIso_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

private theorem isClosedImmersion_embedding_and_comp_eq {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (p : Y ⟶ Spec (CommRingCat.of k))
    (halg : algebraMap k ↥Γ(Y, ⊤)
      = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom))
    (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤)) (hg : Function.Surjective g) :
    IsClosedImmersion (toAffineSpaceOfAlgHom Y g) ∧
      toAffineSpaceOfAlgHom Y g ≫ (affineSpaceIndexedBy k m ↘ Spec (CommRingCat.of k)) = p := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hg
  constructor
  · show IsClosedImmersion (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv)
    infer_instance
  · show (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv) ≫
      (affineSpaceIndexedBy k m ↘ Spec (CommRingCat.of k)) = p
    rw [Category.assoc, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    have h2 : CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial m k) ≫
        CommRingCat.ofHom g.toRingHom
        = (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop := by
      refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
      show g (MvPolynomial.C a) = _
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, halg]
    rw [h2]
    exact isoSpec_hom_comp_spec_map_appTop Y p

private theorem isIrreducible_univ_affineSpaceIndexedBy (k : Type u) [Field k] (m : Type u) :
    IsIrreducible (Set.univ : Set ↥(affineSpaceIndexedBy k m)) := by
  have h0 : IsIrreducible (Set.univ : Set ↥(Spec (CommRingCat.of (MvPolynomial m k)))) :=
    IrreducibleSpace.isIrreducible_univ (PrimeSpectrum (MvPolynomial m k))
  have h1 := h0.image (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm)
    (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm).continuous.continuousOn
  rwa [Set.image_univ,
    (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k)).symm).surjective.range_eq] at h1

private theorem eq_univ_of_mem_irreducibleComponents_of_isIrreducible_univ {X : Type u} [TopologicalSpace X]
    (h : IsIrreducible (Set.univ : Set X)) {T : Set X} (hT : T ∈ irreducibleComponents X) :
    T = Set.univ :=
  Set.eq_univ_of_univ_subset (hT.2 h (Set.subset_univ T))

private theorem support_ker_ne_univ_of_map_X_eq_zero {k : Type u} [Field k] (Y : Scheme.{u}) [IsAffine Y]
    {m : Type u} [Algebra k ↥Γ(Y, ⊤)] (g : MvPolynomial m k →ₐ[k] ↥Γ(Y, ⊤))
    (x₀ : m) (hx₀ : g (MvPolynomial.X x₀) = 0) [QuasiCompact (toAffineSpaceOfAlgHom Y g)] :
    ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m)) ≠ Set.univ := by
  intro hcon
  have hcomp : toAffineSpaceOfAlgHom Y g ≫ (AffineSpace.SpecIso m (CommRingCat.of k)).hom
      = Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
    show (Y.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).inv) ≫
      (AffineSpace.SpecIso m (CommRingCat.of k)).hom = _
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmem0 : ∀ w : PrimeSpectrum ↥Γ(Y, ⊤),
      (MvPolynomial.X x₀ : MvPolynomial m k) ∈
        ((Spec.map (CommRingCat.ofHom g.toRingHom)).base w).asIdeal := by
    intro w
    show g (MvPolynomial.X x₀) ∈ w.asIdeal
    rw [hx₀]
    exact Ideal.zero_mem _
  obtain ⟨v, hv, hvcont, hvsurj⟩ :
      ∃ v : ↥(affineSpaceIndexedBy k m) → PrimeSpectrum (MvPolynomial m k),
        (∀ y : ↥Y, v ((toAffineSpaceOfAlgHom Y g).base y)
            = (Spec.map (CommRingCat.ofHom g.toRingHom)).base (Y.isoSpec.hom.base y)) ∧
          Continuous v ∧ Function.Surjective v := by
    refine ⟨fun x => (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))) x, ?_, ?_, ?_⟩
    · intro y
      exact congrArg
        (fun φ : Y ⟶ Spec (CommRingCat.of (MvPolynomial m k)) => φ.base y) hcomp
    · exact (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))).continuous
    · exact (Scheme.homeoOfIso (AffineSpace.SpecIso m (CommRingCat.of k))).surjective
  have hrange : ∀ y : ↥Y,
      (MvPolynomial.X x₀ : MvPolynomial m k) ∈ (v ((toAffineSpaceOfAlgHom Y g).base y)).asIdeal := by
    intro y
    rw [hv y]
    exact hmem0 _
  have hsub : Set.range (toAffineSpaceOfAlgHom Y g).base ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
    rintro _ ⟨y, rfl⟩
    have : v ((toAffineSpaceOfAlgHom Y g).base y) ∈
        PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact hrange y
    exact this
  have hsupp : ((toAffineSpaceOfAlgHom Y g).ker.support : Set ↥(affineSpaceIndexedBy k m))
      = closure (Set.range (toAffineSpaceOfAlgHom Y g).base) := Scheme.Hom.support_ker _
  have huniv : (Set.univ : Set ↥(affineSpaceIndexedBy k m)) ⊆
      v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} := by
    rw [← hcon, hsupp]
    exact closure_minimal hsub ((PrimeSpectrum.isClosed_zeroLocus _).preimage hvcont)
  obtain ⟨ξ, hξ⟩ := hvsurj ⟨⊥, Ideal.isPrime_bot⟩
  have hmem : ξ ∈ v ⁻¹' PrimeSpectrum.zeroLocus {(MvPolynomial.X x₀ : MvPolynomial m k)} :=
    huniv (Set.mem_univ ξ)
  rw [Set.mem_preimage, hξ, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hmem
  have h6 : (MvPolynomial.X x₀ : MvPolynomial m k) = 0 := Ideal.mem_bot.mp hmem
  have h7 : (1 : k) = 0 := by
    have h8 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single x₀ 1)) h6
    simp at h8
  exact one_ne_zero h7

theorem affineEmbedsIntoAffineSpace : AffineEmbedsIntoAffineSpace.{u} := by
  intro k _ Y _ p _
  have hft : RingHom.FiniteType (p.appTop).hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType) (f := p)).mp inferInstance
  have hiso : Function.Surjective ⇑((Scheme.ΓSpecIso (CommRingCat.of k)).inv) := by
    intro x
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom x, by simp⟩
  have hφ : RingHom.FiniteType
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom) := by
    rw [CommRingCat.hom_comp]
    exact hft.comp (RingHom.FiniteType.of_surjective _ hiso)
  let _ : Algebra k ↥Γ(Y, ⊤) :=
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom).toAlgebra
  have halg : algebraMap k ↥Γ(Y, ⊤)
      = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom) := rfl
  have hfta : Algebra.FiniteType k ↥Γ(Y, ⊤) := hφ
  obtain ⟨n, f, hfsurj⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'').mp hfta
  obtain ⟨hci, hover⟩ := isClosedImmersion_embedding_and_comp_eq Y p halg (extendAlgHomLastVarZero f) (extension_surjective f hfsurj)
  have := hci
  refine ⟨n + 1, toAffineSpaceOfAlgHom Y (extendAlgHomLastVarZero f), hci, ?_, hover⟩
  have hne := support_ker_ne_univ_of_map_X_eq_zero Y (extendAlgHomLastVarZero f) (ULift.up (Fin.last n)) (extension_X_last_eq_zero f)
  have hirr := isIrreducible_univ_affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1)))
  have key : ∀ T ∈ irreducibleComponents ↥(affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1)))),
      ¬ T ⊆ ((toAffineSpaceOfAlgHom Y (extendAlgHomLastVarZero f)).ker.support :
        Set ↥(affineSpaceIndexedBy k (ULift.{u} (Fin (n + 1))))) := by
    intro T hT hsubT
    refine hne (Set.eq_univ_of_univ_subset ?_)
    rw [← eq_univ_of_mem_irreducibleComponents_of_isIrreducible_univ hirr hT]
    exact hsubT
  exact key

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem algebra_smooth_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    Algebra.Smooth k (MvPolynomial (ULift.{u} (Fin n)) k) :=
  ⟨inferInstance, inferInstance⟩

private theorem ringHom_smooth_algebraMap_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    RingHom.Smooth (algebraMap k (MvPolynomial (ULift.{u} (Fin n)) k)) :=
  RingHom.smooth_algebraMap.mpr (algebra_smooth_mvPolynomial k n)

private theorem specIso_inv_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : ℕ) :
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) :=
  AffineSpace.SpecIso_inv_over _

private theorem affineSpaceIndexedByToSpec_eq (k : Type u) [Field k] (n : ℕ) :
    affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) := by
  rw [← specIso_inv_comp_affineSpaceIndexedByToSpec k n, Iso.hom_inv_id_assoc]

theorem affineSpaceIsSmooth : AffineSpaceIsSmooth.{u} := by
  intro k _ n
  have hC : AlgebraicGeometry.Smooth
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k))) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)).mpr (ringHom_smooth_algebraMap_mvPolynomial k n)
  rw [affineSpaceIndexedByToSpec_eq k n]
  infer_instance

theorem nilIsStrictNormalCrossingsOnAffineSpace : NilIsStrictNormalCrossingsOnAffineSpace.{u} := by
  intro k _ n
  refine ⟨by simp, fun x => ⟨⊤, trivial, n,
    ⟨(⊤ : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens).ι, rfl, ?_⟩,
    fun _ => none, by simp, by simp, by simp⟩⟩
  infer_instance

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionCenters
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

private theorem comp_base_apply {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (z : ↥A) :
    (a ≫ b).base z = b.base (a.base z) := by
  simp

private theorem hom_base_inv_base_apply {A B : Scheme.{u}} (e : A ≅ B) (z : ↥B) :
    e.hom.base (e.inv.base z) = z := by
  rw [← comp_base_apply, e.inv_hom_id]
  simp

private theorem mem_support_comap_of_mem_support {Z W : Scheme.{u}} (g : Z ⟶ W) (I : W.IdealSheafData)
    (z : ↥Z) (hz : g.base z ∈ I.support) : z ∈ (I.comap g).support := by
  rw [Scheme.IdealSheafData.support_comap]
  exact hz

theorem centersLieOver_smoothLocusComplement (d : LocalResolutionData k f s) :
    s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
  intro i hi x hx
  obtain ⟨i₀, u, hu⟩ : ∃ (i₀ : d.cover.I₀) (u : ↥(d.cover.X i₀)),
      (d.cover.f i₀).base u = (s.projectionToBase i).base x := by
    obtain ⟨u, hu⟩ := d.cover.covers ((s.projectionToBase i).base x)
    exact ⟨d.cover.idx ((s.projectionToBase i).base x), u, hu⟩
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback u x hu
  have hw1' : (pullback.fst (d.cover.f i₀) (s.projectionToBase i)).base w = u := hw1
  have hw2' : (pullback.snd (d.cover.f i₀) (s.projectionToBase i)).base w = x := hw2
  have hws : w ∈ ((s.center i).comap (pullback.snd (d.cover.f i₀) (s.projectionToBase i))).support := by
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rw [hw2']
    exact hx
  obtain ⟨l, hl, hr⟩ := (d.exists_reindex_eq_iff_exists_mem_support i₀ i hi).2 ⟨w, hws⟩
  subst hr
  have ht : ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈ ((d.seq i₀).center l).support := by
    rw [d.localSequence_center_eq_comap i₀ l hl]
    refine mem_support_comap_of_mem_support _ _ _ ?_
    rw [comp_base_apply, hom_base_inv_base_apply, hw2']
    exact hx
  have key : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)
      = (pullback.fst (d.cover.f i₀) (s.projectionToBase (d.reindex i₀ l))).base w := by
    rw [← d.schemeAtIsoPullback_hom_fst i₀ l hl.le, comp_base_apply, hom_base_inv_base_apply]
  have hres := d.isResolution i₀
  unfold FunctorialResolution.EmbeddedResolution.IsStrongResolution at hres
  obtain ⟨-, -, -, -, hC, -⟩ := hres
  have hCt : ((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w) ∈
      ((smoothLocusComplement (d.cover.f i₀ ≫ f) : TopologicalSpace.Closeds ↥(d.cover.X i₀)) :
        Set ↥(d.cover.X i₀)) := hC l hl _ ht
  rw [← d.preimage_smoothLocusComplement_cover_map i₀] at hCt
  have hfin : (d.cover.f i₀).base
      (((d.seq i₀).projectionToBase l).base ((d.schemeAtIsoPullback i₀ l hl.le).inv.base w)) ∈
      ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X) := hCt
  show (s.projectionToBase (d.reindex i₀ l)).base x ∈
    ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
  rw [← hu, ← hw1', ← key]
  exact hfin

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionDense
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem dense_preimage_smoothLocus (d : LocalResolutionData k f s) :
    Dense ((s.lastStructMap ⁻¹ᵁ f.smoothLocus : TopologicalSpace.Opens ↥(s.lastObj)) : Set ↥(s.lastObj)) := by
  rw [dense_iff_inter_open]
  intro V hV hVne
  obtain ⟨x, hxV⟩ := hVne
  obtain ⟨i, y, hy⟩ := d.exists_chartToLastObj_eq x
  have hres := (d.isResolution i).2.2.2.1
  have hW : IsOpen (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) :=
    ((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj))).2
  have hyW : y ∈ (((d.chartToLastObj i) ⁻¹ᵁ (⟨V, hV⟩ : TopologicalSpace.Opens ↥(s.lastObj)) :
      TopologicalSpace.Opens ↥((d.seq i).lastObj)) : Set ↥((d.seq i).lastObj)) := by
    show (d.chartToLastObj i).base y ∈ V
    rw [hy]
    exact hxV
  obtain ⟨z, hz1, hz2⟩ := dense_iff_inter_open.mp hres _ hW ⟨y, hyW⟩
  refine ⟨(d.chartToLastObj i).base z, hz1, ?_⟩
  have hmem : ((d.seq i).lastStructMap).base z ∈ (d.cover.f i) ⁻¹ᵁ f.smoothLocus := by
    rw [d.preimage_smoothLocus_cover_map i]
    exact hz2
  have hbase : (s.lastStructMap).base ((d.chartToLastObj i).base z)
      = (d.cover.f i).base (((d.seq i).lastStructMap).base z) := by
    have h := congrArg (fun m : (d.seq i).lastObj ⟶ X => m.base z) (d.chartToLastObj_comp_lastStructMap i)
    simpa using h
  show (s.lastStructMap).base ((d.chartToLastObj i).base z) ∈ f.smoothLocus
  rw [hbase]
  exact hmem

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.LocalResolutionProper
section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

def pullbackIsoLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((pullback s.lastStructMap (d.cover.f i) : Scheme.{u}) ≅ (d.seq i).lastObj) :=
  (pullbackSymmetry s.lastStructMap (d.cover.f i)).trans (d.lastObjIsoPullback i).symm

theorem pullbackIsoLastObj_hom_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.pullbackIsoLastObj i).hom ≫ (d.seq i).lastStructMap = pullback.snd s.lastStructMap (d.cover.f i) := by
  rw [pullbackIsoLastObj]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← d.lastObjIsoPullback_hom_fst i, Iso.inv_hom_id_assoc]
  exact pullbackSymmetry_hom_comp_fst _ _

theorem isProper_lastStructMap (d : LocalResolutionData k f s) : IsProper s.lastStructMap := by
  have key : ∀ i : d.cover.I₀, IsProper (d.seq i).lastStructMap := by
    intro i
    obtain ⟨-, h, -⟩ := d.isResolution i
    exact h
  obtain ⟨-, h2⟩ := (inferInstance :
    MorphismProperty.IsLocalAtTarget (@IsProper) Scheme.zariskiPrecoverage)
  refine h2 (R := d.cover.presieve₀) d.cover.mem₀ ?_
  intro U g _inst hg
  obtain ⟨i⟩ := hg
  rw [← d.pullbackIsoLastObj_hom_lastStructMap i]
  have := key i
  infer_instance

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
end

