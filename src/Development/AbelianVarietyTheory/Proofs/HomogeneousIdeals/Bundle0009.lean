module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import ReciprocityTheory.SemistableReduction.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
section
namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial MeasureTheory Module
open scoped Manifold ContDiff

section Null

theorem addHaar_image_eq_zero_of_finrank_lt {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (h : finrank ℝ E < finrank ℝ F) {s : Set E} {f : E → F} (hf : DifferentiableOn ℝ f s) :
    μ (f '' s) = 0 := by
  obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.1 h.le
  obtain ⟨L, hL⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  have hsurj : Function.Surjective L := fun x => ⟨i x, DFunLike.congr_fun hL x⟩
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt h
  let L' : F →L[ℝ] E := LinearMap.toContinuousLinearMap L
  have him : f '' s = (f ∘ L') '' (L' ⁻¹' s) := by
    rw [image_comp, image_preimage_eq s (f := L') hsurj]
  rw [him]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (f' := fun x => (fderivWithin ℝ f s (L' x)).comp L') (fun x hx => ?_) (fun x _ => ?_)
  · exact (hf _ hx).hasFDerivWithinAt.comp x L'.hasFDerivWithinAt (mapsTo_preimage _ _)
  · refine LinearMap.det_eq_zero_iff_ker_ne_bot.2 fun h0 => hker (le_bot_iff.1 ?_)
    rw [← h0]
    intro v hv
    have : L' v = 0 := hv
    simp [this]

variable {d : ℕ}

theorem volume_image_eq_zero_of_finrank_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : finrank ℂ E < d) {s : Set E} {f : E → Fin d → ℂ}
    (hf : DifferentiableOn ℂ f s) : volume (f '' s) = 0 := by
  refine addHaar_image_eq_zero_of_finrank_lt volume ?_ (hf.restrictScalars ℝ)
  rw [finrank_real_of_complex, finrank_real_of_complex]
  simpa using h

end Null

section Algebra

universe u

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}

theorem faithfulSMul_and_isAlgebraic_of_etale (R S : Type*) [CommRing R] [IsDomain R] [CommRing S]
    [IsDomain S] [Algebra R S] [Algebra.Etale R S] :
    FaithfulSMul R S ∧ Algebra.IsAlgebraic R S := by
  haveI : FaithfulSMul R S := inferInstance
  exact ⟨this, isAlgebraic_of_quasiFiniteAt R S ⊥⟩

theorem trdeg_eq_of_etale [IsDomain A] (g : MvPolynomial (Fin d) K →ₐ[K] A) (hg : g.Etale) :
    Algebra.trdeg K A = d := by
  letI : Algebra (MvPolynomial (Fin d) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) A := hg
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨_, _⟩ := faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin d) K) A
  rw [trdeg_eq_of_isAlgebraic_top K (MvPolynomial (Fin d) K) A, MvPolynomial.trdeg_of_isDomain]
  simp

theorem ringKrullDim_eq_of_isStandardSmooth [IsDomain A]
    [Algebra.IsStandardSmoothOfRelativeDimension d K A] : ringKrullDim A = d := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial d K A
  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := A) d
  exact ringKrullDim_eq_of_trdeg_eq K A (trdeg_eq_of_etale g hg)

theorem exists_notMem_isStandardSmoothOfRelativeDimension [IsDomain A] [Algebra.FiniteType K A]
    (hd : ringKrullDim A = d) (P : Ideal A) [P.IsPrime] [Algebra.IsSmoothAt K P] :
    ∃ s ∉ P, Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by
  haveI : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  obtain ⟨s, hs, ι, σ, _, _, ⟨Q⟩⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K P
  refine ⟨s, hs, ?_⟩
  have hs0 : Submonoid.powers s ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors fun h => hs (h ▸ P.zero_mem)
  haveI : IsDomain (Localization.Away s) := IsLocalization.isDomain_localization hs0
  haveI H : Algebra.IsStandardSmoothOfRelativeDimension Q.dimension K (Localization.Away s) :=
    Q.isStandardSmoothOfRelativeDimension rfl
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
    Q.dimension K (Localization.Away s)
  have h1 := trdeg_eq_of_etale g hg
  haveI : FaithfulSMul A (Localization.Away s) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective _ hs0)
  haveI : Algebra.IsAlgebraic A (Localization.Away s) :=
    IsLocalization.isAlgebraic _ (Submonoid.powers s)
  rw [trdeg_eq_of_isAlgebraic_top K A (Localization.Away s)] at h1
  have h2 := ringKrullDim_eq_of_trdeg_eq K A h1
  rw [hd] at h2
  obtain rfl : d = Q.dimension := by exact_mod_cast h2
  exact H

theorem exists_ne_zero_isStandardSmoothOfRelativeDimension [PerfectField K] [IsDomain A]
    [Algebra.FiniteType K A] (hd : ringKrullDim A = d) :
    ∃ s : A, s ≠ 0 ∧ Algebra.IsStandardSmoothOfRelativeDimension d K (Localization.Away s) := by
  haveI : Algebra.IsSmoothAt K (⊥ : Ideal A) := by
    haveI : IsLocalization (⊥ : Ideal A).primeCompl (FractionRing A) := by
      rw [Ideal.primeCompl_bot]; infer_instance
    let e := (IsLocalization.algEquiv (⊥ : Ideal A).primeCompl (FractionRing A)
      (Localization.AtPrime (⊥ : Ideal A))).restrictScalars K
    haveI : Algebra.EssFiniteType K (FractionRing A) := .comp K A _
    haveI : Algebra.FormallySmooth K (FractionRing A) := Algebra.FormallySmooth.of_perfectField
    exact Algebra.FormallySmooth.of_equiv e
  simpa using exists_notMem_isStandardSmoothOfRelativeDimension (K := K) hd ⊥

end Algebra

variable {A : Type} [CommRing A] [Algebra ℂ A] {d : ℕ}

theorem volume_coords_image_zeroSet [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : @Algebra.IsAlgebraic _ A _ _ g.toRingHom.toAlgebra) {f : A} (hf : f ≠ 0) :
    volume (coords g '' {p : A →ₐ[ℂ] ℂ | p f = 0}) = 0 := by
  letI : Algebra (MvPolynomial (Fin d) ℂ) A := g.toRingHom.toAlgebra
  obtain ⟨r, hr, c, hc⟩ := (hg.isAlgebraic f).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hf)
  refine measure_mono_null ?_ (ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin d r hr)
  rintro _ ⟨p, hp, rfl⟩
  have h1 : eval (coords g p) r = p (g r) := aeval_coords g p r
  have h2 : g r = f * c := hc
  simp only [mem_compl_iff, mem_setOf_eq, not_not]
  rw [h1, h2, map_mul, hp, zero_mul]

theorem isOpenMap_coords [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A) (hg : g.Finite)
    (hinj : Function.Injective g) : IsOpenMap (coords g : (A →ₐ[ℂ] ℂ) → Fin d → ℂ) :=
  (mvPolynomialHomeomorph (R := ℂ) (C := ℂ) (σ := Fin d)).isOpenMap.comp (isOpenMap_comap g hg hinj)

theorem dense_compl_of_volume_coords_image [IsDomain A] (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] A)
    (hg : g.Finite) (hinj : Function.Injective g) {S : Set (A →ₐ[ℂ] ℂ)}
    (hS : volume (coords g '' S) = 0) : Dense Sᶜ := by
  have h1 : Dense (coords g '' S)ᶜ :=
    Measure.dense_of_ae (μ := volume) (measure_eq_zero_iff_ae_notMem.1 hS)
  refine (h1.preimage (isOpenMap_coords g hg hinj)).mono ?_
  intro p hp hpS
  exact hp ⟨p, hpS, rfl⟩

theorem dense_nonvanishing [IsDomain A] [Algebra.FiniteType ℂ A] {f : A} (hf : f ≠ 0) :
    Dense {p : A →ₐ[ℂ] ℂ | p f ≠ 0} := by
  obtain ⟨s, g, hinj, hg⟩ := exists_finite_inj_algHom_of_fg ℂ A
  refine dense_compl_of_volume_coords_image g hg hinj (volume_coords_image_zeroSet g ?_ hf)
  letI := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) ℂ) A := hg
  infer_instance

section Cover

variable {ι : Type*} [Countable ι] {E H M : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℂ (E i)] [∀ i, FiniteDimensional ℂ (E i)] [∀ i, TopologicalSpace (H i)]
  {I : ∀ i, ModelWithCorners ℂ (E i) (H i)} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace (H i) (M i)] [∀ i, IsManifold (I i) 1 (M i)] [∀ i, LindelofSpace (M i)]

end Cover

section Immersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set E} {φ : E → (A →ₐ[ℂ] ℂ)}

end Immersion

end GlobalTheory.AffinePoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueComapEqVanishingIdeal
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs

universe u

namespace GlobalTheory.GaloisDescent


set_option backward.isDefEq.respectTransparency false in
theorem ideal_le_comap_appLE {X Y : Scheme.{u}} (f : Y ⟶ X) {J : X.IdealSheafData}
    {I : Y.IdealSheafData} (h : J.comap f ≤ I) (U : X.affineOpens) (V : Y.affineOpens)
    (e : V.1 ≤ f ⁻¹ᵁ U.1) : J.ideal U ≤ (I.ideal V).comap (f.appLE U V e).hom := by
  intro x hx
  have h1 : (I.subschemeι ≫ f).app U x = 0 :=
    (I.subschemeι ≫ f).ideal_ker_le U (Scheme.IdealSheafData.le_map_iff_comap_le.2 h U hx)
  rw [Ideal.mem_comap, ← I.ker_subschemeι_app V, RingHom.mem_ker, Scheme.Hom.app_eq_appLE,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE,
    CommRingCat.comp_apply, h1, map_zero]

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}

include H

theorem isPushout_app {U : X.Opens} (hU : IsAffineOpen U) :
    IsPushout (baseRingHom p U) (CommRingCat.ofHom (algebraMap K L)) (π.app U)
      (baseRingHom q (π ⁻¹ᵁ U)) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [baseRingHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · simp [baseRingHom]


set_option backward.isDefEq.respectTransparency false in
theorem idealSheaf_comap_map_of_stable (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (a : G → (Y ⟶ Y)) (haπ : ∀ g, a g ≫ π = π)
    (haq : ∀ g, a g ≫ q = q ≫ Spec.map (CommRingCat.ofHom (s g)))
    (I : Y.IdealSheafData) (hI : ∀ g, I.comap (a g) ≤ I) : (I.map π).comap π = I := by
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : X.affineOpens => ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) ?_ fun U => ?_
  · change ⨆ U : X.affineOpens, π ⁻¹ᵁ U.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · let := (π.app U).hom.toAlgebra
    let := (baseRingHom p U).hom.toAlgebra
    let := (baseRingHom q (π ⁻¹ᵁ U)).hom.toAlgebra
    let := (baseRingHom (π ≫ p) (π ⁻¹ᵁ U)).hom.toAlgebra
    have : IsScalarTower K Γ(X, U) Γ(Y, π ⁻¹ᵁ U) :=
      .of_algebraMap_eq fun r ↦ (app_baseRingHom π p U r).symm
    have : IsScalarTower K L Γ(Y, π ⁻¹ᵁ U) :=
      .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap (R := .of K) (L := .of L) H _ r).symm
    have hpo : Algebra.IsPushout K Γ(X, U) L Γ(Y, π ⁻¹ᵁ U) :=
      CommRingCat.isPushout_iff_isPushout.mp (isPushout_app H U.2)
    have e : ∀ g, π ⁻¹ᵁ U.1 ≤ a g ⁻¹ᵁ (π ⁻¹ᵁ U.1) := fun g => by
      rw [← Scheme.Hom.comp_preimage, haπ]
    have h1 : ∀ g, π.app U ≫ (a g).appLE _ _ (e g) = π.app U := fun g => by
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, haπ]
    have h2 : ∀ g, baseRingHom q (π ⁻¹ᵁ U) ≫ (a g).appLE _ _ (e g) =
        CommRingCat.ofHom (s g) ≫ baseRingHom q (π ⁻¹ᵁ U) := fun g => by
      rw [← baseRingHom_comp_SpecMap, ← haq]
      simp only [baseRingHom, Category.assoc, Scheme.Hom.appLE_comp_appLE]
    have key := ideal_map_comap_of_stable hpo.symm.out s hs
      (fun g => ((a g).appLE _ _ (e g)).hom.toAddMonoidHom) (fun g l x => by
        have h3 := congr($(h1 g) x)
        have h4 := congr($(h2 g) l)
        change (a g).appLE _ _ (e g) (baseRingHom q (π ⁻¹ᵁ U) l * π.app U x) =
          baseRingHom q (π ⁻¹ᵁ U) (s g l) * π.app U x
        rw [map_mul]
        exact congrArg₂ (· * ·) h4 h3)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
      (fun g x hx => ideal_le_comap_appLE (a g) (hI g) ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩
        ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ (e g) hx)
    rw [← key, Ideal.map_le_iff_le_comap]
    intro x hx
    have h5 := ideal_le_comap_appLE π (le_refl ((I.map π).comap π)) U
      ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ le_rfl (x := x)
      (by rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]; exact hx)
    rw [← Scheme.Hom.app_eq_appLE] at h5
    exact h5

theorem idealSheaf_map_comap (J : X.IdealSheafData) : (J.comap π).map π = J := by
  have : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
    .of_isDominant _
  have h : IsSchemeTheoreticallyDominant (pullback.snd π J.subschemeι) :=
    .of_isPullback ((IsPullback.of_hasPullback π J.subschemeι).flip.paste_vert H).flip
  rw [Scheme.IdealSheafData.comap, Scheme.IdealSheafData.map_ker, pullback.condition,
    Scheme.Hom.ker_comp, h.ker_eq_bot, Scheme.IdealSheafData.map_bot,
    Scheme.IdealSheafData.ker_subschemeι]

theorem idealSheaf_comap_injective :
    Function.Injective fun J : X.IdealSheafData => J.comap π := fun J J' h => by
  rw [← idealSheaf_map_comap H J, ← idealSheaf_map_comap H J']
  exact congrArg (·.map π) h

noncomputable def twist (σ : L →ₐ[K] L) : Y ⟶ Y :=
  H.lift π (q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    rw [H.w, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact σ.comp_algebraMap.symm)

@[reassoc (attr := simp)]
theorem twist_fst (σ : L →ₐ[K] L) : twist H σ ≫ π = π := H.lift_fst _ _ _

theorem twist_snd (σ : L →ₐ[K] L) :
    twist H σ ≫ q = q ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := H.lift_snd _ _ _

theorem idealSheaf_stable_iff_exists_comap (s : G → L →ₐ[K] L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L)) (I : Y.IdealSheafData) :
    (∀ g, I.comap (twist H (s g)) ≤ I) ↔ ∃! J : X.IdealSheafData, J.comap π = I := by
  constructor
  · intro hI
    have h1 := idealSheaf_comap_map_of_stable H (fun g => (s g).toRingHom) hs
      (fun g => twist H (s g)) (fun g => twist_fst H _) (fun g => twist_snd H _) I hI
    exact ⟨_, h1, fun J hJ => idealSheaf_comap_injective H (hJ.trans h1.symm)⟩
  · rintro ⟨J, rfl, -⟩ g
    rw [← Scheme.IdealSheafData.comap_comp, twist_fst]

end GlobalTheory.GaloisDescent
end

