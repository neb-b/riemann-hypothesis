module

public import Development.EtaleCohomology.EtaleTrace.Bundle0010

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleTrace.ChartGenOnPfCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def ChartGenMem : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ((⟨genericPoint X, hη⟩ : U) ∈ chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) w f ≠ 0)

def ChartGenVal : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∀ (hη : genericPoint X ∈ U) (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : (⟨genericPoint X, hη⟩ : U) ∈ chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f),
      U.toScheme.presheaf.germ _ ⟨genericPoint X, hη⟩ h ((chartMor i U hx φ).app _
          (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg))) *
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from
          eval₂ (kHom p) w f) ^ m =
        (U.ι.stalkMap ⟨genericPoint X, hη⟩).hom (show X.presheaf.stalk (U.ι ⟨genericPoint X, hη⟩) from eval₂ (kHom p) w g)

theorem ChartGenOn_of (h1 : ChartGenMem) (h2 : ChartGenVal) : ChartGenOn := by
  intro k _ X _ p N w i hi U hx φ hφ hη n hn f hf
  exact ⟨h1 k p N w i hi U hx φ hφ hη n hn f hf, fun m g hg h => h2 k p N w i hi U hx φ hφ hη n hn f hf m g hg h⟩

theorem ChartGenMem_pf : ChartGenMem := by
  intro k _ X _ p N w i hi U hx φ hφ hη n hn f hf
  have e1 : chartMor i U hx φ = U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι _ (MvPolynomial.X i) hx zero_lt_one := by
    rw [chartMor, Scheme.Opens.toSpecΓ, Category.assoc, ← Spec.map_comp_assoc]; rfl
  have e2 : chartMor i U hx φ ⁻¹ᵁ Proj.basicOpen _ f =
      U.ι ⁻¹ᵁ X.basicOpen (φ (HomogeneousLocalization.Away.isLocalizationElem hx hf)) := by
    rw [e1, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
      Proj.awayι_preimage_basicOpen _ hx zero_lt_one hf hn, SpecMap_preimage_basicOpen,
      Scheme.Opens.toSpecΓ_preimage_basicOpen]
    rfl
  rw [e2]
  change genericPoint X ∈ X.basicOpen _ ↔ _
  rw [Scheme.mem_basicOpen _ _ _ hη]
  have h' : (@algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField CommRing.toCommSemiring _ (stalkFunctionFieldAlgebra X (genericPoint X)))
      (X.presheaf.germ U _ hη (φ (HomogeneousLocalization.Away.isLocalizationElem hx hf))) =
        eval₂ (kHom p) w f / w i ^ n := by
    have h := hφ (genericPoint X) hη n (f ^ 1) (by simpa using hf)
    exact h.trans (by rw [pow_one])
  rw [isUnit_iff_ne_zero, ← (@algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField CommRing.toCommSemiring _ (stalkFunctionFieldAlgebra X (genericPoint X))).injective.ne_iff,
    map_zero, h']
  simp [hi]

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.ChartOverKPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem sect_eq_of_alg (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (s t : Γ(X, U))
    (h : ∀ (y : X) (hy : y ∈ U), algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy s) =
      algebraMap (X.presheaf.stalk y) X.functionField (X.presheaf.germ U y hy t)) : s = t := by
  apply TopCat.Presheaf.section_ext X.sheaf
  intro y hy
  have : Nonempty U := ⟨⟨y, hy⟩⟩
  have hst : s = t := by
    apply Scheme.germToFunctionField_injective X U
    have := h y hy
    rwa [Scheme.algebraMap_germ_eq_germToFunctionField, Scheme.algebraMap_germ_eq_germToFunctionField] at this
  rw [hst]

theorem fromZero_eq_mk {k : Type} [Field k] {N : ℕ} (i : Fin (N + 1))
    (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1) (c : k)
    (hg : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k (0 • 1)) :
    HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (N + 1)) k) (Submonoid.powers (MvPolynomial.X i))
      (algebraMap k (homogeneousSubmodule (Fin (N + 1)) k 0) c) = HomogeneousLocalization.Away.mk _ hx 0 (C c) hg := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.fromZeroRingHom]
  rfl

theorem chart_key {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)) (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U))
  (hφ : ∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) :
  (CommRingCat.ofHom (algebraMap k (homogeneousSubmodule (Fin (N + 1)) k 0)) ≫
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule (Fin (N + 1)) k)
        (Submonoid.powers (MvPolynomial.X i)))) ≫ CommRingCat.ofHom ((U.topIso.inv.hom).comp φ) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.ι ≫ p).appTop := by
  ext c
  have hg : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k (0 • 1) :=
    (mem_homogeneousSubmodule _ _).2 (by simpa using isHomogeneous_C (Fin (N + 1)) c)
  have hsec : φ (HomogeneousLocalization.Away.mk _ hx 0 (C c) hg) =
      X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) := by
    apply sect_eq_of_alg X
    intro y hy
    rw [hφ, TopCat.Presheaf.germ_res_apply]
    have : Nonempty (⊤ : X.Opens) := ⟨⟨y, trivial⟩⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    simp [kHom]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
  rw [fromZero_eq_mk i hx c hg, hsec]
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, CommRingCat.hom_comp,
    RingHom.comp_apply]
  erw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem ChartOverK_of : ChartOverK := by
  intro k _ X _ p N w i hi U hx φ hφ
  have hR : U.ι ≫ p = U.toScheme.toSpecΓ ≫ Spec.map ((U.ι ≫ p).appTop) ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have key := chart_key p N w i U hx φ hφ
  rw [hR]
  unfold chartMor PNto
  simp only [Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp, ← key]
  simp only [Spec.map_comp, Category.assoc]
  rfl

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenEtaleAtBotPf
section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf

theorem formallyEtale_of_fraction {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    [Algebra.FormallyUnramified A K] : Algebra.FormallyEtale A K := by
  have hAK : Function.Injective (algebraMap A K) := by
    rw [IsScalarTower.algebraMap_eq A B K]
    exact (IsFractionRing.injective B K).comp hinj
  have : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).mpr hAK
  let := FractionRing.liftAlgebra A K
  have : Algebra.FormallyUnramified (FractionRing A) K :=
    Algebra.FormallyUnramified.of_restrictScalars A _ _
  have : Algebra.EssFiniteType B K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors B)
  have : Algebra.EssFiniteType A K := Algebra.EssFiniteType.comp A B K
  have : Algebra.EssFiniteType (FractionRing A) K := Algebra.EssFiniteType.of_comp A _ _
  have : Algebra.FormallyEtale (FractionRing A) K := Algebra.FormallyEtale.of_formallyUnramified_of_field _ _
  have : Algebra.FormallyEtale A (FractionRing A) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  exact Algebra.FormallyEtale.comp A (FractionRing A) K

theorem isEtaleAt_bot {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [Module.Finite A B] (hinj : Function.Injective (algebraMap A B))
    [Field K] [Algebra B K] [IsFractionRing B K] [Algebra A K] [IsScalarTower A B K]
    [Algebra.FormallyUnramified A K] :
    ∃ _ : (⊥ : Ideal B).IsPrime, Algebra.IsEtaleAt A (⊥ : Ideal B) := by
  refine ⟨Ideal.isPrime_bot, ?_⟩
  have := formallyEtale_of_fraction (A := A) (B := B) (K := K) hinj
  have : IsLocalization (nonZeroDivisors B) (Localization.AtPrime (⊥ : Ideal B)) := by
    rw [← Ideal.primeCompl_bot]; infer_instance
  let φ : K ≃ₐ[B] Localization.AtPrime (⊥ : Ideal B) :=
    IsLocalization.algEquiv (nonZeroDivisors B) _ _
  exact Algebra.FormallyEtale.of_equiv (φ.restrictScalars A)

theorem genEtaleAtBot : GenEtaleAtBot := by
  intro X P _ _ π U hU hne hU' hfin hinj hun
  haveI : Nonempty U := hne.to_subtype
  have hV : Nonempty (π ⁻¹ᵁ U) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hb : π ⁻¹ᵁ U = ⊥ := SetLike.ext' (Set.isEmpty_coe_sort.mp h)
    have : Subsingleton Γ(X, π ⁻¹ᵁ U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hb)
    exact not_subsingleton Γ(P, U) ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
  let _ := (π.app U).hom.toAlgebra
  have hfin' : Module.Finite Γ(P, U) Γ(X, π ⁻¹ᵁ U) := hfin
  have hη : genericPoint X ∈ π ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (π ⁻¹ᵁ U).isOpen).mpr (by simpa using hV)
  have hx : π (genericPoint X) ∈ U := hη
  let alS := P.presheaf.algebra_section_stalk ⟨π (genericPoint X), hx⟩
  have hloc := hU.isLocalization_stalk ⟨π (genericPoint X), hx⟩
  have h1 : (P.presheaf.germ U (π (genericPoint X)) hx).hom.FormallyUnramified := by
    have := Algebra.FormallyUnramified.of_isLocalization (Rₘ := P.presheaf.stalk (π (genericPoint X)))
      (hU.primeIdealOf ⟨π (genericPoint X), hx⟩).asIdeal.primeCompl
    exact RingHom.formallyUnramified_algebraMap.mpr this
  have h2 := h1.comp hun
  rw [← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap] at h2
  let algK : Algebra Γ(P, U) X.functionField := (π.app U ≫ X.presheaf.germ _ _ hη).hom.toAlgebra
  haveI : IsScalarTower Γ(P, U) Γ(X, π ⁻¹ᵁ U) X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.FormallyUnramified Γ(P, U) X.functionField := h2
  have := functionField_isFractionRing_of_isAffineOpen X (π ⁻¹ᵁ U) hU'
  exact isEtaleAt_bot (K := X.functionField) hinj

theorem GenEtaleAtBot_of : GenEtaleAtBot := genEtaleAtBot

end LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf
end

