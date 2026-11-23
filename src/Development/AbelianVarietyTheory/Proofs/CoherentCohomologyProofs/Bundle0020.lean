module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyHomLocSingletonEquivQuotSMulTop
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNoetherianSubringHomogeneousMatrixFlatChar
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyZeroEquivSections
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem cechLB_homology_zero_equiv_sections :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y)
      (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), ⨆ i, D i = ⊤ →
      Nonempty ((cechLB f M D).homology 0 ≃ₗ[R] SecOnR f M ⊤) := by
  intro R _ Y f M κ _ _ D hc
  exact ⟨((CochainComplex.isoHomologyπ₀ _).symm ≪≫
      cochainCyclesIsoKer (cechLB f M D) 0 ((cechLB f M D).d 0 1).hom rfl).toLinearEquiv ≪≫ₗ
    (CechOne.kerEquiv M f (fun _ => le_top) hc.ge).symm⟩

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.DehomogenisingCompOfSaturating
section
open CategoryTheory CategoryTheory.Limits DirectSum TensorProduct

noncomputable section

namespace GlobalTheory

theorem dehomogenising_comp_of_saturating {ι : Type} [LinearOrder ι] [Fintype ι] {R : Type}
    [CommRing R] {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N] (𝒩 : ℤ → Submodule R N) [PolyGradedSMul ι 𝒩]
    [Decomposition 𝒩] {G : Type} [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    (𝒢 : ℤ → Submodule R G) {ψ : N →ₗ[MvPolynomial ι R] G} (hψ : IsGradedMap 𝒩 𝒢 ψ) (i : ι)
    (h₁ : ∀ y, ψ y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0)
    (h₂ : ∀ z : G, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ)
    {B : Type} [CommRing B] (π : MvPolynomial ι R →+* B) {P : Type} [AddCommGroup P] [Module B P]
    (ε : G →ₛₗ[π] P) (hπ : π (MvPolynomial.X i) = 1) (hε : Function.Surjective ε)
    (hk : ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 → ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    Function.Surjective (ε.comp ψ) ∧
      ∀ y, ε.comp ψ y = 0 ↔ ∃ w : N, y = (MvPolynomial.X i - 1 : MvPolynomial ι R) • w := by
  refine ⟨fun p => ?_, dehomogenising_eq_zero_iff ι R N 𝒩 i B π P (ε.comp ψ) hπ ?_⟩
  · obtain ⟨z, rfl⟩ := hε p
    obtain ⟨k, y, hy⟩ := h₂ z
    refine ⟨y, ?_⟩
    rw [LinearMap.comp_apply, hy, LinearMap.map_smulₛₗ, map_pow, hπ, one_pow, one_smul]
  · intro n y hy h
    obtain ⟨k, hk⟩ := hk n _ (hψ hy) h
    obtain ⟨j, hj⟩ := h₁ _ ((map_smul ψ _ y).trans hk)
    exact ⟨j + k, by rw [pow_add, mul_smul, hj]⟩

theorem exists_noetherian_model_grCube (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢]
    (H : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P)
      (ε : G →ₛₗ[(π : MvPolynomial ι R →+* B)] P),
      Algebra.Smooth R B ∧ Module.FinitePresentation B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (MvPolynomial.X i) = 1 ∧ Function.Surjective ε ∧
        ∀ n, ∀ y ∈ 𝒢 n, ε y = 0 →
          ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι R) ^ k • y = 0) :
    ∃ (R₀ : Subring R) (_ : IsNoetherianRing R₀) (C₀ : Cube.{0} ι R₀)
      (θ : Cube.baseChange R C₀ ⟶ grCube ι 𝒢 0),
      (∀ I : Finset ι, I.Nonempty → Module.Flat R₀ (C₀.obj I)) ∧
        (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) ∧
        ∀ I : Finset ι, I.Nonempty → Function.Bijective (θ.app I).hom := by
  obtain ⟨a, b, d, e, Φ, ψ, hΦ, hψ, hsat⟩ :=
    exists_graded_presentation_saturating ι R G 𝒢 fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, hfp, -, h⟩ := H i
      exact (finite_quotSMulTop_X_sub_one_of_chart ι R G 𝒢 i B iB iA π P iP iM ε h).2
        inferInstance hfp
  let := grQuotDecomposition (grFree ι R d) (isHomogeneous_range_mulVecLin ι R a b d e Φ hΦ)
  obtain ⟨R₀, Φ₀, hN, hmap, hΦ₀, hflat⟩ :=
    exists_noetherian_subring_homogeneous_matrix_flat_charts ι R a b d e Φ hΦ fun i => by
      obtain ⟨B, iB, iA, π, P, iP, iM, ε, hs, -, hp, hπs, hπ, hε, hk⟩ := H i
      obtain ⟨k₁, k₂⟩ := dehomogenising_comp_of_saturating
        (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) 𝒢 hψ i (hsat i).1 (hsat i).2
        (π : MvPolynomial ι R →+* B) ε hπ hε hk
      refine ⟨B, iB, iA, π, P, iP, iM, (ε.comp ψ).comp (LinearMap.range Φ.mulVecLin).mkQ, hs, hp,
        hπs, hπ, k₁.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
      rw [LinearMap.comp_apply, k₂]
      constructor
      · rintro ⟨w, hw⟩
        obtain ⟨w', rfl⟩ := Submodule.mkQ_surjective _ w
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hw
        obtain ⟨v, hv⟩ := hw
        exact ⟨v, w', by rw [← Matrix.mulVecLin_apply, hv, sub_add_cancel]⟩
      · rintro ⟨v, w', rfl⟩
        refine ⟨Submodule.mkQ _ w', ?_⟩
        rw [← map_smul, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
        exact ⟨v, by rw [Matrix.mulVecLin_apply, add_sub_cancel_right]⟩
  let := grQuotDecomposition (grFree ι R₀ d)
    (isHomogeneous_range_mulVecLin ι R₀ a b d e Φ₀ hΦ₀)
  obtain ⟨ψ₀, hbc, hψ₀⟩ := isBaseChange_coker_matrix_mvPolynomial ι R₀ R a b Φ₀ Φ hmap
  obtain ⟨iso⟩ := nonempty_baseChange_grCube_iso ι R₀ R _
    (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) _
    (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) ψ₀ 0 hbc
    (fun i y => by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← Submodule.Quotient.mk_smul, hψ₀, hψ₀, ← Submodule.Quotient.mk_smul]
      congr 1
      ext1 l
      simp)
    (by
      rintro j _ ⟨y, hy, rfl⟩
      refine mem_grQuot.2 ⟨_, mem_grPi.2 fun l => ?_, (hψ₀ y).symm⟩
      have := mem_polyGrading_iff.1 (mem_grPi.1 hy l)
      refine mem_polyGrading_iff.2 fun c hc => this c fun h0 => hc ?_
      rw [MvPolynomial.coeff_map, h0, map_zero])
  refine ⟨R₀, hN, grCube ι (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) 0,
    iso.hom ≫ grCubeMap hψ 0, ?_, ?_, ?_⟩
  · rintro I ⟨i, hi⟩
    obtain ⟨f⟩ := nonempty_homLoc_singleton_equiv_quotSMulTop ι R₀ _
      (grQuot (grFree ι R₀ d) (LinearMap.range Φ₀.mulVecLin)) i
    have := hflat i
    exact flat_homLoc_of_flat_homLoc_singleton ι R₀ _ _ i I 0 hi (Module.Flat.of_linearEquiv f)
  · exact finite_grCech_homology ι R₀ _ _ inferInstance 0
  · rintro I ⟨i, hi⟩
    rw [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.coe_comp]
    exact (homLocMap_bijective_of_X hψ hi (hsat i).1 (hsat i).2 0).comp
      (ConcreteCategory.bijective_of_isIso (iso.hom.app I))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactCechOneOfH1Zero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.Cohom

theorem exact_cech_one_of_h1Zero :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → ⨆ i, D i = ⊤ → FirstCohomologyVanishes M → Function.Exact (Cube.d (secCube f M D) 1) (Cube.d (secCube f M D) 2) :=
  fun _ _ _ f M _ _ _ D hM hc h =>
    (cechComplex_exactAt_succ_iff (secCube f M D) 0).1 (CechOne.exactAt_one_of_h1Zero f hM hc h)

end GlobalTheory.Cohom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNonzeroLocusEqAffineOpenLocallyFactorial
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AffineComplement

open ReciprocityTheory.AnForm.R

theorem effCartier_of_stalkId_of_isLocallyNoetherian {W : Scheme.{0}} [IsLocallyNoetherian W]
    (G : W.IdealSheafData)
    (hG : ∀ x : W, ∃ t ∈ nonZeroDivisors (W.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}) :
    FinalTheorems.EffCartier G := by
  intro x
  obtain ⟨t, htnzd, ht⟩ := hG x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : W.affineOpens := ⟨U, hU⟩
  have hx : x ∈ U'.1 := hxU
  rw [ds_stalkId_eq_map G U' x hx] at ht
  haveI : IsNoetherianRing Γ(W, U) := IsLocallyNoetherian.component_noetherian U'
  letI : Algebra Γ(W, U) (W.presheaf.stalk x) := W.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  have halg : algebraMap Γ(W, U) (W.presheaf.stalk x) = (W.presheaf.germ U x hx).hom := rfl
  rw [Ideal.map] at ht
  obtain ⟨y, ⟨a, haI, rfl⟩, c, hc⟩ := ds_gen_of_span _ t htnzd ht
  have hmap : (G.ideal U').map (algebraMap Γ(W, U) (W.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(W, U) (W.presheaf.stalk x) a} := by
    rw [halg, Ideal.map, ht, hc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(W, U) (W.presheaf.stalk x) a ∈ nonZeroDivisors (W.presheaf.stalk x) := by
    rw [halg, hc]
    exact mul_mem (IsUnit.mem_nonZeroDivisors c.isUnit) htnzd
  obtain ⟨σ, hσP, hT⟩ := ds_spread (hU.primeIdealOf ⟨x, hx⟩).asIdeal (G.ideal U') a haI hmap hnzd
  haveI := hU.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(W, W.basicOpen σ)
  refine ⟨W.affineBasicOpen (U := U') σ, algebraMap Γ(W, U) Γ(W, W.basicOpen σ) a, ?_, h2, ?_⟩
  · show x ∈ W.basicOpen σ
    rw [W.mem_basicOpen σ x hx]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal σ).2 hσP
  · rw [← G.map_ideal_basicOpen U' σ]
    exact h1

theorem exists_radical_span_singleton_eq {A : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] {a : A} (ha : a ≠ 0) :
    ∃ t ∈ nonZeroDivisors A, (Ideal.span {a}).radical = Ideal.span {t} := by
  obtain ⟨y, n, hy, hya, hay⟩ := exists_squarefree_dvd_pow_of_ne_zero ha
  refine ⟨y, mem_nonZeroDivisors_of_ne_zero hy.ne_zero, le_antisymm ?_ ?_⟩
  · rw [← (isRadical_iff_span_singleton.1 hy.isRadical).radical]
    exact Ideal.radical_mono (Ideal.span_singleton_le_span_singleton.2 hya)
  · rw [Ideal.span_singleton_le_iff_mem]
    exact ⟨n, Ideal.mem_span_singleton.2 hay⟩

theorem stalkId_vanishingIdeal_compl {X : Scheme.{0}} (U : X.Opens) (x : X)
    (a : X.presheaf.stalk x)
    (h : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal U.compl) x = (Ideal.span {a}).radical := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ x hx, Scheme.IdealSheafData.vanishingIdeal_ideal]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hW.isLocalization_stalk ⟨x, hx⟩
  have hcl : IsClosed (X := PrimeSpectrum Γ(X, W)) (hW.fromSpec ⁻¹' (U.compl : Set X)) :=
    U.compl.isClosed.preimage hW.fromSpec.continuous
  generalize hJ : PrimeSpectrum.vanishingIdeal (R := Γ(X, W)) (hW.fromSpec ⁻¹' (U.compl : Set X)) = J
  have hz : PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = hW.fromSpec ⁻¹' (U.compl : Set X) := by
    rw [← hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hcl.closure_eq]
    rfl
  have hr : J.radical = J := hJ ▸ (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  change J.map (algebraMap Γ(X, W) (X.presheaf.stalk x)) = _
  rw [← hr, IsLocalization.map_radical (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
    ← PrimeSpectrum.zeroLocus_eq_iff]
  ext q
  have e : X.fromSpecStalk x q =
      hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q) := by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rw [PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem,
    ← not_iff_not, ← h, e]
  have := Set.ext_iff.1 hz (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q)
  exact (not_congr this).trans not_not

theorem exists_nonzeroLocus_eq : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (U : X.Opens), IsAffineOpen U → (U : Set X).Nonempty → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∃ (L : LB X) (σ : LB.Sec L), L.IsLB ∧ nonzeroLocus σ = U := by
  intro X _ _ _ U hU hne hufd
  have hι : IsAffineHom U.ι :=
    haveI : IsAffine U := hU
    haveI : IsAffineHom (U.ι ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  have hE : FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal U.compl) := by
    refine effCartier_of_stalkId_of_isLocallyNoetherian _ fun x => ?_
    haveI := hufd x
    have hd : IsDomain (X.presheaf.stalk x) := inferInstance
    have hn : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    have hA : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ U) := by
      have : IsAffineHom (X.fromSpecStalk x ⁻¹ᵁ U).ι :=
        MorphismProperty.of_isPullback (P := @IsAffineHom)
          (isPullback_morphismRestrict (X.fromSpecStalk x) U) hι
      exact isAffine_of_isAffineHom (X.fromSpecStalk x ⁻¹ᵁ U).ι
    have hg : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨q, hq⟩ := hg
    have hqU : q ∈ X.fromSpecStalk x ⁻¹ᵁ U := by
      change X.fromSpecStalk x q ∈ U
      rw [hq]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)
    obtain ⟨a, ha⟩ := @GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization (X.presheaf.stalk x) (X.presheaf.stalk x).commRing hd hn (hufd x)
      (X.fromSpecStalk x ⁻¹ᵁ U) hA ⟨q, hqU⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal := fun q =>
      iff_of_eq (congrArg (fun V => q ∈ V) ha)
    have ha0 : a ≠ 0 := fun h0 => (h q).1 hqU (h0 ▸ zero_mem _)
    rw [stalkId_vanishingIdeal_compl U x a h]
    exact exists_radical_span_singleton_eq ha0
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hE
  refine ⟨D.lb, D.canonical, D.isLB_lb, TopologicalSpace.Opens.ext ?_⟩
  refine D.coe_nonzeroLocus_canonical.trans ?_
  rw [hD]
  exact compl_compl _

end GlobalTheory.AffineComplement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FirstCohomologyVanishesOfExactSecCube
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem firstCohomologyVanishes_of_exact_secCube (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ]
    (D : κ → Y.Opens) (hM : M.IsLB) (hc : ⨆ i, D i = ⊤) (hA : ∀ i, IsAffineOpen (D i))
    (h : Function.Exact (Cube.d (secCube f M D) 1) (Cube.d (secCube f M D) 2)) : FirstCohomologyVanishes M :=
  CechOne.h1Zero_of_exactAt_one f hM hc hA
    ((cechComplex_exactAt_succ_iff (secCube f M D) 0).2 h)

end GlobalTheory.AbLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnFinitePresentationProjective
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

variable {Y : Scheme.{0}} {M : LB Y} {V : Y.Opens}

noncomputable def SecOn.chartBasicOpen (hM : M.IsLB) (i : M.ι) (a : Γ(Y, V))
    (h : Y.basicOpen a ≤ M.U i) : SecOn M V →ₗ[Γ(Y, V)] Γ(Y, Y.basicOpen a) where
  toFun s := SecOn.chart hM i h (SecOn.restrict M (Y.basicOpen_le a) s)
  map_add' s t := by rw [map_add (f := _), map_add (f := _)]
  map_smul' r s := by
    rw [map_smulₛₗ, map_smul, RingHom.id_apply, Algebra.smul_def r]
    rfl

theorem SecOn.isLocalizedModule_chartBasicOpen (hM : M.IsLB) (hV : IsAffineOpen V) (i : M.ι)
    (a : Γ(Y, V)) (h : Y.basicOpen a ≤ M.U i) :
    IsLocalizedModule (Submonoid.powers a) (SecOn.chartBasicOpen hM i a h) := by
  have := hV.isLocalization_basicOpen a
  obtain ⟨h₁, h₂⟩ := secOn_basicOpen_localization Y M V _ a (Y.basicOpen_le a) hM hV.isCompact
    hV.isQuasiSeparated rfl
  refine ⟨fun x => IsLocalizedModule.map_units
    (Algebra.linearMap Γ(Y, V) Γ(Y, Y.basicOpen a)) x, fun y => ?_, fun {x₁ x₂} e => ?_⟩
  · obtain ⟨k, x, e⟩ := h₂ ((SecOn.chart hM i h).symm y)
    refine ⟨⟨x, ⟨a ^ k, k, rfl⟩⟩, ?_⟩
    change a ^ k • y = SecOn.chart hM i h (SecOn.restrict M (Y.basicOpen_le a) x)
    rw [e, map_smul, LinearEquiv.apply_symm_apply, Algebra.smul_def, map_pow]
    rfl
  · obtain ⟨k, hk⟩ := h₁ (x₁ - x₂) (by
      rw [map_sub, sub_eq_zero]
      exact (SecOn.chart hM i h).injective e)
    refine ⟨⟨a ^ k, k, rfl⟩, ?_⟩
    change a ^ k • x₁ = a ^ k • x₂
    rwa [smul_sub, sub_eq_zero] at hk

theorem secOn_finitePresentation_projective :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V : Y.Opens), M.IsLB → IsAffineOpen V → Module.FinitePresentation Γ(Y, V) (SecOn M V) ∧ Module.Projective Γ(Y, V) (SecOn M V) := by
  intro Y M V hM hV
  let s : Set Γ(Y, V) := {a | ∃ i, Y.basicOpen a ≤ M.U i}
  have hs : Ideal.span s = ⊤ := by
    rw [← hV.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (Set.mem_univ x))
    obtain ⟨f, hf, hxf⟩ := hV.exists_basicOpen_le ⟨x, hi⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, i, hf⟩, hxf⟩
  choose c hc using fun g : s => g.2
  have hl (g : s) := hV.isLocalization_basicOpen g.1
  have hm (g : s) := SecOn.isLocalizedModule_chartBasicOpen hM hV (c g) g.1 (hc g)
  have hfp : Module.FinitePresentation Γ(Y, V) (SecOn M V) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Rₚ := fun g => Γ(Y, Y.basicOpen g.1))
      (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g)) fun _ => inferInstance
  have hfl : Module.Flat Γ(Y, V) (SecOn M V) :=
    Module.flat_of_isLocalized_span Γ(Y, V) (SecOn M V) s hs (fun g => Γ(Y, Y.basicOpen g.1))
      (fun g => SecOn.chartBasicOpen hM (c g) g.1 (hc g))
      fun g => IsLocalization.flat _ (Submonoid.powers g.1)
  exact ⟨hfp, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.AbLaw
end

