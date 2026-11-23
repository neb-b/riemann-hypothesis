module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PLengthQuotientDet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Module

theorem LengthQuotientDet.ord_prod {O : Type} [CommRing O] [IsDomain O] {ι : Type*} (s : Finset ι)
    (a : ι → O) (ha : ∀ i, a i ≠ 0) : Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha j)), ih]

theorem LengthQuotientDet.proof : LengthQuotientDet.Statement := by
  intro O _ _ _ M _ _ _ _ φ hdet
  classical
  have hinj : Function.Injective φ :=
    LinearMap.ker_eq_bot.mp (not_not.mp (mt LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hdet))
  set ι := Module.Free.ChooseBasisIndex O M
  let b := Module.Free.chooseBasis O M
  have hrank : finrank O (LinearMap.range φ) = finrank O M := LinearMap.finrank_range_of_inj hinj
  set a := Submodule.smithNormalFormCoeffs b hrank
  let b' := Submodule.smithNormalFormTopBasis b hrank
  let ab := Submodule.smithNormalFormBotBasis b hrank
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank

  have hlen : Module.length O (M ⧸ LinearMap.range φ) = ∑ i, Ring.ord O (a i) := by
    rw [(Submodule.quotientEquivPiSpan (LinearMap.range φ) b hrank).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let v : Basis ι O M := ab.map (LinearEquiv.ofInjective φ hinj).symm
  have hv : ∀ i, φ (v i) = a i • b' i := by
    intro i
    have h1 : φ (v i) = ((LinearEquiv.ofInjective φ hinj) (v i) : M) :=
      (LinearEquiv.ofInjective_apply _ _).symm
    rw [h1]
    simp only [v, Basis.map_apply, LinearEquiv.apply_symm_apply]
    exact Submodule.smithNormalFormBotBasis_def b hrank i
  have hdetprod : LinearMap.det φ * b'.det v = ∏ i, a i := by
    rw [← Basis.det_comp]
    have : (⇑φ ∘ ⇑v) = fun i => a i • b' i := funext hv
    rw [this, AlternatingMap.map_smul_univ, Basis.det_self, smul_eq_mul, mul_one]
  have hassoc : Associated (LinearMap.det φ) (∏ i, a i) := by
    obtain ⟨u, hu⟩ := b'.isUnit_det v
    exact ⟨u, by rw [hu]; exact hdetprod⟩
  rw [hlen, Ring.ord_eq_of_associated hassoc, LengthQuotientDet.ord_prod _ _ ha]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PLocalMultOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

theorem LocalMultOrd.proof : LocalMultOrd.Statement := by
  intro A _ _ I W x _ hW
  set J := I ⊔ Ideal.span {x} with hJ
  have hWp : W.IsPrime := hW.1.1
  have hIW : I ≤ W := le_sup_left.trans hW.1.2
  have hxJ : x ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  set P := W.map (Ideal.Quotient.mk I) with hPdef
  have hcomap : W = P.comap (Ideal.Quotient.mk I) := by
    rw [hPdef, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr hIW]
  have hcompl : ∀ a : A, a ∉ W → Ideal.Quotient.mk I a ∈ P.primeCompl := fun a ha h =>
    ha (hcomap ▸ h)
  let AW := Localization.AtPrime W
  let BP := Localization.AtPrime P
  let φ : AW →+* BP := Localization.localRingHom W P (Ideal.Quotient.mk I) hcomap
  set x' : BP := algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I x) with hx'
  let C := BP ⧸ Ideal.span {x'}
  let π : AW →+* C := (Ideal.Quotient.mk _).comp φ
  have hφ : ∀ a : A, φ (algebraMap A AW a) = algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I a) :=
    fun a => Localization.localRingHom_to_map _ _ _ _ _
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
    have htW : t ∈ W.primeCompl := fun h => s.2 (ht ▸ Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' AW a ⟨t, htW⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext ht
  have hπs : Function.Surjective π := Ideal.Quotient.mk_surjective.comp hφs

  have hmax : ∀ Q ∈ (Ideal.span {x'}).minimalPrimes, Q.IsMaximal := by
    intro Q hQ
    have := hQ.1.1
    have hle : W ≤ (Q.comap (algebraMap (A ⧸ I) BP)).comap (Ideal.Quotient.mk I) := by
      refine hW.2 ⟨Ideal.comap_isPrime _ _, sup_le ?_ ?_⟩ ?_
      · intro a ha
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hQ.1.2 (Ideal.mem_span_singleton_self _)
      · intro a ha
        by_contra haW
        exact hQ.1.1.ne_top (Ideal.eq_top_of_isUnit_mem _ ha
          (IsLocalization.map_units BP (⟨_, hcompl a haW⟩ : P.primeCompl)))
    have hm : IsLocalRing.maximalIdeal BP ≤ Q := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro b hb
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact hle (by rw [hcomap]; exact hb)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hQ.1.1.ne_top) hm]
    infer_instance
  have : Ring.KrullDimLE 0 C :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr hmax
  have : IsArtinianRing C := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := C)
  have hfin : Module.length C C ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

  let : Algebra AW C := RingHom.toAlgebra (R := AW) (S := C) π
  have hJπ : ∀ y ∈ J.map (algebraMap A AW), (Algebra.ofId AW C) y = 0 := by
    have : J.map (algebraMap A AW) ≤ RingHom.ker π := by
      rw [Ideal.map_le_iff_le_comap]
      refine sup_le (fun a ha => ?_) ?_
      · simp [RingHom.mem_ker, π, hφ, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        simp [RingHom.mem_ker, π, hφ, ← hx']
    exact fun y hy => this hy
  let f : (AW ⧸ J.map (algebraMap A AW)) →ₐ[AW] C := Ideal.Quotient.liftₐ _ (Algebra.ofId AW C) hJπ
  have hf : ∀ y, f (Ideal.Quotient.mk _ y) = π y := fun y => rfl
  let ψ0 : A ⧸ I →+* AW ⧸ J.map (algebraMap A AW) :=
    Ideal.Quotient.lift I ((Ideal.Quotient.mk _).comp (algebraMap A AW)) (fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left ha)))
  have hunit : ∀ s : P.primeCompl, IsUnit (ψ0 s) := by
    intro s
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
    have htW : t ∈ W.primeCompl := fun h => s.2 (ht ▸ Ideal.mem_map_of_mem _ h)
    rw [← ht]
    exact (IsLocalization.map_units AW (⟨t, htW⟩ : W.primeCompl)).map (Ideal.Quotient.mk _)
  let ψ1 : BP →+* AW ⧸ J.map (algebraMap A AW) := IsLocalization.lift hunit
  have hψ1 : ∀ a : A, ψ1 (algebraMap (A ⧸ I) BP (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk _ (algebraMap A AW a) := fun a => by
    simp [ψ1, ψ0, IsLocalization.lift_eq]
  let ψ : C →+* AW ⧸ J.map (algebraMap A AW) := Ideal.Quotient.lift _ ψ1 (by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [map_mul, hx', hψ1, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hxJ), mul_zero])
  have hψπ : ψ.comp π = Ideal.Quotient.mk _ := by
    apply IsLocalization.ringHom_ext W.primeCompl
    ext a
    change ψ (Ideal.Quotient.mk _ (φ (algebraMap A AW a))) =
      Ideal.Quotient.mk _ (algebraMap A AW a)
    rw [hφ]
    exact hψ1 a
  have hinj : Function.Injective f := by
    intro q₁ q₂ h
    obtain ⟨y₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
    obtain ⟨y₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
    rw [hf, hf] at h
    have e₁ : ψ (π y₁) = _ := RingHom.congr_fun hψπ y₁
    have e₂ : ψ (π y₂) = _ := RingHom.congr_fun hψπ y₂
    exact e₁.symm.trans ((congrArg ψ h).trans e₂)
  have hsurj : Function.Surjective f := fun c => by
    obtain ⟨y, rfl⟩ := hπs c
    exact ⟨_, hf y⟩
  let e := LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hsurj⟩
  have hord : Ring.ord BP x' = Module.length C C :=
    Module.length_eq_of_surjective (S := BP) (R := C) (M := C) Ideal.Quotient.mk_surjective
  have hlen : Module.length AW (AW ⧸ J.map (algebraMap A AW)) = Module.length C C := by
    rw [e.length_eq]
    exact Module.length_eq_of_surjective (S := AW) (R := C) (M := C) hπs
  have hloc : localMult J W = (Module.length AW (AW ⧸ J.map (algebraMap A AW))).toNat := by
    unfold localMult
    rw [dite_eq_left hWp]
  rw [hloc, hlen, hord]
  exact ENat.natCast_toNat hfin

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PMinimalPrimeHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isHomogIdeal_iff_isHomogeneous_degree {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    convert h r hr i using 1
    exact decomposition.decompose'_apply r i
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

theorem MinimalPrimeHomog.proof : MinimalPrimeHomog.Statement := by
  intro F _ n J W hJ hW
  rw [isHomogIdeal_iff_isHomogeneous_degree] at hJ ⊢
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal = W := by
    apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    refine hW.2 ⟨hWp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    exact hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  rw [← hcore]
  exact (W.homogeneousCore _).isHomogeneous

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.POrdPolynomialLocalization
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

theorem OrdPolynomialLocalization.comap_C_map_C {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) :
    Ideal.comap (C : R →+* MvPolynomial σ R) (Ideal.map (C : R →+* MvPolynomial σ R) p) = p := by
  classical
  ext r
  rw [Ideal.mem_comap, MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h m
    rw [coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem

theorem OrdPolynomialLocalization.proof : OrdPolynomialLocalization.Statement := by
  intro R _ σ p _ _ x
  set P := Ideal.map (C : R →+* MvPolynomial σ R) p with hPdef
  have : P.LiesOver p := ⟨by
    rw [Ideal.under, MvPolynomial.algebraMap_eq, hPdef]
    exact (OrdPolynomialLocalization.comap_C_map_C σ p).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p P
  set A := Localization.AtPrime p
  set B := Localization.AtPrime P
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p P (algebraMap R (MvPolynomial σ R))
      Ideal.LiesOver.over))
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R (MvPolynomial σ R) B, ← Ideal.map_map, MvPolynomial.algebraMap_eq,
      ← hPdef, Localization.AtPrime.map_eq_maximalIdeal]
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have key := IsLocalRing.length_baseChange A B (A ⧸ Ideal.span {algebraMap R A x})
  rw [hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (Ideal.span {algebraMap R A x})).toLinearEquiv.length_eq, Ideal.map_span,
    Set.image_singleton, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R (MvPolynomial σ R) B, MvPolynomial.algebraMap_eq] at key
  exact key

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PProjNullstellensatz
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ProjNullstellensatz.proof (h₁ : FGNullstellensatz.Statement) :
    ProjNullstellensatz.Statement := by
  intro F _ n P hP
  have : P.IsPrime := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  set D := MvPolynomial (Fin n) F ⧸ P
  have hr : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  have hφ : ∃ φ : D →ₐ[F] AlgebraicClosure F, φ (Ideal.Quotient.mk P (X j)) ≠ 0 := by
    by_contra hne
    apply hr
    refine h₁ F D _ (fun φ => ?_)
    by_contra h
    exact hne ⟨φ, h⟩
  obtain ⟨φ, hφj⟩ := hφ
  have hcomp : φ.comp (Ideal.Quotient.mkₐ F P) = aeval (fun i => φ (Ideal.Quotient.mk P (X i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, aeval_X]
    rfl
  refine ⟨fun i => φ (Ideal.Quotient.mk P (X i)), ?_, ?_⟩
  · intro h0
    exact hφj (congrFun h0 j)
  · intro g hg
    rw [← hcomp, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]

end GroundTheory.Heights₂.Heights
end

