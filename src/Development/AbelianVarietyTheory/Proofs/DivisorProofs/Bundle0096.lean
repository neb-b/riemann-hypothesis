module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceFibreHypersurfaceSpectrumIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.FibreHyp

section defs
variable {A : Type} [CommRing A] {σ : Type} (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k]

abbrev Ik : Ideal (MvPolynomial σ k) := Ideal.span {MvPolynomial.map (algebraMap A k) f}

abbrev Lk := Localization.Away (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))

abbrev LA := Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g)

def rhoK : MvPolynomial σ k →ₐ[k] Lk f g k :=
  (IsScalarTower.toAlgHom k (MvPolynomial σ k ⧸ Ik f k) (Lk f g k)).comp (Ideal.Quotient.mkₐ k (Ik f k))

def rhoA : MvPolynomial σ A →ₐ[A] LA f g :=
  (IsScalarTower.toAlgHom A (MvPolynomial σ A ⧸ Ideal.span {f}) (LA f g)).comp
    (Ideal.Quotient.mkₐ A (Ideal.span {f}))

lemma rhoK_apply (p : MvPolynomial σ k) :
    rhoK f g k p = algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k) (Ideal.Quotient.mk (Ik f k) p) := rfl

lemma rhoA_apply (p : MvPolynomial σ A) :
    rhoA f g p = algebraMap (MvPolynomial σ A ⧸ Ideal.span {f}) (LA f g) (Ideal.Quotient.mk _ p) := rfl

def fwd0 : MvPolynomial σ A →ₐ[A] Lk f g k :=
  MvPolynomial.aeval (fun i => rhoK f g k (MvPolynomial.X i))

lemma fibreHypersurfaceForwardPolynomial_apply (p : MvPolynomial σ A) :
    fwd0 f g k p = rhoK f g k (MvPolynomial.map (algebraMap A k) p) := by
  rw [fwd0, ← MvPolynomial.aeval_map_algebraMap k]
  conv_rhs => rw [MvPolynomial.aeval_unique (rhoK f g k)]
  rfl

def fwd1 : (MvPolynomial σ A ⧸ Ideal.span {f}) →ₐ[A] Lk f g k :=
  Ideal.Quotient.liftₐ (Ideal.span {f}) (fwd0 f g k) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, fibreHypersurfaceForwardPolynomial_apply f g k f]
    have : rhoK f g k (MvPolynomial.map (algebraMap A k) f) = 0 := by
      simp [rhoK, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
    rw [this, mul_zero])

lemma fibreHypersurfaceForwardQuotient_mk (p : MvPolynomial σ A) :
    fwd1 f g k (Ideal.Quotient.mk _ p) = rhoK f g k (MvPolynomial.map (algebraMap A k) p) := by
  rw [← fibreHypersurfaceForwardPolynomial_apply]; rfl

def fwd2 : LA f g →ₐ[A] Lk f g k :=
  IsLocalization.Away.liftAlgHom (S := LA f g) (Ideal.Quotient.mk (Ideal.span {f}) g) (f := fwd1 f g k) (by
    rw [fibreHypersurfaceForwardQuotient_mk, rhoK_apply]
    exact IsLocalization.Away.algebraMap_isUnit (S := Lk f g k)
      (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)))

def fwd : k ⊗[A] LA f g →ₐ[k] Lk f g k :=
  Algebra.TensorProduct.lift (Algebra.ofId k _) (fwd2 f g k) (fun _ _ => Commute.all _ _)

def bwd0 : MvPolynomial σ k →ₐ[k] k ⊗[A] LA f g :=
  MvPolynomial.aeval (fun i => Algebra.TensorProduct.includeRight (rhoA f g (MvPolynomial.X i)))

lemma fibreHypersurfaceBackwardPolynomial_map (p : MvPolynomial σ A) :
    bwd0 f g k (MvPolynomial.map (algebraMap A k) p) =
      Algebra.TensorProduct.includeRight (R := A) (A := k) (rhoA f g p) := by
  letI : IsScalarTower A k (k ⊗[A] LA f g) := TensorProduct.isScalarTower_left
  rw [bwd0, MvPolynomial.aeval_map_algebraMap]
  change _ = ((Algebra.TensorProduct.includeRight (R := A) (A := k)).comp (rhoA f g)) p
  conv_rhs => rw [MvPolynomial.aeval_unique ((Algebra.TensorProduct.includeRight (R := A) (A := k)).comp (rhoA f g))]
  rfl

def bwd1 : (MvPolynomial σ k ⧸ Ik f k) →ₐ[k] k ⊗[A] LA f g :=
  Ideal.Quotient.liftₐ _ (bwd0 f g k) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, fibreHypersurfaceBackwardPolynomial_map]
    have : rhoA f g f = 0 := by
      simp [rhoA, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
    rw [this, map_zero, mul_zero])

lemma fibreHypersurfaceBackwardQuotient_mk (p : MvPolynomial σ k) : bwd1 f g k (Ideal.Quotient.mk _ p) = bwd0 f g k p := rfl

def bwd2 : Lk f g k →ₐ[k] k ⊗[A] LA f g :=
  IsLocalization.Away.liftAlgHom (S := Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)) (f := bwd1 f g k) (by
    rw [fibreHypersurfaceBackwardQuotient_mk, fibreHypersurfaceBackwardPolynomial_map, rhoA_apply]
    exact (IsLocalization.Away.algebraMap_isUnit (S := LA f g)
      (Ideal.Quotient.mk (Ideal.span {f}) g)).map (Algebra.TensorProduct.includeRight (R := A) (A := k)))

lemma fwd_bwd : (fwd f g k).comp (bwd2 f g k) = AlgHom.id k _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g)))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have h1 := fibreHypersurfaceForwardQuotient_mk f g k (MvPolynomial.X i)
  have h2 := fibreHypersurfaceBackwardPolynomial_map f g k (MvPolynomial.X i)
  simp only [MvPolynomial.map_X, rhoK_apply, rhoA_apply] at h1 h2
  change fwd f g k (bwd2 f g k (algebraMap _ (Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.X i)))) =
    algebraMap _ (Lk f g k) (Ideal.Quotient.mk (Ik f k) (MvPolynomial.X i))
  simp only [bwd2, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    fibreHypersurfaceBackwardQuotient_mk, h2, Algebra.TensorProduct.includeRight_apply, fwd, Algebra.TensorProduct.lift_tmul, map_one,
    _root_.one_mul, fwd2, h1]

lemma bwd_fwd : (bwd2 f g k).comp (fwd f g k) = AlgHom.id k _ := by
  letI : IsScalarTower A k (k ⊗[A] LA f g) := TensorProduct.isScalarTower_left
  apply Algebra.TensorProduct.ext
  · ext
  · apply IsLocalization.algHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {f}) g))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    have h1 := fibreHypersurfaceForwardQuotient_mk f g k (MvPolynomial.X i)
    have h2 := fibreHypersurfaceBackwardPolynomial_map f g k (MvPolynomial.X i)
    simp only [MvPolynomial.map_X, rhoK_apply, rhoA_apply] at h1 h2
    change bwd2 f g k (fwd f g k ((1 : k) ⊗ₜ[A] algebraMap _ (LA f g) (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.X i)))) =
      (1 : k) ⊗ₜ[A] algebraMap _ (LA f g) (Ideal.Quotient.mk (Ideal.span {f}) (MvPolynomial.X i))
    simp only [fwd, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul, fwd2, IsLocalization.Away.coe_liftAlgHom,
      IsLocalization.Away.lift_eq, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, bwd2, fibreHypersurfaceBackwardQuotient_mk, h2,
      Algebra.TensorProduct.includeRight_apply]

lemma rhoK_comp : (rhoK f g k).toRingHom =
    (algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k)).comp (Ideal.Quotient.mk (Ik f k)) := rfl

theorem isEmbedding_comap_rhoK : Topology.IsEmbedding (PrimeSpectrum.comap (rhoK f g k).toRingHom) := by
  rw [rhoK_comp, PrimeSpectrum.comap_comp]
  exact (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding.comp
    (PrimeSpectrum.localization_away_isOpenEmbedding (Lk f g k)
      (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))).isEmbedding

theorem range_comap_rhoK : Set.range (PrimeSpectrum.comap (rhoK f g k).toRingHom) =
    PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \
      PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      have : (rhoK f g k).toRingHom (MvPolynomial.map (algebraMap A k) f) = 0 := by
        simp [rhoK_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton_self]
      rw [this]; exact q.asIdeal.zero_mem
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      intro h
      have hu : IsUnit ((rhoK f g k).toRingHom (MvPolynomial.map (algebraMap A k) g)) :=
        IsLocalization.Away.algebraMap_isUnit (S := Lk f g k)
          (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  · rintro ⟨hf, hg⟩
    have h1 : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ik f k))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
        PrimeSpectrum.zeroLocus_span]
      exact hf
    obtain ⟨q0, rfl⟩ := h1
    have h2 : q0 ∈ Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial σ k ⧸ Ik f k) (Lk f g k))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Lk f g k)
        (Ideal.Quotient.mk (Ik f k) (MvPolynomial.map (algebraMap A k) g))]
      intro h
      apply hg
      rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
      exact h
    obtain ⟨q, rfl⟩ := h2
    exact ⟨q, by rw [rhoK_comp, PrimeSpectrum.comap_comp_apply]⟩

end defs

theorem preirreducibleSpace_congr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    PreirreducibleSpace X ↔ PreirreducibleSpace Y := by
  have key : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y),
      PreirreducibleSpace X → PreirreducibleSpace Y := by
    intro X Y _ _ e h
    refine ⟨?_⟩
    have := (PreirreducibleSpace.isPreirreducible_univ (X := X)).image e e.continuous.continuousOn
    rwa [Set.image_univ_of_surjective e.surjective] at this
  exact ⟨key e, key e.symm⟩

theorem spectrum_fibre_preirreducible_iff (A : Type) [CommRing A] (σ : Type) (f g : MvPolynomial σ A)
    (k : Type) [Field k] [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g))) ↔
      IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \
        PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g}) := by
  let e : (k ⊗[A] LA f g) ≃ₐ[k] Lk f g k :=
    AlgEquiv.ofAlgHom (fwd f g k) (bwd2 f g k) (fwd_bwd f g k) (bwd_fwd f g k)
  rw [preirreducibleSpace_congr (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv), ← range_comap_rhoK,
    isPreirreducible_iff_preirreducibleSpace]
  exact preirreducibleSpace_congr (isEmbedding_comap_rhoK f g k).toHomeomorph

end GlobalTheory.FibreHyp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimaryTorsionDivisibleAndTorsionEqIdealTorsion
section
open NumberField

namespace GlobalTheory

theorem primaryTorsion_divisible_and_gTorsion :
    ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (g : ℕ) (I : Ideal (𝓞 E)), g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → (∀ x : M, ∃ y : M, g • y = x) → (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → ∃ y : M, g • y = x ∧ ∀ a ∈ I ^ (j + 1), a • y = 0) ∧ (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → g • x = 0 → ∀ a ∈ I, a • x = 0) := by
  intro E _ _ M _ _ g I hg hN hg2 hdiv
  have hgI : (g : 𝓞 E) ∈ I := by
    have := Ideal.absNorm_mem I
    rwa [hN] at this
  have hIne : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN
    exact hg.ne_zero hN.symm
  have hprime : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hg)
  have hmax : I.IsMaximal := hprime.isMaximal hIne
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 ((Ideal.span_singleton_le_iff_mem I).2 hgI)
  have hJI : ¬ J ≤ I := by
    intro h
    apply hg2
    have h2 : Ideal.span {(g : 𝓞 E)} ≤ I ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact h2 (Ideal.mem_span_singleton_self _)
  have hsup : I ⊔ J = ⊤ := by
    by_contra h
    exact hJI (le_sup_right.trans (le_of_eq (hmax.eq_of_le h le_sup_left).symm))
  have hpow : ∀ k : ℕ, I ^ k ⊔ J = ⊤ := fun k => Ideal.pow_sup_eq_top hsup
  refine ⟨fun j x hx => ?_, fun j x hx hgx a ha => ?_⟩
  · obtain ⟨y0, hy0⟩ := hdiv x
    have h1 : (1 : 𝓞 E) ∈ I ^ j ⊔ J := by rw [hpow j]; exact Submodule.mem_top
    obtain ⟨f, hf, e, he, hfe⟩ := Submodule.mem_sup.1 h1
    refine ⟨e • y0, ?_, ?_⟩
    · rw [← Nat.cast_smul_eq_nsmul (𝓞 E), smul_comm, Nat.cast_smul_eq_nsmul (𝓞 E), hy0]
      have : e = 1 - f := by rw [← hfe]; ring
      rw [this, sub_smul, one_smul, hx f hf, sub_zero]
    · intro a ha
      have hae : a * e ∈ I ^ j * Ideal.span {(g : 𝓞 E)} := by
        rw [hJ, ← mul_assoc, ← pow_succ]
        exact Ideal.mul_mem_mul ha he
      have hker : I ^ j * Ideal.span {(g : 𝓞 E)} ≤
          LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) M y0) := by
        rw [Ideal.mul_le]
        intro c hc s hs
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hs
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, ← mul_assoc, mul_smul,
          Nat.cast_smul_eq_nsmul (𝓞 E), hy0]
        exact hx _ (Ideal.mul_mem_right _ _ hc)
      have := hker hae
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this
      rw [smul_smul]; exact this
  · have hker : I ^ j ⊔ Ideal.span {(g : 𝓞 E)} ≤
        LinearMap.ker (LinearMap.toSpanSingleton (𝓞 E) M x) := by
      refine sup_le (fun b hb => ?_) ?_
      · rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]; exact hx b hb
      · refine (Ideal.span_singleton_le_iff_mem _).2 ?_
        rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Nat.cast_smul_eq_nsmul]
        exact hgx
    have hIle : I ≤ I ^ j ⊔ Ideal.span {(g : 𝓞 E)} := by
      cases j with
      | zero => rw [pow_zero, Ideal.one_eq_top]; exact le_top.trans le_sup_left
      | succ k =>
        have h : I = I ^ (k + 1) ⊔ Ideal.span {(g : 𝓞 E)} := by
          calc I = I * (I ^ k ⊔ J) := by rw [hpow k, Ideal.mul_top]
            _ = I ^ (k + 1) ⊔ Ideal.span {(g : 𝓞 E)} := by rw [Ideal.mul_sup, hJ, pow_succ']
        exact h.le
    have := hker (hIle ha)
    rwa [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOne
section
open NumberField

namespace GlobalTheory

theorem prod_arg_real_unit_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ)
    (hq : q.Prime) (hq2 : 2 < q)
    (u : (𝓞 E)ˣ) (hu : (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)})
    (hreal : ∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E)) :
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) /
      ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  set x : E := ((u : 𝓞 E) : E) with hx
  have hnorm : ∏ w : InfinitePlace E, ‖w.embedding x‖ = 1 := by
    have h1 := InfinitePlace.prod_eq_abs_norm x
    have hN : |Algebra.norm ℚ x| = 1 := Units.norm E u
    rw [hN] at h1
    have h2 : ∏ w : InfinitePlace E, w x ^ w.mult =
        (∏ w : InfinitePlace E, ‖w.embedding x‖) ^ 2 := by
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [IsTotallyComplex.mult_eq, InfinitePlace.norm_embedding_eq]
    rw [h2] at h1
    have h0 : 0 ≤ ∏ w : InfinitePlace E, ‖w.embedding x‖ :=
      Finset.prod_nonneg fun _ _ => norm_nonneg _
    exact (pow_eq_one_iff_of_nonneg h0 two_ne_zero).mp (by exact_mod_cast h1)
  rw [Finset.prod_div_distrib, ← Complex.ofReal_prod, hnorm, Complex.ofReal_one, div_one]
  set P : ℂ := ∏ w : InfinitePlace E, w.embedding x with hP
  have hPreal : starRingEnd ℂ P = P := by
    rw [hP, map_prod]
    exact Finset.prod_congr rfl fun w _ => hreal w.embedding
  have hPnorm : ‖P‖ = 1 := by rw [hP, norm_prod, hnorm]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hu
  have hxy : x = 1 + ((y : 𝓞 E) : E) * (q : E) := by
    have : (u : 𝓞 E) = 1 + y * (q : 𝓞 E) := by rw [hy]; ring
    rw [hx, this]; push_cast; ring
  have hcong : ∃ s ∈ integralClosure ℤ ℂ, P = 1 + s * (q : ℂ) := by
    rw [hP]
    refine Finset.prod_induction _ (fun z => ∃ s ∈ integralClosure ℤ ℂ, z = 1 + s * (q : ℂ))
      ?_ ⟨0, zero_mem _, by ring⟩ ?_
    · rintro a b ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
      refine ⟨s + t + s * t * q, ?_, by ring⟩
      exact add_mem (add_mem hs ht) (mul_mem (mul_mem hs ht) (Subalgebra.natCast_mem _ q))
    · intro w _
      refine ⟨w.embedding ((y : 𝓞 E) : E), ?_, ?_⟩
      · rw [mem_integralClosure_iff]
        exact (RingOfIntegers.isIntegral_coe y).map w.embedding.toIntAlgHom
      · rw [hxy]; simp
  obtain ⟨s, hs, hPs⟩ := hcong
  have hre : P = (P.re : ℂ) := ((Complex.conj_eq_iff_re).mp hPreal).symm
  have habs : |P.re| = 1 := by
    rw [← hPnorm, hre, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  rcases (abs_eq zero_le_one).mp habs with h | h
  · rw [hre, h, Complex.ofReal_one]
  · exfalso
    have hPm : P = -1 := by rw [hre, h]; simp
    have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hs' : s = algebraMap ℚ ℂ (-2 / q) := by
      rw [hPm] at hPs
      rw [map_div₀, map_neg, map_ofNat, map_natCast]
      field_simp
      linear_combination -hPs
    rw [mem_integralClosure_iff, hs'] at hs
    have hint : IsIntegral ℤ ((-2 / q : ℚ)) :=
      (isIntegral_algebraMap_iff ).mp hs
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h2 : (n : ℚ) * q = -2 := by
      rw [show (algebraMap ℤ ℚ n) = (n : ℚ) from rfl] at hn
      rw [hn]; field_simp
    have h3 : n * (q : ℤ) = -2 := by exact_mod_cast h2
    have h4 : (q : ℤ) ∣ 2 := ⟨-n, by linarith⟩
    have h5 : q ∣ 2 := by exact_mod_cast h4
    have := Nat.le_of_dvd two_pos h5
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFourMapsEqOne
section
namespace GlobalTheory.SymmProd

open scoped Matrix

theorem zpow_finsum_eq {U : Type} [CommGroup U] {ι : Type} (s : Finset ι) (x : U) (f : ι → ℤ) :
    x ^ (∑ i ∈ s, f i) = ∏ i ∈ s, x ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem prod_collect {U : Type} [CommGroup U] {r : ℕ} (W M : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (e : ℤ) :
    ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ (M i k * M j l)) ^ (e * W i j)
      = ∏ k, ∏ l, lam k l ^ ((e • (Mᵀ * W * M)) k l) := by
  have h : ∀ k l, (e • (Mᵀ * W * M)) k l = ∑ i, ∑ j, (M i k * M j l) * (e * W i j) := by
    intro k l
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [h, zpow_finsum_eq, ← Finset.prod_zpow, ← zpow_mul]
  calc ∏ i, ∏ j, ∏ k, ∏ l, lam k l ^ (M i k * M j l * (e * W i j))
      = ∏ i, ∏ k, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ j, ∏ l, lam k l ^ (M i k * M j l * (e * W i j)) := Finset.prod_comm
    _ = ∏ k, ∏ i, ∏ l, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun i _ => Finset.prod_comm
    _ = ∏ k, ∏ l, ∏ i, ∏ j, lam k l ^ (M i k * M j l * (e * W i j)) :=
        Finset.prod_congr rfl fun k _ => Finset.prod_comm

theorem prod_antisymm {U : Type} [CommGroup U] {r : ℕ} (D : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k) :
    ∏ k, ∏ l, lam k l ^ ((D - Dᵀ) k l) = 1 := by
  simp only [Matrix.sub_apply, Matrix.transpose_apply, zpow_sub, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  rw [mul_inv_eq_one, Finset.prod_comm]
  exact Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun l _ => by rw [hlam]

theorem prod_four_maps_eq_one (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ)
    (lam : Fin r → Fin r → U) (hlam : ∀ k l, lam k l = lam l k)
    (hW : W = (W + W.transpose) * A) :
    ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^
      ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k *
        (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^
      ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  simp only [prod_collect]
  rw [← prod_antisymm (Aᵀ * W) lam hlam, Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← zpow_finsum_eq, ← Matrix.sum_apply]
  refine congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => lam k l ^ M k l) ?_
  have h2 : Wᵀ * A = W - W * A := by
    rw [eq_sub_iff_add_eq, add_comm, ← add_mul]; exact hW.symm
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_zero, h2]
  noncomm_ring

end GlobalTheory.SymmProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdHomeoSymmApplySnd
section
noncomputable section

namespace GlobalTheory.Cusp.Shear

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N N' : Subgroup G}
  {V : Type} [AddCommGroup V] [TopologicalSpace V] {s : V → G} {π : N → V}

def prodMap (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (z : N' × V) : N :=
  ⟨z.1 * s z.2, N.mul_mem (hle z.1.2) (hs z.2)⟩

theorem coe_prodMap (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (z : N' × V) :
    (prodMap hle hs z : G) = z.1 * s z.2 := rfl

theorem map_inv_of_mul (hπmul : ∀ a b : N, π (a * b) = π a + π b) (a : N) : π a⁻¹ = -π a := by
  have h1 : π 1 = 0 := by simpa using hπmul 1 1
  have := hπmul a a⁻¹
  rw [mul_inv_cancel, h1] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem mul_inv_mem (hs : ∀ v, s v ∈ N) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
    (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (n : N) :
    (n : G) * (s (π n))⁻¹ ∈ N' := by
  have h := (hker (n * (⟨s (π n), hs _⟩ : N)⁻¹)).1 (by
    rw [hπmul, map_inv_of_mul hπmul, hπs ⟨s (π n), hs _⟩ _ rfl, add_neg_cancel])
  simpa using h

def prodHomeo (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') : N' × V ≃ₜ N where
  toFun := prodMap hle hs
  invFun n := (⟨(n : G) * (s (π n))⁻¹, mul_inv_mem hs hπmul hπs hker n⟩, π n)
  left_inv z := by
    have hv : π (prodMap hle hs z) = z.2 := by
      have e : prodMap hle hs z = ⟨z.1, hle z.1.2⟩ * ⟨s z.2, hs _⟩ := rfl
      rw [e, hπmul, hπs ⟨s z.2, hs _⟩ z.2 rfl, (hker _).2 z.1.2, zero_add]
    refine Prod.ext (Subtype.ext ?_) hv
    simp [hv, coe_prodMap]
  right_inv n := by
    apply Subtype.ext
    simp [coe_prodMap]
  continuous_toFun := by
    unfold prodMap
    fun_prop
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hπc
    fun_prop

@[simp] theorem prodHomeo_apply (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (z : N' × V) :
    (prodHomeo hle hs hsc hπc hπmul hπs hker z : G) = z.1 * s z.2 := rfl

end GlobalTheory.Cusp.Shear

end
end

