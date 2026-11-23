module

public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.ExistsExtensionEmbeddingAlgClosed
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_comp_eq_of_numberField (k k' A : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A) :
    ∃ j' : k' →+* A, j'.comp f = j := by
  let _ : Algebra k k' := f.toAlgebra
  let _ : Algebra k A := j.toAlgebra
  have : IsScalarTower ℚ k k' := IsScalarTower.of_algebraMap_eq fun q => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ k') q, eq_ratCast (algebraMap ℚ k) q,
      map_ratCast]
  have : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  refine ⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : k' →ₐ[k] A).commutes x

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealNormPrincipalInExtension
section
open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Lines

theorem ideal_eq_of_pow_eq {R : Type} [CommRing R] [IsDedekindDomain R] {a b : Ideal R} {h : ℕ}
    (hh : h ≠ 0) (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hab : a ^ h = b ^ h) : a = b := by
  classical
  have h1 := congrArg UniqueFactorizationMonoid.normalizedFactors hab
  rw [UniqueFactorizationMonoid.normalizedFactors_pow,
    UniqueFactorizationMonoid.normalizedFactors_pow] at h1
  have h2 : UniqueFactorizationMonoid.normalizedFactors a
      = UniqueFactorizationMonoid.normalizedFactors b := by
    ext p
    have h3 := congrArg (Multiset.count p) h1
    rw [Multiset.count_nsmul, Multiset.count_nsmul] at h3
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hh) h3
  exact associated_iff_eq.mp
    ((UniqueFactorizationMonoid.associated_iff_normalizedFactors_eq_normalizedFactors ha hb).mpr h2)

theorem principal_of_root (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (h : ℕ) (hh : h ≠ 0) (c : 𝓞 K)
    (hc : I ^ h = Ideal.span {c}) (z : K') (hz : z ^ h = algebraMap K K' (c : K)) :
    ∃ y : 𝓞 K', y ≠ 0 ∧ y ∈ I.map (algebraMap (𝓞 K) (𝓞 K')) ∧
      |((Algebra.norm ℚ (y : K') : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ Module.finrank K K' := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero] at hc
    exact pow_ne_zero h hI hc
  have hcK : (c : K) ≠ 0 := fun h0 => hc0 (RingOfIntegers.ext h0)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hh] at hz
    exact hcK ((map_eq_zero _).mp hz.symm)
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hh) ?_
    rw [hz]
    exact (c.2 : IsIntegral ℤ (c : K)).map (IsScalarTower.toAlgHom ℤ K K')
  let y : 𝓞 K' := ⟨z, hint⟩
  have hyz : (y : K') = z := rfl
  have hy0 : y ≠ 0 := fun h0 => hz0 (by rw [← hyz, h0]; rfl)
  have hyc : y ^ h = algebraMap (𝓞 K) (𝓞 K') c := by
    apply RingOfIntegers.ext
    exact (map_pow (algebraMap (𝓞 K') K') y h).trans hz
  have hspan : Ideal.span {y} ^ h = (I.map (algebraMap (𝓞 K) (𝓞 K'))) ^ h := by
    rw [Ideal.span_singleton_pow, hyc, ← Ideal.map_pow, hc, Ideal.map_span, Set.image_singleton]
  have heq : Ideal.span {y} = I.map (algebraMap (𝓞 K) (𝓞 K')) := by
    have hs0 : Ideal.span {y} ≠ ⊥ := by simpa using hy0
    refine ideal_eq_of_pow_eq hh hs0 ?_ hspan
    intro h0
    rw [h0, ← Ideal.zero_eq_bot, zero_pow hh] at hspan
    exact pow_ne_zero h hs0 hspan
  refine ⟨y, hy0, heq ▸ Ideal.mem_span_singleton_self y, ?_⟩
  have hnc : |((Algebra.norm ℚ (c : K) : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ h := by
    have h1 : I.absNorm ^ h = (Algebra.norm ℤ c).natAbs := by
      rw [← map_pow, hc, Ideal.absNorm_span_singleton]
    rw [← Algebra.coe_norm_int]
    have h2 : ((I.absNorm : ℝ)) ^ h = ((Algebra.norm ℤ c).natAbs : ℝ) := by exact_mod_cast h1
    rw [h2, Nat.cast_natAbs]
    simp
  have hN : Algebra.norm ℚ (z ^ h) = (Algebra.norm ℚ (c : K)) ^ Module.finrank K K' := by
    rw [hz, ← Algebra.norm_norm (R := ℚ) (S := K) (A := K'), Algebra.norm_algebraMap, map_pow]
  have hpow : |((Algebra.norm ℚ z : ℚ) : ℝ)| ^ h
      = ((I.absNorm : ℝ) ^ Module.finrank K K') ^ h := by
    rw [← abs_pow, ← Rat.cast_pow, ← map_pow, hN, Rat.cast_pow, abs_pow, hnc, ← pow_mul, ← pow_mul,
      mul_comm]
  exact (pow_left_inj₀ (abs_nonneg _) (by positivity) hh).mp hpow

theorem exists_principal_extension : ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (𝓞 K)),
    I ≠ ⊥ → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (y : 𝓞 K'),
      y ≠ 0 ∧ y ∈ I.map (algebraMap (𝓞 K) (𝓞 K')) ∧
        |((Algebra.norm ℚ (y : K') : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ Module.finrank K K' := by
  intro K _ _ I hI
  obtain ⟨h, c, hh, hc⟩ := GlobalTheory.UnRep.exists_pow_eq_span_singleton K I hI
  let p : Polynomial K := Polynomial.X ^ h - Polynomial.C (c : K)
  have hdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hh)]
    exact_mod_cast hh
  haveI : FiniteDimensional ℚ p.SplittingField := FiniteDimensional.trans ℚ K p.SplittingField
  haveI : NumberField p.SplittingField := NumberField.mk
  obtain ⟨z, hz⟩ := (Polynomial.SplittingField.splits p).exists_eval_eq_zero
    (by rwa [Polynomial.degree_map])
  have hz' : z ^ h = algebraMap K p.SplittingField (c : K) := by
    simpa [p, sub_eq_zero] using hz
  obtain ⟨y, h1, h2, h3⟩ := principal_of_root K p.SplittingField I hI h hh c hc z hz'
  exact ⟨p.SplittingField, inferInstance, inferInstance, inferInstance, y, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Lines
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsOfNonzeroAdelic
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl.LogNorms

theorem norm_integer_le_one (p : ℕ) [Fact p.Prime] {k : Type} [Field k] (ι : k →+* ℂ_[p])
    (a : 𝓞 k) : ‖ι (a : k)‖ ≤ 1 := by
  letI : Algebra ℤ ℂ_[p] := Ring.toIntAlgebra _
  exact (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).isIntegral_iff_v_le_one.1
    ((map_isIntegral_int ι (RingOfIntegers.isIntegral_coe a)).tower_top)

theorem norm_intCast_eq_one (p : ℕ) [hp : Fact p.Prime] {z : ℤ} (h : ¬ (p : ℤ) ∣ z) :
    ‖(z : ℂ_[p])‖ = 1 := by
  have h1 : ‖(z : ℚ_[p])‖ = 1 := Padic.norm_intCast_eq_one_iff.2
    ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp.out)).2 h).symm
  rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) z, norm_algebraMap', h1]

theorem exists_int_mul_eq_integer {k : Type} [Field k] [NumberField k] (x : k) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ a : 𝓞 k, (a : k) = n * x := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ (L := k) {x}
  exact ⟨d, hd, ⟨d • x, h x (Finset.mem_singleton_self x)⟩, zsmul_eq_mul x d⟩

theorem norm_le_one_of_mul {k : Type} [Field k] (p : ℕ) [Fact p.Prime] (ι : k →+* ℂ_[p])
    {x : k} {n : ℤ} {a : 𝓞 k} (ha : (a : k) = n * x) (hp : ¬ (p : ℤ) ∣ n) : ‖ι x‖ ≤ 1 := by
  have h := norm_integer_le_one p ι a
  rwa [ha, map_mul, map_intCast, norm_mul, norm_intCast_eq_one p hp, one_mul] at h

theorem isAdelic_ofElt (k : Type) [Field k] [NumberField k] (x : k) (hx : x ≠ 0) :
    (LogNorms.ofElt x).IsAdelic := by
  obtain ⟨n, hn, a, ha⟩ := exists_int_mul_eq_integer x
  obtain ⟨m, hm, b, hb⟩ := exists_int_mul_eq_integer x⁻¹
  have hfin : {p : Nat.Primes | (p : ℕ) ∣ (n * m).natAbs}.Finite := by
    refine Set.Finite.of_injOn (f := fun p : Nat.Primes => (p : ℕ))
      (t := ((n * m).natAbs.primeFactors : Set ℕ)) ?_ (fun _ _ _ _ h => Subtype.ext h)
      (Finset.finite_toSet _)
    intro p hp
    exact Finset.mem_coe.2 (Nat.mem_primeFactors.2
      ⟨p.2, hp, Int.natAbs_ne_zero.2 (mul_ne_zero hn hm)⟩)
  refine hfin.subset ?_
  rintro p ⟨ι, hι⟩
  by_contra hp
  have hnm : ¬ ((p : ℕ) : ℤ) ∣ n * m := fun h => hp (Int.natCast_dvd.1 h)
  have hpn : ¬ ((p : ℕ) : ℤ) ∣ n := fun h => hnm (h.mul_right m)
  have hpm : ¬ ((p : ℕ) : ℤ) ∣ m := fun h => hnm (h.mul_left n)
  have h1 : ‖ι x‖ ≤ 1 := norm_le_one_of_mul p ι ha hpn
  have h2 : ‖ι x⁻¹‖ ≤ 1 := norm_le_one_of_mul p ι hb hpm
  have h0 : 0 < ‖ι x‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hx)
  rw [map_inv₀, norm_inv] at h2
  have h3 : ‖ι x‖ = 1 := le_antisymm h1 ((inv_le_one₀ h0).1 h2)
  apply hι
  change Real.log ‖ι x‖ = 0
  rw [h3, Real.log_one]

end GlobalTheory.CompanionTheory.Ar.Fl.LogNorms
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogEmbeddingsEqNorm
section
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem sum_log_norm_embeddings_eq_log_norm (k A : Type) [Field k] [NumberField k] [NormedField A]
    [CharZero A] [IsAlgClosed A] (x : k) (hx : x ≠ 0) :
    ∑ j : k →+* A, Real.log ‖j x‖ = Real.log ‖((Algebra.norm ℚ x : ℚ) : A)‖ := by
  letI : Algebra ℚ A := DivisionRing.toRatAlgebra
  have h1 : algebraMap ℚ A (Algebra.norm ℚ x) = ∏ σ : k →ₐ[ℚ] A, σ x :=
    Algebra.norm_eq_prod_embeddings ℚ A x
  have h2 : ((Algebra.norm ℚ x : ℚ) : A) = ∏ σ : k →ₐ[ℚ] A, σ x := by
    rw [← h1]; simp
  have h3 : ∏ σ : k →ₐ[ℚ] A, σ x = ∏ j : k →+* A, j x :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom (R := k) (S := A)).symm _ _ (fun σ => rfl)
  rw [h2, h3, norm_prod, Real.log_prod]
  intro j _
  exact norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hx)

end GlobalTheory.CompanionTheory.Ar.Fl
end

