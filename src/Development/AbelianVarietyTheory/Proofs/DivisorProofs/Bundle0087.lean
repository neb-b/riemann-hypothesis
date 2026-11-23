module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoOrderLOfCyclotomicIrreducible
section
namespace GlobalTheory

open Polynomial in
theorem no_order_l_of_cyclotomic_irreducible :
    ∀ (E : Type) [Field E] [CharZero E] (l N : ℕ) (g : Matrix (Fin N) (Fin N) E),
      l.Prime → Irreducible (Polynomial.cyclotomic l E) → N + 1 < l → g ^ l = 1 → g = 1 := by
  intro E _ _ l N g hl hirr hN hg
  haveI : Fact l.Prime := ⟨hl⟩
  have hmon : g.charpoly.Monic := Matrix.charpoly_monic g
  have hdeg : g.charpoly.natDegree = N := by
    simpa using Matrix.charpoly_natDegree_eq_dim g
  have hndvd : ¬ cyclotomic l E ∣ g.charpoly := by
    intro h
    have h1 := Polynomial.natDegree_le_of_dvd h hmon.ne_zero
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hl, hdeg] at h1
    omega
  obtain ⟨a, b, hab⟩ := (hirr.coprime_iff_not_dvd).2 hndvd
  have hev := congrArg (aeval g) hab
  simp only [map_add (f := _), map_mul, map_one, Matrix.aeval_self_charpoly, mul_zero, add_zero] at hev
  have hcyc : aeval g (cyclotomic l E) * (g - 1) = 0 := by
    have := congrArg (aeval g) (Polynomial.cyclotomic_prime_mul_X_sub_one E l)
    simp only [map_mul, map_sub, aeval_X, map_one, map_pow] at this
    rw [this, hg, sub_self]
  have : g - 1 = 0 := by
    calc g - 1 = (aeval g a * aeval g (cyclotomic l E)) * (g - 1) := by rw [hev, one_mul]
      _ = aeval g a * (aeval g (cyclotomic l E) * (g - 1)) := by rw [mul_assoc]
      _ = 0 := by rw [hcyc, mul_zero]
  exact sub_eq_zero.1 this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoSplittingFactorisationOfPderivNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hypersurface_part_no_splitting_factorisation :
    ∀ (Ω : Type) [Field Ω] (σ : Type) (f g : MvPolynomial σ Ω) (i : σ) (D : ℕ),
      (∀ Q : σ → Ω, MvPolynomial.eval Q f = 0 → MvPolynomial.eval Q g ≠ 0 →
        MvPolynomial.eval Q (MvPolynomial.pderiv i f) ≠ 0) →
      IsPreirreducible (PrimeSpectrum.zeroLocus {f} \ PrimeSpectrum.zeroLocus {g}) →
      ¬ (∃ u v : MvPolynomial σ Ω, u.totalDegree ≤ D ∧ v.totalDegree ≤ D ∧ u * v = f ∧
        ∃ P Q : σ → Ω, MvPolynomial.eval P u = 0 ∧ MvPolynomial.eval P g ≠ 0 ∧
          MvPolynomial.eval Q v = 0 ∧ MvPolynomial.eval Q g ≠ 0) := by
  intro Ω _ σ f g i D hsmooth hirr ⟨u, v, _, _, huv, P, Q, hPu, hPg, hQv, hQg⟩
  subst huv
  let pt : (σ → Ω) → PrimeSpectrum (MvPolynomial σ Ω) := fun R =>
    ⟨RingHom.ker (MvPolynomial.eval R), RingHom.ker_isPrime _⟩
  have mem_pt : ∀ R h, h ∈ (pt R).asIdeal ↔ MvPolynomial.eval R h = 0 :=
    fun R h => RingHom.mem_ker
  have inS : ∀ R, MvPolynomial.eval R (u * v) = 0 → MvPolynomial.eval R g ≠ 0 →
      pt R ∈ PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} := by
    intro R h1 h2
    refine ⟨?_, ?_⟩
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact (mem_pt R _).2 h1
    · rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
      exact fun h => h2 ((mem_pt R _).1 h)
  have hcov : PrimeSpectrum.zeroLocus {u * v} \ PrimeSpectrum.zeroLocus {g} ⊆
      PrimeSpectrum.zeroLocus {u} ∪ PrimeSpectrum.zeroLocus {v} := by
    intro x hx
    have hx1 := hx.1
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hx1
    rcases x.isPrime.mem_or_mem hx1 with h | h
    · left; rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact h
    · right; rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]; exact h
  have key : ∀ R, MvPolynomial.eval R u = 0 → MvPolynomial.eval R v = 0 →
      MvPolynomial.eval R g ≠ 0 → False := by
    intro R hu hv hg
    apply hsmooth R (by simp [hu]) hg
    simp [Derivation.leibniz, hu, hv]
  rcases (isPreirreducible_iff_isClosed_union_isClosed.1 hirr) _ _
      (PrimeSpectrum.isClosed_zeroLocus _) (PrimeSpectrum.isClosed_zeroLocus _) hcov with h | h
  · have hm := h (inS Q (by simp [hQv]) hQg)
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hm
    exact key Q ((mem_pt Q _).1 hm) hQv hQg
  · have hm := h (inS P (by simp [hPu]) hPg)
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff] at hm
    exact key P hPu ((mem_pt P _).1 hm) hPg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherNormalizationFiniteAevalPowAdd
section
open Polynomial

namespace GlobalTheory

theorem noether_trick_monic {k : Type} [Field k] (f : Polynomial (Polynomial k)) (hf : f.Monic)
    (M : ℕ) (hM0 : M ≠ 0) (hM : ∀ i, (f.coeff i).natDegree < M) :
    (f.eval₂ (Polynomial.mapRingHom (Polynomial.C : k →+* Polynomial k))
      ((Polynomial.X : Polynomial (Polynomial k)) ^ M - Polynomial.C Polynomial.X)).Monic := by
  set r : Polynomial (Polynomial k) := X ^ M - C X with hr
  have hrm : r.Monic := monic_X_pow_sub_C _ hM0
  have hrd : r.natDegree = M := natDegree_X_pow_sub_C _
  rw [eval₂_eq_sum_range, Finset.sum_range_succ]
  have hlead : f.coeff f.natDegree = 1 := hf
  rw [hlead, map_one, one_mul]
  apply Monic.add_of_right (hrm.pow _)
  rw [degree_eq_natDegree (hrm.pow _).ne_zero, hrm.natDegree_pow, hrd]
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  rw [Finset.mem_range] at hi
  refine lt_of_le_of_lt degree_le_natDegree ?_
  rw [Nat.cast_lt]
  have h1 : (mapRingHom (C : k →+* Polynomial k) (f.coeff i)).natDegree ≤ (f.coeff i).natDegree := by
    rw [coe_mapRingHom]; exact natDegree_map_le
  have h2 : (r ^ i).natDegree ≤ i * M := by
    rw [← hrd]; exact natDegree_pow_le
  have h3 := hM i
  have h4 : (i + 1) * M ≤ f.natDegree * M := Nat.mul_le_mul_right M hi
  calc _ ≤ _ := natDegree_mul_le
    _ ≤ (f.coeff i).natDegree + i * M := Nat.add_le_add h1 h2
    _ < f.natDegree * M := by nlinarith

theorem noether_trick : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (t a : A),
    (Polynomial.aeval (R := k) t).Finite → ∃ M : ℕ, (Polynomial.aeval (R := k) (t ^ M + a)).Finite := by
  intro k A _ _ _ t a ht
  have hint : (aeval (R := k) t).toRingHom.IsIntegral := RingHom.Finite.to_isIntegral ht
  obtain ⟨f, hfm, hf0⟩ := hint (-a)
  set M := 1 + ∑ i ∈ Finset.range (f.natDegree + 1), (f.coeff i).natDegree with hMdef
  have hM : ∀ i, (f.coeff i).natDegree < M := by
    intro i
    by_cases hi : i ≤ f.natDegree
    · have := Finset.single_le_sum (f := fun i => (f.coeff i).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      have h' : (f.coeff i).natDegree ≤ ∑ j ∈ Finset.range (f.natDegree + 1), (f.coeff j).natDegree := this
      omega
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; simp only [natDegree_zero]; omega
  refine ⟨M, ?_⟩
  set φ : Polynomial k →+* A := (aeval (R := k) (t ^ M + a)).toRingHom with hφ
  set q : Polynomial (Polynomial k) :=
    f.eval₂ (mapRingHom (C : k →+* Polynomial k)) (X ^ M - C X) with hqdef
  have hq : q.Monic := noether_trick_monic f hfm M (by omega) hM
  set ψ : Polynomial (Polynomial k) →+* A := eval₂RingHom φ t with hψ
  have hcomp : ψ.comp (mapRingHom C) = (aeval (R := k) t).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c; simp [ψ, φ]
    · simp [ψ, φ]
  have hψq : ψ q = 0 := by
    simp only [hqdef]
    rw [hom_eval₂, hcomp]
    have : ψ (X ^ M - C X) = -a := by simp [ψ, φ]
    rw [this]; exact hf0
  have hqt : q.eval₂ φ t = 0 := by simpa [ψ] using hψq
  let L : AdjoinRoot q →+* A := AdjoinRoot.lift φ t hqt
  have hL : L.comp (AdjoinRoot.mk q) = ψ := by
    ext g <;> simp [L, ψ, AdjoinRoot.lift_mk]
  have hψfin : ψ.Finite := by
    apply RingHom.Finite.of_comp_finite (f := mapRingHom (C : k →+* Polynomial k))
    rw [hcomp]; exact ht
  have hLfin : L.Finite := by
    apply RingHom.Finite.of_comp_finite (f := AdjoinRoot.mk q)
    rw [hL]; exact hψfin
  have hof : (AdjoinRoot.of q).Finite := by
    haveI : Module.Finite (Polynomial k) (AdjoinRoot q) := (AdjoinRoot.powerBasis' hq).finite
    exact RingHom.finite_algebraMap.mpr this
  have hφeq : L.comp (AdjoinRoot.of q) = φ := by
    ext c <;> simp [L, AdjoinRoot.lift_of]
  have : φ.Finite := by rw [← hφeq]; exact hLfin.comp hof
  exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAlgHomAdjoin
section
namespace GlobalTheory.AdjoinAlgebraHomNonempty

theorem nonempty_algHom_adjoin (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω]
    [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S) (hh : ψ h ≠ 0) (T : Set F)
    (hT : ∀ x ∈ T, (h : F) * x ∈ S) : Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by
  have h0 : h ≠ 0 := fun e => hh (by rw [e, map_zero])
  have h0F : (h : F) ≠ 0 := fun e => h0 (Subtype.ext e)
  have hu : ∀ y : Submonoid.powers h, IsUnit (S.val y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ h0F).pow n
  have hv : ∀ y : Submonoid.powers h, IsUnit (ψ y) := by
    rintro ⟨y, n, rfl⟩
    simp only [map_pow]
    exact (IsUnit.mk0 _ hh).pow n
  let f : Localization.Away h →ₐ[k] F := IsLocalization.liftAlgHom (M := Submonoid.powers h) hu
  let g : Localization.Away h →ₐ[k] Ω := IsLocalization.liftAlgHom (M := Submonoid.powers h) hv
  have hf : ∀ s : S, f (algebraMap S (Localization.Away h) s) = (s : F) := fun s => by
    simp [f, IsLocalization.liftAlgHom_apply]
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (Submonoid.powers h) z
    have h1 := congrArg f hab
    rw [map_mul, hz, zero_mul, hf] at h1
    have ha : a = 0 := Subtype.ext h1.symm
    rw [ha, map_zero] at hab
    exact (IsLocalization.map_units (Localization.Away h) b).mul_left_eq_zero.mp hab
  have hle : Algebra.adjoin k T ≤ f.range := by
    refine Algebra.adjoin_le fun x hx => ?_
    obtain ⟨u, hu'⟩ := IsLocalization.map_units (Localization.Away h)
      (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)
    refine ⟨(↑u⁻¹ : Localization.Away h) * algebraMap S _ ⟨_, hT x hx⟩, ?_⟩
    apply mul_left_cancel₀ h0F
    have e : f u = (h : F) := by rw [hu']; exact hf h
    change (h : F) * f _ = _
    rw [map_mul, hf, ← mul_assoc]
    have e2 : (h : F) * f (↑u⁻¹ : Localization.Away h) = 1 := by
      rw [← e, ← map_mul, Units.mul_inv, map_one]
    rw [e2, one_mul]
  exact ⟨(g.comp (AlgEquiv.ofInjective f hinj).symm.toAlgHom).comp (Subalgebra.inclusion hle)⟩

end GlobalTheory.AdjoinAlgebraHomNonempty
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRingHomComplexOfFg
section
set_option autoImplicit false

namespace GlobalTheory.FGFieldEmb

open Cardinal

theorem nonempty_ringHom_complex_of_mk_le (K : Type) [Field K] [CharZero K] (hK : #K ≤ 𝔠) :
    Nonempty (K →+* ℂ) := by
  let F := FractionRing (MvPolynomial ℝ K)
  let L := AlgebraicClosure F
  have hF : #F = 𝔠 := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max, Cardinal.mk_real, max_eq_right hK,
      max_eq_left Cardinal.aleph0_le_continuum]
  have hL : #L = 𝔠 := by
    refine le_antisymm ?_ (hF ▸ Cardinal.mk_le_of_injective (algebraMap F L).injective)
    have := Algebra.IsAlgebraic.cardinalMk_le_max F L
    rwa [hF, max_eq_left Cardinal.aleph0_le_continuum] at this
  let j : K →+* L := (algebraMap F L).comp ((algebraMap (MvPolynomial ℝ K) F).comp MvPolynomial.C)
  have : CharZero L := (RingHom.charZero_iff j.injective).1 inferInstance
  obtain ⟨e⟩ := IsAlgClosed.ringEquiv_of_equiv_of_charZero (K := L) (L := ℂ)
    (hL ▸ Cardinal.aleph0_lt_continuum) (Cardinal.eq.1 (hL.trans Cardinal.mk_complex.symm))
  exact ⟨e.toRingHom.comp j⟩

theorem nonempty_ringHom_complex_of_fg :
    ∀ (K : Type) [Field K] [CharZero K] (k : IntermediateField ℚ K), k.FG → Nonempty (k →+* ℂ) := by
  intro K _ _ k hk
  obtain ⟨t, rfl⟩ := hk
  refine nonempty_ringHom_complex_of_mk_le _ ?_
  refine le_trans ?_ Cardinal.aleph0_le_continuum
  refine (IntermediateField.cardinalMk_adjoin_le ℚ (t : Set K)).trans ?_
  refine max_le (max_le ?_ ?_) le_rfl
  · simp [Cardinal.mkRat]
  · exact (Cardinal.lt_aleph0_of_finite _).le

end GlobalTheory.FGFieldEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormClassFiniteOfReducedRatAlgebra
section
open scoped TensorProduct Classical

namespace GlobalTheory
namespace ReducedInvolutionNormClass

variable {E : Type} [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E]

theorem numberField_quot (I : Ideal E) [I.IsMaximal] :
    @NumberField (E ⧸ I) (Ideal.Quotient.field I) := by
  letI := Ideal.Quotient.field I
  have hfin : Module.Finite ℚ (E ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : CharZero (E ⧸ I) := charZero_of_injective_ringHom (algebraMap ℚ (E ⧸ I)).injective
  exact @NumberField.mk _ _ _ (by
    convert hfin
    exact congrArg (fun A : Algebra ℚ (E ⧸ I) => A.toModule) (Subsingleton.elim _ (Ideal.Quotient.algebra ℚ)))

theorem stable_factor (H : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e)) (τ : E ≃ₐ[ℚ] E) (hτ : ∀ x, τ (τ x) = x) (S : Finset ℕ)
    (I : Ideal E) [I.IsMaximal] (hI : ∀ x ∈ I, τ x ∈ I) :
    ∃ M : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ m ∈ M, ∃ e : E, e ∉ I ∧ a - e * m * τ e ∈ I := by
  letI := Ideal.Quotient.field I
  haveI := numberField_quot I
  have hmap : I = I.map (τ : E ≃+* E) := by
    apply le_antisymm
    · intro x hx
      have : x = (τ : E ≃+* E) (τ x) := (hτ x).symm
      rw [this]; exact Ideal.mem_map_of_mem _ (hI x hx)
    · rw [Ideal.map_le_iff_le_comap]; intro x hx; exact hI x hx
  let τI := Ideal.quotientEquiv I I (τ : E ≃+* E) hmap
  have hτmk : ∀ x, τI (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (τ x) := fun x => rfl
  have hτI : ∀ z, τI (τI z) = z := by
    intro z; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hτmk, hτmk, hτ]
  obtain ⟨M, hM⟩ := H (E ⧸ I) τI hτI S
  let lift : E ⧸ I → E := fun z => Classical.choose (Ideal.Quotient.mk_surjective z)
  have hlift : ∀ z, Ideal.Quotient.mk I (lift z) = z :=
    fun z => Classical.choose_spec (Ideal.Quotient.mk_surjective z)
  refine ⟨M.image lift, fun a ha hτa hyp => ?_⟩
  have ha0 : Ideal.Quotient.mk I a ≠ 0 := (ha.map _).ne_zero
  obtain ⟨m, hm, e', he', hae⟩ := hM (Ideal.Quotient.mk I a) ha0 (by rw [hτmk, hτa]) (by
    intro ℓ hℓ hS
    obtain ⟨b, x, y, hb, h1, h2, d, hd, hx, hy⟩ := hyp ℓ hℓ hS
    refine ⟨Ideal.Quotient.mk I b, Ideal.Quotient.mk I x, Ideal.Quotient.mk I y,
      (hb.map _).ne_zero, ?_, ?_, d, hd, ?_, ?_⟩
    · rw [hτmk, h1, map_mul, map_mul]
    · rw [hτmk, ← map_mul, h2, map_mul]
    · have := hx.map (Ideal.Quotient.mk I).toIntAlgHom
      simp only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this
      convert this using 1
      all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _)
    · have := hy.map (Ideal.Quotient.mk I).toIntAlgHom
      simp only [map_mul, map_natCast, RingHom.toIntAlgHom_apply] at this
      convert this using 1
      all_goals first | rfl | exact Subsingleton.elim _ _ | (congr; exact Subsingleton.elim _ _))
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective e'
  refine ⟨lift m, Finset.mem_image_of_mem _ hm, e, ?_, ?_⟩
  · intro he; exact he' (Ideal.Quotient.eq_zero_iff_mem.2 he)
  · rw [← Ideal.Quotient.eq, map_mul, map_mul, hlift, hae, hτmk]

variable [IsReduced E]

theorem crt (c : MaximalSpectrum E → E) : ∃ u : E, ∀ I : MaximalSpectrum E, u - c I ∈ I.asIdeal := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  refine ⟨(IsArtinianRing.equivPi E).symm (fun I => Ideal.Quotient.mk I.asIdeal (c I)), fun I => ?_⟩
  rw [← Ideal.Quotient.eq]
  exact congrFun ((IsArtinianRing.equivPi E).apply_symm_apply
    (fun I => Ideal.Quotient.mk I.asIdeal (c I))) I

theorem eq_zero_of_mem_all (x : E) (h : ∀ I : MaximalSpectrum E, x ∈ I.asIdeal) : x = 0 := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  apply (IsArtinianRing.equivPi E).injective
  rw [map_zero]; funext I; exact Ideal.Quotient.eq_zero_iff_mem.2 (h I)

end ReducedInvolutionNormClass


open ReducedInvolutionNormClass in
theorem normClassFinite_of_reduced : (∀ (K : Type) [Field K] [NumberField K] (τ : K ≃+* K), (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ,
    ∃ M : Finset K, ∀ a : K, a ≠ 0 → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : K), b ≠ 0 ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : K) * x) ∧ IsIntegral ℤ ((d : K) * y)) →
    ∃ m ∈ M, ∃ e : K, e ≠ 0 ∧ a = e * m * τ e) →
  ∀ (E : Type) [CommRing E] [Algebra ℚ E] [FiniteDimensional ℚ E] [IsReduced E] (τ : E ≃ₐ[ℚ] E),
    (∀ x, τ (τ x) = x) → ∀ S : Finset ℕ, ∃ A : Finset E, ∀ a : E, IsUnit a → τ a = a →
    (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (b x y : E), IsUnit b ∧ a = x * (b * τ b) ∧ b * τ b = y * a ∧
      ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : E) * x) ∧ IsIntegral ℤ ((d : E) * y)) →
    ∃ a₀ ∈ A, ∃ e : Eˣ, a = (e : E) * a₀ * τ e := by
  intro H E _ _ _ _ τ hτ S
  haveI : IsArtinianRing E := IsArtinianRing.of_finite ℚ E
  haveI : Fintype (MaximalSpectrum E) := Fintype.ofFinite _
  let σ : MaximalSpectrum E → MaximalSpectrum E := fun I =>
    ⟨I.asIdeal.comap (τ : E ≃+* E), Ideal.comap_isMaximal_of_surjective _ (τ : E ≃+* E).surjective⟩
  have hσ : ∀ I x, x ∈ (σ I).asIdeal ↔ τ x ∈ I.asIdeal := fun I x => Iff.rfl
  have hσσ : ∀ I, σ (σ I) = I := fun I =>
    MaximalSpectrum.ext (Ideal.ext fun x => by rw [hσ, hσ, hτ])
  have hst : ∀ I, σ I = I → ∀ x ∈ I.asIdeal, τ x ∈ I.asIdeal := by
    intro I h x hx; rw [← hσ, h]; exact hx
  let n := Fintype.equivFin (MaximalSpectrum E)
  let ch : MaximalSpectrum E → Prop := fun I => n I < n (σ I)
  let Mset : MaximalSpectrum E → Finset E := fun I =>
    if h : σ I = I then Classical.choose (stable_factor H τ hτ S I.asIdeal (hst I h)) else {1}
  let F : (MaximalSpectrum E → E) → E := fun f => Classical.choose (crt f)
  have hF : ∀ f I, F f - f I ∈ I.asIdeal := fun f => Classical.choose_spec (crt f)
  refine ⟨(Fintype.piFinset Mset).image F, fun a ha hτa hyp => ?_⟩
  have key : ∀ I, ∃ m ∈ Mset I, ∃ e : E, e ∉ I.asIdeal ∧ (σ I = I → a - e * m * τ e ∈ I.asIdeal) ∧
      (σ I ≠ I → m = 1 ∧ e = if ch I then a else 1) := by
    intro I
    by_cases h : σ I = I
    · obtain ⟨m, hm, e, he, hae⟩ :=
        Classical.choose_spec (stable_factor H τ hτ S I.asIdeal (hst I h)) a ha hτa hyp
      refine ⟨m, by simp only [Mset, dif_pos h]; exact hm, e, he, fun _ => hae, fun h' => absurd h h'⟩
    · refine ⟨1, by simp [Mset, h], if ch I then a else 1, ?_, fun h' => absurd h' h, fun _ => ⟨rfl, rfl⟩⟩
      split_ifs
      · exact fun hmem => I.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem ha)
      · exact fun hmem => I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
  choose m hm e he hst1 hst2 using key
  obtain ⟨u, hu⟩ := crt e
  have hunit : IsUnit u := by
    by_contra hn
    obtain ⟨J, hJ, huJ⟩ := exists_max_ideal_of_mem_nonunits hn
    apply he ⟨J, hJ⟩
    have := J.sub_mem huJ (hu ⟨J, hJ⟩)
    simpa using this
  refine ⟨F m, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hm), hunit.unit, ?_⟩
  simp only [IsUnit.unit_spec]
  rw [← sub_eq_zero]
  apply eq_zero_of_mem_all
  intro I
  have hu' : ∀ J : MaximalSpectrum E, Ideal.Quotient.mk J.asIdeal u = Ideal.Quotient.mk J.asIdeal (e J) :=
    fun J => Ideal.Quotient.eq.2 (hu J)
  have hF' : Ideal.Quotient.mk I.asIdeal (F m) = Ideal.Quotient.mk I.asIdeal (m I) :=
    Ideal.Quotient.eq.2 (hF m I)
  have hτu : ∀ J, Ideal.Quotient.mk J.asIdeal (τ u) = Ideal.Quotient.mk J.asIdeal (τ (e (σ J))) := by
    intro J; rw [Ideal.Quotient.eq, ← map_sub, ← hσ]; exact hu (σ J)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hu', hF', hτu, sub_eq_zero]
  by_cases h : σ I = I
  · rw [h, ← map_mul, ← map_mul, Ideal.Quotient.eq]
    exact hst1 I h
  · obtain ⟨hm1, he1⟩ := hst2 I h
    have hJ : σ (σ I) ≠ σ I := by rw [hσσ]; exact fun h' => h h'.symm
    obtain ⟨_, he2⟩ := hst2 (σ I) hJ
    rw [hm1, he1, he2]
    have hne : n I ≠ n (σ I) := fun h' => h (n.injective h').symm
    by_cases hc : ch I
    · have hc' : ¬ ch (σ I) := by
        show ¬ n (σ I) < n (σ (σ I)); rw [hσσ]; exact not_lt.2 hc.le
      rw [if_pos hc, if_neg hc']
      simp
    · have hc' : ch (σ I) := by
        show n (σ I) < n (σ (σ I)); rw [hσσ]; exact lt_of_le_of_ne (not_lt.1 hc) hne.symm
      rw [if_neg hc, if_pos hc', hτa]
      simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormEigenvalueLeOneOfEntries
section
namespace GlobalTheory.EigenvalueNormAtMostOne

theorem norm_eigenvalue_le_one_of_entries {K : Type} [NormedField K] [IsUltrametricDist K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (c : Fin n → K) (μ : K) (hc : c ≠ 0) (h : A.mulVec c = μ • c) : ‖μ‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hc
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖c j‖)
    ⟨k, Finset.mem_univ k⟩
  have hpos : 0 < ‖c i‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hk) (hi k (Finset.mem_univ k))
  have hrow : ∑ j, A i j * c j = μ * c i := by
    have := congrFun h i
    simpa [Matrix.mulVec, dotProduct] using this
  have hle : ‖∑ j, A i j * c j‖ ≤ ‖c i‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j hj
    rw [norm_mul]
    calc ‖A i j‖ * ‖c j‖ ≤ 1 * ‖c i‖ :=
          mul_le_mul (hA i j) (hi j hj) (norm_nonneg _) zero_le_one
      _ = ‖c i‖ := one_mul _
  rw [hrow, norm_mul] at hle
  exact le_of_mul_le_mul_right (by rwa [one_mul]) hpos

theorem norm_eigenvalue_le_one :
    ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (O : Type) [inst_1 : CommRing O]
      (emb : O →+* PadicAlgCl l), (∀ (a : O), ‖(emb : O → PadicAlgCl l) a‖ ≤ (1 : ℝ)) →
      ∀ (n : ℕ) (N : Matrix (Fin n) (Fin n) O) (c : Fin n → PadicAlgCl l) (μ : PadicAlgCl l),
        c ≠ (0 : Fin n → PadicAlgCl l) →
        Matrix.mulVec (Matrix.map N (⇑emb : O → PadicAlgCl l)) c = μ • c → ‖μ‖ ≤ (1 : ℝ) := by
  intro l _ O _ emb hemb n N c μ hc h
  exact norm_eigenvalue_le_one_of_entries _ (fun i j => hemb (N i j)) c μ hc h

end GlobalTheory.EigenvalueNormAtMostOne
end

