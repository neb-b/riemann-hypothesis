module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasicOpenEqZeroOfMemIInfPowSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import GroundTheory.GlobalFields.Artin.LogCharpoly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPrimeLocalizationDvr
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_under_eq_of_mem_associatedPrimes_of_surjective {A A' M : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] [AddCommGroup M] [Module A M] [Module A' M]
    [IsScalarTower A A' M] (hs : Function.Surjective (algebraMap A A')) {q : Ideal A}
    (hq : q ∈ associatedPrimes A M) : ∃ q' ∈ associatedPrimes A' M, q'.under A = q := by
  obtain ⟨hp, v, hv⟩ := hq
  set q' : Ideal A' := ((⊥ : Submodule A' M).colon {v}).radical with hq'
  have hunder : q'.under A = q := by
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hv]
    simp only [hq', Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot,
      ← map_pow, algebraMap_smul]
  have hmap : q.map (algebraMap A A') = q' := by
    rw [← hunder]
    exact Ideal.map_comap_of_surjective _ hs q'
  have hker : RingHom.ker (algebraMap A A') ≤ q := fun a ha ↦ by
    rw [hv]
    refine Ideal.le_radical ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, ← algebraMap_smul A',
      RingHom.mem_ker.1 ha, zero_smul]
  have hprime : q'.IsPrime := hmap ▸ Ideal.map_isPrime_of_surjective hs hker
  exact ⟨q', ⟨hprime, v, rfl⟩, hunder⟩

theorem exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span {S : Type*} [CommRing S]
    [IsLocalRing S] [IsNoetherianRing S] {t : S} (ht : maximalIdeal S = Ideal.span {t})
    (hreg : IsSMulRegular S t) : ∃ _ : IsDomain S, IsDiscreteValuationRing S := by
  have hfac : ∀ y : S, y ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ y = t ^ n * u := by
    intro y hy
    have hinf : (⨅ i : ℕ, maximalIdeal S ^ i) = ⊥ :=
      Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'
    have hex : ∃ n : ℕ, y ∉ maximalIdeal S ^ n := by
      by_contra! h
      exact hy (by simpa [hinf] using (Submodule.mem_iInf _).2 h)
    classical
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_succ_of_ne_zero fun h0 ↦ ?_
      have := Nat.find_spec hex
      rw [h0] at this
      simp at this
    have h1 : y ∈ maximalIdeal S ^ k := by
      have := Nat.find_min hex (m := k) (by omega)
      simpa using this
    have h2 : y ∉ maximalIdeal S ^ (k + 1) := hk ▸ Nat.find_spec hex
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    obtain ⟨u, rfl⟩ := h1
    refine ⟨k, u, ?_, rfl⟩
    by_contra hu
    apply h2
    have hum : u ∈ maximalIdeal S := (mem_maximalIdeal u).2 hu
    rw [ht, Ideal.mem_span_singleton] at hum
    obtain ⟨c, rfl⟩ := hum
    rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ⟨c, by ring⟩
  have hnzd : NoZeroDivisors S := by
    refine ⟨fun {a b} hab ↦ ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨m, u, hu, rfl⟩ := hfac a hne.1
    obtain ⟨n, v, hv, rfl⟩ := hfac b hne.2
    have h0 : t ^ (m + n) • (u * v) = 0 := by
      rw [smul_eq_mul, pow_add]
      linear_combination hab
    have h3 : u * v = 0 := (hreg.pow (m + n)).right_eq_zero_of_smul h0
    exact (hu.mul hv).ne_zero h3
  have hdom : IsDomain S := NoZeroDivisors.to_isDomain S
  refine ⟨hdom, ?_⟩
  have ht0 : t ≠ 0 := fun h ↦ by
    have : IsSMulRegular S (0 : S) := h ▸ hreg
    exact one_ne_zero (this.right_eq_zero_of_smul (zero_smul S (1 : S)))
  have hf : ¬ IsField S := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ht]
    simpa using ht0
  refine ((IsDiscreteValuationRing.TFAE S hf).out 5 1).mp ?_
  exact ⟨t, ht⟩

theorem exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 →
      (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) →
      ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) →
        ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by
  intro A R _ _ _ _ _ _ _ _ x hx hred P _ hP
  set I : Ideal A := Ideal.span {x} with hI
  have hIR : Ideal.span {algebraMap A R x} = I.map (algebraMap A R) := by
    rw [hI, Ideal.map_span, Set.image_singleton]
  rw [hIR] at hP
  set q : Ideal A := P.under A with hqdef
  have hqp : q.IsPrime := Ideal.IsPrime.under A P

  have hxq : x ∈ q := by
    have h1 := IsAssociatedPrime.annihilator_le hP
    rw [Submodule.annihilator_top, Ideal.annihilator_quotient] at h1
    exact h1 (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self x))

  have hqA : q ∈ associatedPrimes A (A ⧸ I) := by
    have h0 : q ∈ associatedPrimes A (R ⧸ I.map (algebraMap A R)) :=
      under_mem_associatedPrimes (A := A) hP
    let e : (R ⧸ I.map (algebraMap A R)) ≃ₗ[A] (A ⧸ I) ⊗[A] R :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R I).toLinearEquiv.restrictScalars A) ≪≫ₗ
        TensorProduct.comm A R (A ⧸ I)
    rw [LinearEquiv.AssociatedPrimes.eq e] at h0
    obtain ⟨q', hq', hu⟩ := exists_under_eq_of_mem_associatedPrimes_of_surjective (A' := A ⧸ I)
      Ideal.Quotient.mk_surjective h0
    have h2 : q' ∈ associatedPrimes (A ⧸ I) (A ⧸ I) := associatedPrimes_subset_of_flat hq'
    rw [← hu]
    exact under_mem_associatedPrimes (A := A) h2
  have hheight : q.height = 1 := height_eq_one_of_mem_associatedPrimes hx hqA

  have hPq : P ∈ associatedPrimes R (R ⧸ q.map (algebraMap A R)) := by
    rw [LinearEquiv.AssociatedPrimes.eq
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R I).toLinearEquiv] at hP
    rw [LinearEquiv.AssociatedPrimes.eq
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R q).toLinearEquiv]
    exact mem_associatedPrimes_tensor_quotient_under (A := A) hP

  obtain ⟨z, hzP, hz⟩ : ∃ z ∉ P, ∀ p ∈ P, p * z ∈ q.map (algebraMap A R) := by
    obtain ⟨-, w, hw⟩ := isAssociatedPrime_iff.mp hPq
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hmem : ∀ p, p ∈ P ↔ p * z ∈ q.map (algebraMap A R) := fun p ↦ by
      rw [hw, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    refine ⟨z, fun hzP ↦ ?_, fun p hp ↦ (hmem p).1 hp⟩
    have := hred q hqp hxq
    have h2 : Ideal.Quotient.mk (q.map (algebraMap A R)) z ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two]
      exact (hmem z).1 hzP
    have h3 : z ∈ q.map (algebraMap A R) :=
      Ideal.Quotient.eq_zero_iff_mem.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
    exact Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one P).2 ((hmem 1).2 (by simpa using h3)))

  obtain ⟨t, htq, ht⟩ : ∃ t ∈ q, ∀ b ∈ q, ∃ v ∉ q, ∃ c, v * b = t * c := by
    let B := Localization.AtPrime q
    have hdvr : IsDiscreteValuationRing B := isDiscreteValuationRing_of_height_eq_one q hheight B
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl ϖ
    have hmax : maximalIdeal B = Ideal.span {IsLocalization.mk' B a s} := hϖ.maximalIdeal_eq
    have h1 : IsLocalization.mk' B a s * algebraMap A B s = algebraMap A B a :=
      IsLocalization.mk'_spec B a s
    have haq : a ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff B q a, ← h1, hmax]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    refine ⟨a, haq, fun b hb ↦ ?_⟩
    have hbB := (IsLocalization.AtPrime.to_map_mem_maximal_iff B q b).2 hb
    rw [hmax, Ideal.mem_span_singleton] at hbB
    obtain ⟨d, hd⟩ := hbB
    obtain ⟨c, u, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl d
    have h2 : IsLocalization.mk' B c u * algebraMap A B u = algebraMap A B c :=
      IsLocalization.mk'_spec B c u
    refine ⟨s * u, q.primeCompl.mul_mem s.2 u.2, c, ?_⟩
    apply IsLocalization.injective B q.primeCompl_le_nonZeroDivisors
    simp only [map_mul]
    linear_combination (algebraMap A B s * algebraMap A B u) * hd +
      (IsLocalization.mk' B c u * algebraMap A B u) * h1 + algebraMap A B a * h2

  let S := Localization.AtPrime P
  have hflatRS : Module.Flat R S := IsLocalization.flat S P.primeCompl
  have hflatAS : Module.Flat A S := Module.Flat.trans A R S
  have hnoeth : IsNoetherianRing S := IsLocalization.isNoetherianRing P.primeCompl S inferInstance
  have ht0 : t ≠ 0 := by
    rintro rfl
    obtain ⟨v, hv, c, hvc⟩ := ht x hxq
    rw [zero_mul] at hvc
    rcases mul_eq_zero.1 hvc with h | h
    · exact hv (h ▸ q.zero_mem)
    · exact hx h
  have hreg : IsSMulRegular S (algebraMap A S t) := (IsSMulRegular.of_ne_zero ht0).of_flat
  have hunitS : ∀ r ∉ P, IsUnit (algebraMap R S r) := fun r hr ↦
    IsLocalization.map_units S (⟨r, hr⟩ : P.primeCompl)
  have hqS : ∀ b ∈ q, algebraMap A S b ∈ Ideal.span {algebraMap A S t} := fun b hb ↦ by
    obtain ⟨v, hv, c, hvc⟩ := ht b hb
    have hu : IsUnit (algebraMap A S v) := by
      rw [IsScalarTower.algebraMap_apply A R S]
      exact hunitS _ hv
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul, hvc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hqRS : q.map (algebraMap A R) ≤ (Ideal.span {algebraMap A S t}).comap (algebraMap R S) :=
    Ideal.map_le_iff_le_comap.2 fun b hb ↦ by
      rw [Ideal.mem_comap, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact hqS b hb
  have hmaxS : maximalIdeal S = Ideal.span {algebraMap A S t} := by
    refine le_antisymm ?_ ?_
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro p hp
      have h := hqRS (hz p hp)
      rw [Ideal.mem_comap, map_mul] at h
      exact (Ideal.mul_unit_mem_iff_mem _ (hunitS z hzP)).1 h
    · rw [Ideal.span_singleton_le_iff_mem, IsScalarTower.algebraMap_apply A R S,
        IsLocalization.AtPrime.to_map_mem_maximal_iff S P]
      exact htq
  exact exists_isDomain_isDiscreteValuationRing_of_maximalIdeal_eq_span hmaxS hreg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyDvdPowFinrankOfAevalEqZero
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent

namespace GlobalTheory.CharpolyDvd

theorem matrix_charpoly_dvd_pow {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (G : K[X]) (hG : aeval M G = 0) :
    M.charpoly ∣ G ^ Fintype.card ι := by
  classical
  by_cases h0 : G = 0
  · subst h0
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · have : M.charpoly = 1 := by
        apply Polynomial.eq_one_of_monic_natDegree_zero M.charpoly_monic
        rw [Matrix.charpoly_natDegree_eq_dim, h]
      rw [this, h, pow_zero]
    · rw [zero_pow h.ne']
      exact dvd_zero _
  let Ω := AlgebraicClosure K
  let f := algebraMap K Ω
  rw [← Polynomial.map_dvd_map' f, Polynomial.map_pow, ← Matrix.charpoly_map]
  set N := M.map f with hNdef
  have hN : aeval N (G.map f) = 0 := by
    rw [aeval_map_algebraMap]
    have := congrArg (AlgHom.mapMatrix (m := ι) (Algebra.ofId K Ω)) hG
    rw [← aeval_algHom_apply, map_zero] at this
    exact this
  have hG0 : G.map f ≠ 0 := Polynomial.map_ne_zero h0
  have hq0 : G.map f ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hG0
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots N.charpoly_monic.ne_zero ?_
  rw [roots_pow, Multiset.le_iff_count]
  intro μ
  rw [Multiset.count_nsmul]
  by_cases hμ : μ ∈ N.charpoly.roots
  · have h1 : μ ∈ spectrum Ω N := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact isRoot_of_mem_roots hμ
    have h2 := spectrum.subset_polynomial_aeval N (G.map f) ⟨μ, h1, rfl⟩
    rw [hN] at h2
    have h3 : (G.map f).eval μ = 0 := by
      by_contra hne
      exact (spectrum.mem_iff.1 h2)
        (by simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix ι ι Ω)))
    have h4 : 1 ≤ (G.map f).roots.count μ :=
      Multiset.one_le_count_iff_mem.2 ((mem_roots hG0).2 h3)
    calc N.charpoly.roots.count μ ≤ Multiset.card N.charpoly.roots := Multiset.count_le_card _ _
      _ ≤ N.charpoly.natDegree := card_roots' _
      _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim N
      _ ≤ Fintype.card ι * (G.map f).roots.count μ := Nat.le_mul_of_pos_right _ h4
  · rw [Multiset.count_eq_zero.2 hμ]
    exact Nat.zero_le _

theorem charpoly_dvd_pow_finrank {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (G : K[X]) (hG : aeval f G = 0) :
    f.charpoly ∣ G ^ Module.finrank K V := by
  classical
  let b := Module.finBasis K V
  have hM : aeval (LinearMap.toMatrix b b f) G = 0 := by
    have := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom f G
    rw [hG, map_zero] at this
    have e : LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f := by
      ext i j
      simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [← e]
    exact this
  have := matrix_charpoly_dvd_pow _ G hM
  rwa [LinearMap.charpoly_toMatrix, Fintype.card_fin] at this

theorem main : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V :=
  fun f G hG => charpoly_dvd_pow_finrank f G hG

end GlobalTheory.CharpolyDvd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyMulBaseChangeFiniteMapOfIsPushout
section
noncomputable section

namespace GlobalTheory.NormalDescent

open CategoryTheory Polynomial TensorProduct

theorem charK_map_of_isPushout {A B A' B' K K' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Field K] [Field K'] [Algebra A K] [Algebra A' K'] (φ : A →+* B) (α : A →+* A') (β : B →+* B')
    (φ' : A' →+* B')
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (hφ : φ.Finite) (hφ' : φ'.Finite) (ι : K →+* K')
    (hι : ∀ a : A, ι (algebraMap A K a) = algebraMap A' K' (α a)) (b : B) :
    charK φ' hφ' K' (β b) = (charK φ hφ K b).map ι := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have P : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  have hb : IsBaseChange A' (IsScalarTower.toAlgHom A B B').toLinearMap := P.symm.out
  haveI : Module.Finite A B := hφ
  haveI : Module.Finite A' B' := hφ'
  letI : Algebra K K' := ι.toAlgebra
  letI : Algebra A K' := (ι.comp (algebraMap A K)).toAlgebra
  haveI : IsScalarTower A K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A A' K' := IsScalarTower.of_algebraMap_eq fun a => hι a
  let e : K' ⊗[K] (K ⊗[A] B) ≃ₗ[K'] K' ⊗[A'] B' :=
    AlgebraTensorModule.cancelBaseChange A K K' K' B ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange A A' K' K' B).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl K' K') hb.equiv
  unfold charK
  change (Algebra.lmul K' (K' ⊗[A'] B') (1 ⊗ₜ β b)).charpoly =
    (Algebra.lmul K (K ⊗[A] B) (1 ⊗ₜ b)).charpoly.map (algebraMap K K')
  rw [← LinearMap.charpoly_baseChange, ← e.charpoly_conj]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨t, rfl⟩ := e.surjective y
  simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add (f := _), hs, ht]
  | tmul c' u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [tmul_add, map_add (f := _), hs, ht]
    | tmul c x =>
      simp [e, IsBaseChange.equiv_tmul]
      rfl

end GlobalTheory.NormalDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZer
section
namespace GlobalTheory

open Polynomial

theorem charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero
    {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ}
    (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R)
    (h : ∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) :
    M.charpolyRev * N.charpolyRev = 1 := by
  set f := M.charpolyRev
  set g := N.charpolyRev
  have hS : (PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
      (PowerSeries.mk fun k => (N ^ (k + 1)).trace) = 0 := by
    ext k
    simp [h (k + 1) (Nat.le_add_left 1 k)]
  have hd : derivative (f * g) = 0 := by
    apply Polynomial.coe_injective
    rw [Polynomial.derivative_mul, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_mul,
      GroundTheory.Global.coe_derivative_charpolyRev, GroundTheory.Global.coe_derivative_charpolyRev,
      Polynomial.coe_zero]
    calc -(f : PowerSeries R) * PowerSeries.mk (fun k => (M ^ (k + 1)).trace) * (g : PowerSeries R) +
          (f : PowerSeries R) * (-(g : PowerSeries R) * PowerSeries.mk fun k => (N ^ (k + 1)).trace)
        = -((f : PowerSeries R) * (g : PowerSeries R)) *
          ((PowerSeries.mk fun k => (M ^ (k + 1)).trace) +
            (PowerSeries.mk fun k => (N ^ (k + 1)).trace)) := by ring
      _ = 0 := by rw [hS, mul_zero]
  have h0 : (f * g).coeff 0 = 1 := by
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev, Matrix.eval_charpolyRev,
      mul_one]
  ext k
  rcases k with _ | k
  · rw [h0, Polynomial.coeff_one_zero]
  · have hk := congrArg (fun r => r.coeff k) hd
    simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hk
    have hu : IsUnit ((k : R) + 1) := by
      have : ((k : R) + 1) = algebraMap K R ((k : K) + 1) := by simp
      rw [this]
      exact (IsUnit.mk0 _ (by exact_mod_cast Nat.succ_ne_zero k)).map _
    rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero k)]
    exact hu.mul_left_eq_zero.mp hk

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorProdFstStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_fst_eq_of_integral_of_conductor : ∀ (R S' S : Type) [CommRing R] [CommRing S'] [CommRing S] (e : S ≃+* R × S') (d : S), (∀ c : FractionRing S, IsIntegral S c → ∃ s : S, algebraMap S (FractionRing S) s = algebraMap S (FractionRing S) d * c) → ∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) (e d).1 * c := by
  first | exact @GlobalTheory.conductor_prod_fst | exact GlobalTheory.conductor_prod_fst | (intros; apply GlobalTheory.conductor_prod_fst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameterStatement
section
open MeasureTheory Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_of_continuous_oneParameter_hom : ∀ (A : Type) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (T : ℝ → A), Continuous T → T 0 = 1 → (∀ s t, T (s + t) = T s * T t) → ContDiff ℝ ∞ T := by
  first | exact @GlobalTheory.contDiff_of_continuous_oneParameter | exact GlobalTheory.contDiff_of_continuous_oneParameter | (intros; apply GlobalTheory.contDiff_of_continuous_oneParameter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConvexAndDifferentiableOnTsumCexp
section
open Complex

namespace GlobalTheory.ExpSeries

theorem convexOn_norm_mul_cexp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (c : ℂ) (L : V →ₗ[ℂ] ℂ) :
    ConvexOn ℝ Set.univ (fun z : V => ‖c * cexp (L z)‖) := by
  have h := (convexOn_exp.comp_linearMap
    (Complex.reLm ∘ₗ (L.restrictScalars ℝ))).smul (norm_nonneg c)
  rw [Set.preimage_univ] at h
  have e : (fun z : V => ‖c * cexp (L z)‖) = fun z : V =>
      ‖c‖ • (Real.exp ∘ ⇑(Complex.reLm ∘ₗ (L.restrictScalars ℝ))) z := by
    funext z
    simp [Complex.norm_exp]
  rw [e]
  exact h

theorem convex_and_differentiableOn_tsum_cexp :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : Type)
      (c : J → ℂ) (L : J → V →ₗ[ℂ] ℂ),
      Convex ℝ {z : V | Summable fun j => c j * cexp (L j z)} ∧
      DifferentiableOn ℂ (fun z : V => ∑' j, c j * cexp (L j z))
        (interior {z : V | Summable fun j => c j * cexp (L j z)}) := by
  intro V _ _ _ J c L
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [← summable_norm_iff] at hx hy ⊢
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
      ((hx.mul_left a).add (hy.mul_left b))
    exact (convexOn_norm_mul_cexp (c j) (L j)).2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  · intro z0 hz0
    have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
    obtain ⟨b, hb0, hb⟩ := exists_mem_interior_convexHull_affineBasis
      (mem_interior_iff_mem_nhds.1 hz0)
    have hsum : Summable fun j => ∑ i, ‖c j * cexp (L j (b i))‖ := by
      refine summable_sum fun i _ => ?_
      have : b i ∈ {z : V | Summable fun j => c j * cexp (L j z)} :=
        hb (subset_convexHull ℝ _ ⟨i, rfl⟩)
      exact summable_norm_iff.2 this
    have hd := (GlobalTheory.SCV.differentiableOn_tsum_of_normal_on_compacts
      (F := fun j z => c j * cexp (L j z)) (U := interior (convexHull ℝ (Set.range b)))
      isOpen_interior
      (fun j => ((((L j).toContinuousLinearMap.differentiable).cexp).const_mul
        (c j)).differentiableOn)
      (fun K hK _ => ⟨_, hsum, fun j z hz => by
        obtain ⟨y, ⟨i, rfl⟩, hy⟩ := (convexOn_norm_mul_cexp (c j) (L j)).exists_ge_of_mem_convexHull
          (Set.subset_univ _) (interior_subset (hK hz))
        exact hy.trans (Finset.single_le_sum (f := fun i => ‖c j * cexp (L j (b i))‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ i))⟩)).1
    exact (hd.differentiableAt (isOpen_interior.mem_nhds hb0)).differentiableWithinAt

end GlobalTheory.ExpSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInFiniteDomainTraceMemStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_of_integral_with_trace_in_base : ∀ (T C F K : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C], ∃ (n : ℕ) (b : Module.Basis (Fin n) F K), (∀ i, ∃ c : C, algebraMap C K c = b i) ∧ ∀ i j, ∃ t : T, algebraMap T F t = Algebra.trace F K (b i * b j) := by
  first | exact @GlobalTheory.exists_basis_in_finite_domain_trace_mem | exact GlobalTheory.exists_basis_in_finite_domain_trace_mem | (intros; apply GlobalTheory.exists_basis_in_finite_domain_trace_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonNonzeroOfPolynomialOnRealLinesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (ι : Type) [Finite ι] (f : ι → V → ℂ), (∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ)) → (∀ i, ∃ v, f i v ≠ 0) → ∃ v, ∀ i, f i v ≠ 0 := by
  first | exact @GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | exact GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | (intros; apply GlobalTheory.exists_common_nonzero_of_polynomial_on_lines <;> assumption)
end

