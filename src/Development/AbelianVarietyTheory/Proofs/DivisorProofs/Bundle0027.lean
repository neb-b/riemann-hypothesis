module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingLocalDomainEqMulMaximal
section
open IsLocalRing Polynomial

namespace GlobalTheory.Izumi

theorem exists_dominating_of_residue_map {R S : Type} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] (j : R →+* S) (hj : Function.Injective j)
    (φ : S →+* ResidueField R) (hφ : ∀ r, φ (j r) = residue R r) (f G : R) (u : S)
    (hu : φ u = 0) (hf : j f = j G * u) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
      (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧
      (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨j r, hφ r⟩
  haveI hmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  let B := Localization.AtPrime (RingHom.ker φ)
  have hmem : ∀ s : S, algebraMap S B s ∈ maximalIdeal B ↔ φ s = 0 := fun s => by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff B (RingHom.ker φ), RingHom.mem_ker]
  haveI : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing (RingHom.ker φ).primeCompl B inferInstance
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap S B).comp j, ?_, ⟨fun r hr => ?_⟩, fun b => ?_, algebraMap S B u,
    (hmem u).2 hu, ?_⟩
  · exact (IsLocalization.injective B (RingHom.ker φ).primeCompl_le_nonZeroDivisors).comp hj
  · by_contra h
    have h1 : φ (j r) = 0 := by
      rw [hφ, residue_eq_zero_iff]; exact h
    exact (hmem _).2 h1 hr
  · obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker φ).primeCompl b
    have ht : φ t ≠ 0 := t.2
    obtain ⟨r, hr⟩ := residue_surjective (φ s / φ t)
    refine ⟨r, ?_⟩
    have hunit : IsUnit (algebraMap S B t) := IsLocalization.map_units B t
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit, mul_sub]
    dsimp only
    rw [IsLocalization.mk'_spec', RingHom.comp_apply, ← map_mul, ← map_sub, hmem, map_sub,
      map_mul, hφ, hr, mul_div_cancel₀ _ ht, sub_self]
  · simp [hf]

theorem coeff_zero_mem_maximalIdeal_of_aeval_div {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsIntegrallyClosed R] (f G : R) (h : G ∉ Ideal.span {f}) (P : R[X])
    (hP : aeval (algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G) P = 0) :
    P.coeff 0 ∈ maximalIdeal R := by
  by_contra hc
  have hunit : IsUnit (P.coeff 0) := by
    simpa [mem_maximalIdeal] using hc
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hG : G ≠ 0 := by rintro rfl; exact h (zero_mem _)
  have hG' : algebraMap R (FractionRing R) G ≠ 0 := (map_ne_zero_iff _ hinj).2 hG
  have hf : f ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, ← coeff_zero_eq_aeval_zero'] at hP
    exact hunit.ne_zero ((map_eq_zero_iff _ hinj).1 hP)
  have hf' : algebraMap R (FractionRing R) f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
  set u := algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G with hu
  have hu0 : u ≠ 0 := div_ne_zero hf' hG'
  letI := invertibleOfNonzero hu0
  have hrev : aeval (⅟u) P.reverse = 0 := by
    rw [aeval_def, eval₂_reverse_eq_zero_iff]; exact hP
  have hint := isIntegral_leadingCoeff_smul P.reverse (⅟u) hrev
  rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hunit.ne_zero] at hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  apply h
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, Ideal.mem_span_singleton']
  refine ⟨r, hinj ?_⟩
  rw [map_mul, map_mul, hr, invOf_eq_inv, hu, Algebra.smul_def]
  field_simp

theorem exists_dominating_eq_mul_of_not_mem_span :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
        (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧
        (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  intro R _ _ _ _ _ f G h
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hG : G ≠ 0 := by rintro rfl; exact h (zero_mem _)
  have hG' : algebraMap R (FractionRing R) G ≠ 0 := (map_ne_zero_iff _ hinj).2 hG
  let u := algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G
  let e : R[X] →+* FractionRing R := (aeval u : R[X] →ₐ[R] FractionRing R)
  have he : ∀ P, e P = aeval u P := fun _ => rfl
  haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  let φ : (R[X] ⧸ RingHom.ker e) →+* ResidueField R :=
    Ideal.Quotient.lift _ ((residue R).comp constantCoeff) fun P hP => by
      rw [RingHom.comp_apply, residue_eq_zero_iff]
      exact coeff_zero_mem_maximalIdeal_of_aeval_div f G h P hP
  refine exists_dominating_of_residue_map ((Ideal.Quotient.mk (RingHom.ker e)).comp C) ?_ φ ?_
    f G (Ideal.Quotient.mk _ X) ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker, he, aeval_C] at hr
    exact (map_eq_zero_iff _ hinj).1 hr
  · intro r; simp [φ]
  · simp [φ]
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← map_mul, Ideal.Quotient.eq, RingHom.mem_ker, he]
    simp only [map_sub, map_mul, aeval_C, aeval_X, u]
    field_simp
    ring

end GlobalTheory.Izumi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramForm
section
namespace GlobalTheory

theorem parallelogram_zsmul {E : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (k : ℤ) (f : E) :
    Q (k • f) = k ^ 2 * Q f := by
  have h0 : Q 0 = 0 := by
    have := hQ 0 0
    simp only [add_zero, sub_zero] at this
    omega
  have hneg : ∀ g, Q (-g) = Q g := by
    intro g
    have := hQ 0 g
    simp only [zero_add, zero_sub, h0] at this
    omega
  have hnat : ∀ n : ℕ, Q ((n : ℤ) • f) = (n : ℤ) ^ 2 * Q f ∧
      Q (((n : ℤ) + 1) • f) = ((n : ℤ) + 1) ^ 2 * Q f := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have h := hQ (((n : ℤ) + 1) • f) f
      have e1 : ((n : ℤ) + 1) • f + f = (((n + 1 : ℕ) : ℤ) + 1) • f := by
        push_cast; module
      have e2 : ((n : ℤ) + 1) • f - f = (n : ℤ) • f := by module
      rw [e1, e2, ih.1, ih.2] at h
      push_cast at h ⊢
      linear_combination h
  obtain ⟨n, rfl | rfl⟩ := k.eq_nat_or_neg
  · exact (hnat n).1
  · rw [neg_smul, hneg, (hnat n).1]; ring

theorem parallelogram_sum_le {E ι : Type} [AddCommGroup E] (Q : E → ℤ)
    (hQ : ∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) (hpos : ∀ f, 0 ≤ Q f)
    (u : ι → E) (s : Finset ι) :
    ∃ C : ℕ, ∀ (z : ι → ℤ) (M : ℤ), (∀ i, |z i| ≤ M) →
      Q (∑ i ∈ s, z i • u i) ≤ C * M ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0, fun z M _ => ?_⟩
    have := parallelogram_zsmul Q hQ 0 0
    simp at this
    simp [this]
  | insert a s ha ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨2 * (Q (u a)).toNat + 2 * C, fun z M hz => ?_⟩
    rw [Finset.sum_insert ha]
    have h1 := hQ (z a • u a) (∑ i ∈ s, z i • u i)
    have h2 := hpos (z a • u a - ∑ i ∈ s, z i • u i)
    have h3 := hC z M hz
    have h4 := parallelogram_zsmul Q hQ (z a) (u a)
    have h5 : z a ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs (z a)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hz a) 2
    have h6 := mul_le_mul_of_nonneg_right h5 (hpos (u a))
    push_cast
    rw [Int.toNat_of_nonneg (hpos (u a))]
    nlinarith

theorem exists_dvd_coords_of_definite_form :
    ∀ (E : Type) [AddCommGroup E] (H : AddSubgroup E) (Q : E → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f ∈ H, Q f = 0 → f = 0) → ∀ (n : ℕ) (u : Fin n → E), (∀ i, u i ∈ H) → LinearIndependent ℤ u → ∃ e : ℕ, 0 < e ∧ ∀ (k : ℕ) (m : Fin n → ℤ) (h : E), h ∈ H → k • h = ∑ i, m i • u i → ∀ i, (k : ℤ) ∣ e * m i := by
  intro E _ H Q hQ hpos hdef n u hu hli
  obtain ⟨C, hC⟩ := parallelogram_sum_le Q hQ hpos u Finset.univ
  rw [Fintype.linearIndependent_iff] at hli
  set R : ℕ := C + 1 with hR
  refine ⟨(R ^ n).factorial, Nat.factorial_pos _, fun k m h hh hk => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · intro i
    have := hli m (by simpa using hk.symm) i
    simp [this]
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hR0 : (0 : ℤ) < R := by positivity
  obtain ⟨a, ha, b, hb, hab, hf⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (R ^ n + 1))
    (t := Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) R))
    (f := fun (j : ℕ) (i : Fin n) => ((R : ℤ) * (((j : ℤ) * m i) % k)) / k)
    (by simp [Fintype.card_piFinset])
    (by
      intro j _
      simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Ico]
      intro i
      have h1 := Int.emod_nonneg ((j : ℤ) * m i) hk0.ne'
      have h2 := Int.emod_lt_of_pos ((j : ℤ) * m i) hk0
      refine ⟨Int.ediv_nonneg (by positivity) hk0.le, ?_⟩
      apply Int.ediv_lt_of_lt_mul hk0
      exact mul_lt_mul_of_pos_left h2 hR0)
  set y : Fin n → ℤ := fun i => ((a : ℤ) * m i) % k - ((b : ℤ) * m i) % k with hy
  set q : Fin n → ℤ := fun i => ((a : ℤ) * m i) / k - ((b : ℤ) * m i) / k with hq
  have hyq : ∀ i, y i = ((a : ℤ) - b) * m i - k * q i := by
    intro i
    simp only [hy, hq, Int.emod_def]
    ring
  have hbound : ∀ i, |(R : ℤ) * y i| ≤ k := by
    intro i
    have e := congrFun hf i
    beta_reduce at e
    have a1 := Int.emod_nonneg ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0.ne'
    have a2 := Int.emod_lt_of_pos ((R : ℤ) * (((a : ℤ) * m i) % k)) hk0
    have b1 := Int.emod_nonneg ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0.ne'
    have b2 := Int.emod_lt_of_pos ((R : ℤ) * (((b : ℤ) * m i) % k)) hk0
    rw [Int.emod_def] at a1 a2 b1 b2
    rw [e] at a1 a2
    simp only [hy]
    rw [abs_le, mul_sub]
    constructor <;> linarith
  set w : E := ((a : ℤ) - b) • h - ∑ i, q i • u i with hw
  have hwH : w ∈ H := H.sub_mem (H.zsmul_mem hh _) (H.sum_mem fun i _ => H.zsmul_mem (hu i) _)
  have hkw : (k : ℤ) • w = ∑ i, y i • u i := by
    rw [hw, smul_sub, smul_comm, natCast_zsmul h k, hk, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hyq i, smul_smul, smul_smul, sub_smul]
  have hRkw : ((R : ℤ) * k) • w = ∑ i, ((R : ℤ) * y i) • u i := by
    rw [mul_smul, hkw, Finset.smul_sum]
    simp only [smul_smul]
  have hle := hC (fun i => (R : ℤ) * y i) k hbound
  rw [← hRkw, parallelogram_zsmul Q hQ] at hle
  have hQw : Q w = 0 := by
    by_contra hne
    have h1 : 1 ≤ Q w := by have := hpos w; omega
    have h2 : ((R : ℤ) * k) ^ 2 ≤ ((R : ℤ) * k) ^ 2 * Q w := le_mul_of_one_le_right (by positivity) h1
    have h3 : (C : ℤ) < (R : ℤ) ^ 2 := by
      rw [hR]; push_cast; nlinarith [Int.natCast_nonneg C]
    have h4 := mul_lt_mul_of_pos_right h3 (show (0 : ℤ) < (k : ℤ) ^ 2 by positivity)
    rw [mul_pow] at h2 hle
    linarith
  have hw0 := hdef w hwH hQw
  rw [hw0, smul_zero] at hkw
  intro i
  have hyi := hli y hkw.symm i
  have hd : (k : ℤ) ∣ ((a : ℤ) - b) * m i := ⟨q i, by have := hyq i; linarith⟩
  refine hd.trans (mul_dvd_mul_right ?_ _)
  rw [← Int.natAbs_dvd, Int.natCast_dvd_natCast]
  rw [Finset.mem_range] at ha hb
  apply Nat.dvd_factorial
  · omega
  · omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingBijectiveLocalizedModuleMapOfRank
section
namespace GlobalTheory

open Module

theorem localizedModule_map_injective_of_surjective_of_rankAtStalk
    {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q]
    (r : ℕ) (P : PrimeSpectrum R) (hP : Module.rankAtStalk Q P = r) (φ : (Fin r → R) →ₗ[R] Q)
    (hs : Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl φ)) :
    Function.Injective (LocalizedModule.map P.asIdeal.primeCompl φ) := by
  haveI : Nontrivial R := nontrivial_of_ne (0 : R) 1 fun h =>
    P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (h ▸ P.asIdeal.zero_mem))
  haveI : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl Q) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl (Fin r → R)) := Module.free_of_flat_of_isLocalRing
  have h1 : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl (Fin r → R)) = r := by
    have := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := R) (M := Fin r → R)) P
    rw [Module.finrank_fin_fun] at this
    exact this
  have h2 : Module.finrank (Localization.AtPrime P.asIdeal)
      (LocalizedModule P.asIdeal.primeCompl Q) = r := hP
  let e := LinearEquiv.ofFinrankEq _ _ (h1.trans h2.symm)
  exact OrzechProperty.injective_of_surjective_of_injective e.toLinearMap _ e.injective hs

theorem exists_smul_mem_range_of_surjective_localizedModule_map
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    [Module.Finite R Q] (P : Ideal R) [P.IsPrime] (φ : M →ₗ[R] Q)
    (hs : Function.Surjective (LocalizedModule.map P.primeCompl φ)) :
    ∃ f ∉ P, ∀ q : Q, f • q ∈ LinearMap.range φ := by
  have key : ∀ g : Q, ∃ a ∈ P.primeCompl, a • g ∈ LinearMap.range φ := by
    intro g
    obtain ⟨y, hy⟩ := hs (LocalizedModule.mk g 1)
    induction y using LocalizedModule.induction_on with
    | h x t =>
      rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hy
      obtain ⟨u, hu⟩ := hy
      refine ⟨(u : R) * t, P.primeCompl.mul_mem u.2 t.2, ⟨(u : R) • x, ?_⟩⟩
      rw [map_smul, mul_smul]
      simpa [Submonoid.smul_def] using hu
  classical
  choose a ha hga using key
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := Q)
  refine ⟨∏ g ∈ s, a g, fun h => ?_, ?_⟩
  · exact (Submonoid.prod_mem P.primeCompl fun g _ => ha g) h
  · have hle : Submodule.span R (s : Set Q) ≤
        (LinearMap.range φ).comap (LinearMap.lsmul R Q (∏ g ∈ s, a g)) := by
      rw [Submodule.span_le]
      intro g hg
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
      rw [← Finset.prod_erase_mul s a hg, mul_smul]
      exact Submodule.smul_mem _ _ (hga g)
    intro q
    have := hle (hs ▸ Submodule.mem_top : q ∈ Submodule.span R (s : Set Q))
    simpa using this

theorem localizedModule_map_surjective_of_smul_mem_range
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (S : Submonoid R) (φ : M →ₗ[R] Q) (f : R) (hf : f ∈ S)
    (h : ∀ q : Q, f • q ∈ LinearMap.range φ) :
    Function.Surjective (LocalizedModule.map S φ) := by
  intro y
  induction y using LocalizedModule.induction_on with
  | h q s =>
    obtain ⟨x, hx⟩ := h q
    refine ⟨LocalizedModule.mk x (⟨f, hf⟩ * s), ?_⟩
    rw [LocalizedModule.map_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    rw [hx]
    simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    exact smul_comm _ _ _

theorem exists_pow_smul_eq_zero_of_localizedModule_map_injective
    {R M Q : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q]
    (φ : M →ₗ[R] Q) (f : R)
    (h : ∀ (P : Ideal R) [P.IsPrime], f ∉ P →
      Function.Injective (LocalizedModule.map P.primeCompl φ))
    (k : M) (hk : φ k = 0) : ∃ n : ℕ, f ^ n • k = 0 := by
  by_contra hne
  push_neg at hne
  let I : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M k)
  have hd : Disjoint (I : Set R) (Submonoid.powers f : Set R) := by
    rw [Set.disjoint_left]
    rintro a ha ⟨n, rfl⟩
    exact hne n (by simpa [I] using ha)
  obtain ⟨P, hP, hIP, hPd⟩ := Ideal.exists_le_prime_disjoint I _ hd
  have hfP : f ∉ P := fun hf => Set.disjoint_left.1 hPd hf (Submonoid.mem_powers f)
  have h0 : LocalizedModule.map P.primeCompl φ (LocalizedModule.mk k 1) =
      LocalizedModule.map P.primeCompl φ 0 := by
    rw [LocalizedModule.map_mk, hk, LocalizedModule.zero_mk, map_zero]
  have h1 := h P hfP h0
  rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
  obtain ⟨u, hu⟩ := h1
  have hu' : (u : R) ∈ I := by
    simpa [I, Submonoid.smul_def] using hu
  exact u.2 (hIP hu')

theorem exists_embedding_bijective_localizedModule_map_of_rankAtStalk :
    ∀ (R Q : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Flat R Q]
      (N r : ℕ) (b : Fin N → Q), Submodule.span R (Set.range b) = ⊤ →
      (∀ P : PrimeSpectrum R, Module.rankAtStalk Q P = r) → ∀ P₀ : PrimeSpectrum R,
      ∃ (σ : Fin r ↪ Fin N) (f : R), f ∉ P₀.asIdeal ∧
        Function.Bijective (LocalizedModule.map (Submonoid.powers f)
          (Fintype.linearCombination R (b ∘ σ))) := by
  intro R Q _ _ _ _ _ N r b hspan hrank P₀
  let p := P₀.asIdeal
  haveI : Module.Free (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.FinitePresentation (Localization.AtPrime p) (LocalizedModule p.primeCompl Q) :=
    Module.finitePresentation_of_projective _ _
  let v : Fin N → LocalizedModule p.primeCompl Q := fun i => LocalizedModule.mk (b i) 1
  have hv : Submodule.span (Localization.AtPrime p) (Set.range v) = ⊤ := by
    have hle : Submodule.span R (Set.range b) ≤
        ((Submodule.span (Localization.AtPrime p) (Set.range v)).restrictScalars R).comap
          (LocalizedModule.mkLinearMap p.primeCompl Q) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    rw [eq_top_iff]
    rintro y -
    induction y using LocalizedModule.induction_on with
    | h q s =>
      have hq : LocalizedModule.mk q 1 ∈ Submodule.span (Localization.AtPrime p) (Set.range v) :=
        hle (hspan ▸ Submodule.mem_top)
      have : LocalizedModule.mk q s =
          (Localization.mk 1 s : Localization.AtPrime p) • LocalizedModule.mk q 1 := by
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ hq
  obtain ⟨κ, a, bs, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  haveI : Finite κ := Module.Finite.finite_basis bs
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [← hrank P₀, Module.rankAtStalk, Module.finrank_eq_card_basis bs]
  have ha : Function.Injective a := fun i j hij => bs.injective (by rw [hb, hb, hij])
  let eqv : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  let σ : Fin r ↪ Fin N := eqv.toEmbedding.trans ⟨a, ha⟩
  let φ : (Fin r → R) →ₗ[R] Q := Fintype.linearCombination R (b ∘ σ)
  have hs0 : Function.Surjective (LocalizedModule.map p.primeCompl φ) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← bs.span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨LocalizedModule.mk (Pi.single (eqv.symm j) 1) 1, ?_⟩
    rw [LocalizedModule.map_mk, hb]
    simp [φ, σ, v]
  obtain ⟨f, hf, hfr⟩ := exists_smul_mem_range_of_surjective_localizedModule_map p φ hs0
  refine ⟨σ, f, hf, ?_,
    localizedModule_map_surjective_of_smul_mem_range _ φ f (Submonoid.mem_powers f) hfr⟩
  have hloc : ∀ (P : Ideal R) [P.IsPrime], f ∉ P →
      Function.Injective (LocalizedModule.map P.primeCompl φ) := by
    intro P hP hfP
    exact localizedModule_map_injective_of_surjective_of_rankAtStalk r ⟨P, hP⟩ (hrank ⟨P, hP⟩) φ
      (localizedModule_map_surjective_of_smul_mem_range _ φ f hfP hfr)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  induction y using LocalizedModule.induction_on with
  | h x s =>
    rw [LocalizedModule.map_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq] at hy
    obtain ⟨u, hu⟩ := hy
    have hk : φ ((u : R) • (s : R) • x) = 0 := by
      simpa [Submonoid.smul_def, map_smul] using hu
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_localizedModule_map_injective φ f hloc _ hk
    rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨f ^ n, n, rfl⟩ * u, ?_⟩
    simp only [Submonoid.smul_def, smul_zero, Submonoid.coe_mul, mul_smul]
    exact hn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEsymmPowDivMemOfIsLocalRing
section
namespace GlobalTheory

theorem exists_esymm_pow_div_mem_of_isLocalRing : ∀ (K : Type) [Field K] (O : Subring K) [IsLocalRing O] (A : Type) [Fintype A] (x : A → K) (D k : ℕ) (c : K), 1 ≤ D → 1 ≤ k → k ∣ D → c ≠ 0 → (Finset.univ.val.map x).esymm k ^ (D / k) = c → (∀ a, x a ^ D / c ∈ O) → ∃ a, x a ≠ 0 ∧ c / x a ^ D ∈ O := by
  intro K _ O _ A _ x D k c hD hk hkD hc hce hO
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.mk O).exists_le_valuationSubring
  have hkD' : 0 < D / k := Nat.div_pos (Nat.le_of_dvd (by omega) hkD) (by omega)
  have hes : (Finset.univ.val.map x).esymm k = ∑ t ∈ (Finset.univ : Finset A).powersetCard k, ∏ b ∈ t, x b :=
    Finset.esymm_map_val x _ k
  rcases isEmpty_or_nonempty A with hA | hA
  · exfalso
    apply hc
    rw [← hce, hes, Finset.powersetCard_eq_empty.2 (by simp; omega), Finset.sum_empty, zero_pow hkD'.ne']
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A) (fun b => V.valuation (x b))
    Finset.univ_nonempty
  have hvc : V.valuation c ≠ 0 := by simpa using hc
  have h1 : V.valuation (x a) ^ D ≤ V.valuation c := by
    have := (V.valuation_le_one_iff _).2 (hle (hO a))
    rw [map_div₀, map_pow] at this
    exact (div_le_one₀ (zero_lt_iff.2 hvc)).1 this
  have h2 : V.valuation c ≤ V.valuation (x a) ^ D := by
    rw [← hce, map_pow, hes]
    have hb : V.valuation (∑ t ∈ (Finset.univ : Finset A).powersetCard k, ∏ b ∈ t, x b) ≤ V.valuation (x a) ^ k := by
      refine Valuation.map_sum_le _ (fun t ht => ?_)
      rw [map_prod]
      have hcard := (Finset.mem_powersetCard.1 ht).2
      rw [← hcard]
      exact Finset.prod_le_pow_card _ _ _ (fun b _ => ha b (Finset.mem_univ b))
    calc _ ≤ (V.valuation (x a) ^ k) ^ (D / k) := pow_le_pow_left₀ zero_le' hb _
      _ = V.valuation (x a) ^ D := by rw [← pow_mul, Nat.mul_div_cancel' hkD]
  have heq : V.valuation (x a) ^ D = V.valuation c := le_antisymm h1 h2
  have hxa : x a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_pow (by omega)] at heq
    exact hvc heq.symm
  refine ⟨a, hxa, ?_⟩
  let y : O := ⟨x a ^ D / c, hO a⟩
  have hyV : IsUnit (Subring.inclusion hle y) := by
    refine (V.valuation_eq_one_iff ⟨x a ^ D / c, hle (hO a)⟩).2 ?_
    show V.valuation (x a ^ D / c) = 1
    rw [map_div₀, map_pow, heq, div_self hvc]
  have hy : IsUnit y := hloc.map_nonunit _ hyV
  obtain ⟨u, hu⟩ := hy
  have : ((u⁻¹ : Oˣ) : O) = c / x a ^ D := by
    have h3 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    rw [hu] at h3
    have h4 : (x a ^ D / c) * (((u⁻¹ : Oˣ) : O) : K) = 1 := h3
    show (((u⁻¹ : Oˣ) : O) : K) = c / x a ^ D
    rw [eq_inv_of_mul_eq_one_right h4, inv_div]
  rw [← this]
  exact ((u⁻¹ : Oˣ) : O).2

end GlobalTheory
end

