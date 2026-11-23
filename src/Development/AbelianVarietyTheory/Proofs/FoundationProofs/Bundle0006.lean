module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitAlgebraMapEqOfValuationEqOne
section
open IsLocalRing

namespace GlobalTheory.PrimeElement

variable {R : Type*} [CommRing R] {π : R}

theorem isPrime_span (hπ : Prime π) : (Ideal.span {π}).IsPrime :=
  (Ideal.span_singleton_prime hπ.ne_zero).2 hπ

theorem mem_primeCompl_span [(Ideal.span {π}).IsPrime] {b : R} :
    b ∈ (Ideal.span {π}).primeCompl ↔ ¬ π ∣ b := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]

section AtPrime

variable [(Ideal.span {π}).IsPrime] (S : Type*) [CommRing S] [Algebra R S]
  [IsLocalization.AtPrime S (Ideal.span {π})]

theorem maximalIdeal_eq_span [IsLocalRing S] :
    maximalIdeal S = Ideal.span {algebraMap R S π} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {π}) S, Ideal.map_span,
    Set.image_singleton]

include π in
theorem algebraMap_atPrime_injective [IsDomain R] : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (Ideal.span {π}).primeCompl_le_nonZeroDivisors

include π in
theorem isDomain_atPrime [IsDomain R] : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors S (Ideal.span {π}).primeCompl_le_nonZeroDivisors

theorem isDiscreteValuationRing [IsDomain R] [IsNoetherianRing R] [IsDomain S] (hπ : π ≠ 0) :
    IsDiscreteValuationRing S := by
  have := IsLocalization.AtPrime.isLocalRing S (Ideal.span {π})
  have : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing (Ideal.span {π}).primeCompl S inferInstance
  have hne : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_atPrime_injective (π := π) S)).2 hπ
  have hf : ¬ IsField S := by
    rw [isField_iff_maximalIdeal_eq, maximalIdeal_eq_span (π := π) S, Ideal.span_singleton_eq_bot]
    exact hne
  refine ((IsDiscreteValuationRing.TFAE S hf).out 1 5).2 ?_
  exact ⟨⟨_, maximalIdeal_eq_span (π := π) S⟩⟩

theorem irreducible_algebraMap [IsDomain R] [IsNoetherianRing R] (hπ : π ≠ 0) :
    Irreducible (algebraMap R S π) := by
  have := isDomain_atPrime (π := π) S
  have := isDiscreteValuationRing (π := π) S hπ
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (maximalIdeal_eq_span S)

end AtPrime

theorem exists_eq_of_pow_mul_of_mul {K : Type*} [CommRing K] [IsDomain K] [Algebra R K]
    [FaithfulSMul R K] (hπ : Prime π) {x : K} {n : ℕ} {a b c : R}
    (ha : algebraMap R K (π ^ n) * x = algebraMap R K a) (hb : ¬ π ∣ b)
    (hc : algebraMap R K b * x = algebraMap R K c) : ∃ r : R, algebraMap R K r = x := by
  have hinj := FaithfulSMul.algebraMap_injective R K
  have := hinj.isDomain
  have h : b * a = π ^ n * c := hinj <| by
    rw [map_mul, map_mul, ← ha, ← hc]; ring
  obtain ⟨r, rfl⟩ : π ^ n ∣ a := hπ.pow_dvd_of_dvd_mul_left n hb ⟨c, h⟩
  refine ⟨r, mul_left_cancel₀ ((map_ne_zero_iff _ hinj).2 (pow_ne_zero n hπ.ne_zero)) ?_⟩
  rw [ha, map_mul]

section Inter

variable [(Ideal.span {π}).IsPrime]
  (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  (K : Type*) [CommRing K] [IsDomain K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K]

theorem range_inf_range (hπ : π ≠ 0) :
    (algebraMap A K).range ⊓ (algebraMap S K).range = (algebraMap R K).range := by
  have hp : Prime π := (Ideal.span_singleton_prime hπ).1 inferInstance
  refine le_antisymm ?_ ?_
  · rintro x ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h₁⟩ := IsLocalization.surj (Submonoid.powers π) y
    obtain ⟨⟨c, ⟨b, hb⟩⟩, h₂⟩ := IsLocalization.surj (Ideal.span {π}).primeCompl z
    refine exists_eq_of_pow_mul_of_mul hp (n := n) (a := a) (c := c) ?_
      (mem_primeCompl_span.1 hb) ?_
    · rw [IsScalarTower.algebraMap_apply R A K, IsScalarTower.algebraMap_apply R A K a, ← h₁,
        map_mul, hy, mul_comm]
    · rw [IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K c, ← h₂,
        map_mul, hz, mul_comm]
  · rintro _ ⟨r, rfl⟩
    exact ⟨⟨algebraMap R A r, (IsScalarTower.algebraMap_apply R A K r).symm⟩,
      ⟨algebraMap R S r, (IsScalarTower.algebraMap_apply R S K r).symm⟩⟩

omit [(Ideal.span {π}).IsPrime] in
theorem algebraMap_away_injective (hπ : π ≠ 0) : Function.Injective (algebraMap A K) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have hinj := FaithfulSMul.algebraMap_injective R K
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers π) y
  have h := congrArg (algebraMap A K) (IsLocalization.mk'_spec A a s)
  rw [map_mul, hy, zero_mul, ← IsScalarTower.algebraMap_apply, eq_comm,
    map_eq_zero_iff _ hinj] at h
  simp [h]


variable {A S} in
theorem exists_algebraMap_eq (hπ : π ≠ 0) {y : A} {z : S}
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, algebraMap R A r = y := by
  obtain ⟨r, hr⟩ : algebraMap A K y ∈ (algebraMap R K).range := by
    rw [← range_inf_range A S K hπ]
    exact ⟨⟨y, rfl⟩, ⟨z, h.symm⟩⟩
  exact ⟨r, algebraMap_away_injective A K hπ (by rw [← IsScalarTower.algebraMap_apply, hr])⟩


variable {A S} in
theorem exists_unit_algebraMap_eq (hπ : π ≠ 0) {y : A} (hy : IsUnit y) {z : S} (hz : IsUnit z)
    (h : algebraMap A K y = algebraMap S K z) :
    ∃ r : R, IsUnit r ∧ algebraMap R A r = y := by
  obtain ⟨y, rfl⟩ := hy
  obtain ⟨z, rfl⟩ := hz
  have h' : algebraMap A K (y⁻¹ : Aˣ) = algebraMap S K (z⁻¹ : Sˣ) := by
    refine mul_left_cancel₀ (y.isUnit.map (algebraMap A K)).ne_zero ?_
    rw [← map_mul, Units.mul_inv, map_one, h, ← map_mul, Units.mul_inv, map_one]
  obtain ⟨r, hr⟩ := exists_algebraMap_eq (A := A) (S := S) (K := K) hπ h
  obtain ⟨r', hr'⟩ := exists_algebraMap_eq (A := A) (S := S) (K := K) hπ h'
  refine ⟨r, IsUnit.of_mul_eq_one r' (FaithfulSMul.algebraMap_injective R K ?_), hr⟩
  rw [IsScalarTower.algebraMap_apply R A K, map_mul, hr, hr', Units.mul_inv, map_one, map_one]

end Inter

section Valuation

variable [(Ideal.span {π}).IsPrime]
  {A : Type*} [CommRing A] [Algebra R A] [IsLocalization.Away π A]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
  [IsDomain S] [IsDiscreteValuationRing S]
  (K : Type*) [Field K] [Algebra R K] [FaithfulSMul R K]
  [Algebra A K] [IsScalarTower R A K] [Algebra S K] [IsScalarTower R S K] [IsFractionRing S K]

end Valuation

theorem existsUnique_zpow_mul_eq_unit {S K : Type*} [CommRing S] [IsDomain S]
    [IsDiscreteValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] {ϖ : S}
    (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃! a : ℤ, ∃ u : S, IsUnit u ∧ algebraMap S K u = algebraMap S K ϖ ^ a * x := by
  have hinj := IsFractionRing.injective S K
  have h0 : algebraMap S K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
  have key : ∀ (a b : ℤ) (u v : S), IsUnit v → algebraMap S K u = algebraMap S K ϖ ^ a * x →
      algebraMap S K v = algebraMap S K ϖ ^ b * x → b ≤ a := by
    intro a b u v hv h₁ h₂
    by_contra! hlt
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + (n + 1 : ℕ) := ⟨(b - a - 1).toNat, by push_cast; omega⟩
    have : v = ϖ * (ϖ ^ n * u) := hinj <| by
      rw [h₂, hn, zpow_add₀ h0, zpow_natCast, map_mul, map_mul, map_pow, h₁]; ring
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (this ▸ hv))
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := S) x
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  have hp0 : p ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hq0 hϖ
  refine existsUnique_of_exists_of_unique ⟨(n : ℤ) - m, (u * v⁻¹ : Sˣ), Units.isUnit _, ?_⟩ ?_
  · have hv : algebraMap S K v ≠ 0 := (v.isUnit.map _).ne_zero
    rw [zpow_sub₀ h0]
    simp only [Units.val_mul, map_mul, map_units_inv, map_pow, zpow_natCast]
    field_simp
  · rintro a b ⟨u, hu, h₁⟩ ⟨v, hv, h₂⟩
    exact le_antisymm (key b a v u hu h₂ h₁) (key a b u v hv h₁ h₂)

end GlobalTheory.PrimeElement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitNormOfSelfDualHermitianLattice
section
namespace GlobalTheory

theorem exists_unit_norm_of_selfDual_hermitian_lattice :
    ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (p d : ℕ) (θ : K) (O : Subring K) (L : AddSubgroup V), p.Prime → d.Prime → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → (∀ x ∈ O, σ x ∈ O) → (1 + θ) / 2 ∈ O → (∀ r : ℚ, (r : K) ∈ O ↔ padicNorm p r ≤ 1) → (∀ x y : V, h y x = σ (h x y)) → (∀ x : V, h x x = 0 → x = 0) → (∀ a ∈ O, ∀ x ∈ L, a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, h x y ∈ O) → (∀ x : V, ∃ m : ℕ, (p : K) ^ m • x ∈ L) → ∀ W : Submodule K V, (∀ x ∈ W, (∀ y ∈ L, y ∈ W → h x y ∈ O) → x ∈ L) → (∃ x ∈ W, x ≠ 0) → ∃ y ∈ L, y ∈ W ∧ ∃ u : ℚ, h y y = (u : K) ∧ padicNorm p u = 1 := by
  intro K V _ _ _ _ σ h p d θ O L hp hd hθ hσθ hK _ hω hO hherm hdef hL hLO hscale W hW hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    have : (d : K) = 0 := by simpa using hθ
    exact hd.ne_zero (by exact_mod_cast this)

  have hrat : ∀ x : V, ∃ u : ℚ, h x x = (u : K) := by
    intro x
    obtain ⟨a, b, hab⟩ := hK (h x x)
    have h1 := hherm x x
    rw [hab, map_add (f := _), map_mul, map_ratCast, map_ratCast, hσθ] at h1
    have h2 : (b : K) * θ = 0 := by
      have : (2 : K) * ((b : K) * θ) = 0 := by linear_combination h1
      simpa using this
    exact ⟨a, by rw [hab, h2, add_zero]⟩
  have hnp : padicNorm p (p : ℚ) = (p : ℚ)⁻¹ := padicNorm.padicNorm_p_of_prime
  by_contra hcon
  push_neg at hcon
  have hdiv : ∀ y ∈ L, y ∈ W → h y y / p ∈ O := by
    intro y hy hyW
    obtain ⟨u, hu⟩ := hrat y
    have h1 : padicNorm p u ≤ 1 := (hO u).1 (hu ▸ hLO y hy y hy)
    have h2 := hcon y hy hyW u hu
    have h3 : ((u / p : ℚ) : K) ∈ O := by
      rw [hO, padicNorm.div, hnp]
      by_cases hu0 : u = 0
      · simp [hu0]
      obtain ⟨z, hz⟩ := padicNorm.values_discrete (p := p) hu0
      rw [hz] at h1 h2 ⊢
      have hz0 : -z < 0 := by
        have := lt_of_le_of_ne h1 h2
        exact (zpow_lt_one_iff_right₀ hp1).1 this
      rw [div_inv_eq_mul, ← zpow_add_one₀ hpQ]
      exact zpow_le_one_of_nonpos₀ hp1.le (by omega)
    rw [hu]
    simpa using h3
  have htr : ∀ x ∈ L, x ∈ W → ∀ y ∈ L, y ∈ W → (h x y + σ (h x y)) / p ∈ O := by
    intro x hx hxW y hy hyW
    have h1 := O.sub_mem (O.sub_mem (hdiv _ (L.add_mem hx hy) (W.add_mem hxW hyW)) (hdiv x hx hxW))
      (hdiv y hy hyW)
    convert h1 using 1
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [← hherm x y]
    ring
  have hstep : ∀ x ∈ L, x ∈ W → (θ / p) • x ∈ L := by
    intro x hx hxW
    refine hW _ (W.smul_mem _ hxW) ?_
    intro y hy hyW
    have r1 := htr x hx hxW y hy hyW
    have r2 := htr _ (hL _ hω x hx) (W.smul_mem _ hxW) y hy hyW
    have h1 := O.add_mem r2 (O.mul_mem (O.sub_mem hω O.one_mem) r1)
    convert h1 using 1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, map_div₀, map_add (f := _), map_one,
      hσθ, map_ofNat]
    field_simp
    ring
  obtain ⟨x, hxW, hx0⟩ := hne
  obtain ⟨m, hm⟩ := hscale x
  set x0 := (p : K) ^ m • x with hx0def
  have hx0W : x0 ∈ W := W.smul_mem _ hxW
  have hx00 : x0 ≠ 0 := smul_ne_zero (pow_ne_zero _ hpK) hx0
  have hiter : ∀ k : ℕ, (θ / p) ^ k • x0 ∈ L := by
    intro k
    induction k with
    | zero => simpa using hm
    | succ k ih =>
      rw [pow_succ', mul_smul]
      exact hstep _ ih (W.smul_mem _ hx0W)
  obtain ⟨u, hu⟩ := hrat x0
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hx00 (hdef _ (by simpa using hu))
  have hupos : 0 < padicNorm p u :=
    lt_of_le_of_ne (padicNorm.nonneg _) (padicNorm.nonzero hu0).symm
  have hnd : (p : ℚ)⁻¹ ≤ padicNorm p (d : ℚ) := by
    by_cases hpd : p = d
    · rw [← hpd, hnp]
    · haveI : Fact d.Prime := ⟨hd⟩
      rw [padicNorm.padicNorm_of_prime_of_ne hpd]
      exact inv_le_one_of_one_le₀ hp1.le
  have hc : (p : ℚ) ≤ padicNorm p ((d : ℚ) / (p * p)) := by
    rw [padicNorm.div, padicNorm.mul, hnp, le_div_iff₀ (by positivity)]
    calc (p : ℚ) * ((p : ℚ)⁻¹ * (p : ℚ)⁻¹) = (p : ℚ)⁻¹ := by field_simp
      _ ≤ _ := hnd
  have hpow : ∀ (q : ℚ) (k : ℕ), padicNorm p (q ^ k) = padicNorm p q ^ k := by
    intro q k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, pow_succ, padicNorm.mul, ih]
  have hbound : ∀ k : ℕ, (p : ℚ) ^ k * padicNorm p u ≤ 1 := by
    intro k
    have h1 := hLO _ (hiter k) _ (hiter k)
    have h2 : h ((θ / p) ^ k • x0) ((θ / p) ^ k • x0) = ((((d : ℚ) / (p * p)) ^ k * u : ℚ) : K) := by
      rw [h.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, hu, smul_eq_mul, smul_eq_mul,
        map_pow, map_div₀, hσθ, map_natCast, ← mul_assoc, ← mul_pow]
      push_cast
      congr 2
      field_simp
      linear_combination -hθ
    rw [h2, hO, padicNorm.mul, hpow] at h1
    refine le_trans ?_ h1
    gcongr
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (padicNorm p u)⁻¹ hp1
  have := hbound k
  rw [inv_lt_iff_one_lt_mul₀ hupos] at hk
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalFixedFieldMapOfFiniteIndex
section
open Polynomial IntermediateField

namespace GlobalTheory

theorem isSeparable_and_natDegree_le_of_fixed {F E : Type} [Field F] [Field E] [Algebra F E]
    (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G) [N.FiniteIndex]
    (hG : ∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E))
    (x : E) (hx : ∀ n ∈ N, act n x = x) :
    IsIntegral F x ∧ IsSeparable F x ∧ (minpoly F x).natDegree ≤ N.index := by
  classical
  haveI : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let f : G ⧸ N → E := fun q => Quotient.liftOn' q (fun g => act g x) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have := hx _ hab
    show act a x = act b x
    calc act a x = act a (act (a⁻¹ * b) x) := by rw [this]
      _ = act b x := by rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left])
  have hf : ∀ g : G, f (QuotientGroup.mk g) = act g x := fun g => rfl
  let S : Finset E := Finset.univ.image f
  have hS : ∀ y, y ∈ S ↔ ∃ g : G, act g x = y := by
    intro y
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨q, rfl⟩
      induction q using QuotientGroup.induction_on with
      | H g => exact ⟨g, (hf g).symm⟩
    · rintro ⟨g, rfl⟩; exact ⟨_, hf g⟩
  have hcard : S.card ≤ N.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    exact Finset.card_image_le.trans (by simp)
  let p : E[X] := ∏ y ∈ S, (X - C y)
  have hpmon : p.Monic := monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y
  have hpsep : p.Separable := separable_prod_X_sub_C_iff'.2 (fun a _ b _ h => h)
  have hpdeg : p.natDegree = S.card := natDegree_finsetProd_X_sub_C_eq_card S id
  have hpinv : ∀ g : G, p.map ((act g : E ≃ₐ[F] E) : E →+* E) = p := by
    intro g
    simp only [p, Polynomial.map_prod, Polynomial.map_sub, map_X, map_C]
    have himg : S.image (act g) = S := by
      ext y
      simp only [Finset.mem_image, hS]
      constructor
      · rintro ⟨z, ⟨h, rfl⟩, rfl⟩
        exact ⟨g * h, by rw [map_mul, AlgEquiv.mul_apply]⟩
      · rintro ⟨h, rfl⟩
        exact ⟨act (g⁻¹ * h) x, ⟨g⁻¹ * h, rfl⟩, by
          rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]⟩
    conv_rhs => rw [← himg]
    rw [Finset.prod_image (fun a _ b _ h => (act g).injective h)]
    rfl
  have hlift : p ∈ lifts (algebraMap F E) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have : p.coeff n ∈ (⊥ : IntermediateField F E) := by
      apply hG
      intro g
      conv_rhs => rw [← hpinv g]
      rw [coeff_map]
      rfl
    exact mem_bot.1 this
  obtain ⟨q, hqmap, hqdeg, hqmon⟩ := lifts_and_natDegree_eq_and_monic hlift hpmon
  have hxS : x ∈ S := (hS x).2 ⟨1, by simp⟩
  have hqx : aeval x q = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, hqmap, eval_prod]
    exact Finset.prod_eq_zero hxS (by simp)
  have hint : IsIntegral F x := ⟨q, hqmon, hqx⟩
  have hdvd : minpoly F x ∣ q := minpoly.dvd F x hqx
  have hqsep : q.Separable := (separable_map (algebraMap F E)).1 (hqmap ▸ hpsep)
  refine ⟨hint, hqsep.of_dvd hdvd, ?_⟩
  calc (minpoly F x).natDegree ≤ q.natDegree := natDegree_le_of_dvd hdvd hqmon.ne_zero
    _ = S.card := by rw [hqdeg, hpdeg]
    _ ≤ N.index := hcard

theorem finiteDimensional_fixedField_map_of_finiteIndex : ∀ {F E : Type} [Field F] [Field E]
    [Algebra F E] (G : Type) [Group G] (act : G →* (E ≃ₐ[F] E)) (N : Subgroup G), N.FiniteIndex →
    (∀ x : E, (∀ g, act g x = x) → x ∈ (⊥ : IntermediateField F E)) →
    FiniteDimensional F (IntermediateField.fixedField (N.map act)) := by
  intro F E _ _ _ G _ act N hN hG
  set L := IntermediateField.fixedField (N.map act) with hLdef
  have key : ∀ y ∈ L, IsIntegral F y ∧ IsSeparable F y ∧ (minpoly F y).natDegree ≤ N.index := by
    intro y hy
    refine isSeparable_and_natDegree_le_of_fixed G act N hG y fun n hn => ?_
    exact (mem_fixedField_iff _ _).1 hy _ (Subgroup.mem_map_of_mem act hn)
  have hbound : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ N.index := by
    intro y hy
    rw [adjoin.finrank (key y hy).1]
    exact (key y hy).2.2
  let D : Set ℕ := {d | ∃ y ∈ L, Module.finrank F F⟮y⟯ = d}
  have hDne : D.Nonempty := ⟨_, 0, L.zero_mem, rfl⟩
  have hDbdd : BddAbove D := ⟨N.index, by rintro d ⟨y, hy, rfl⟩; exact hbound y hy⟩
  obtain ⟨x, hxL, hxmax⟩ := Nat.sSup_mem hDne hDbdd
  have hle : ∀ y ∈ L, Module.finrank F F⟮y⟯ ≤ Module.finrank F F⟮x⟯ := by
    intro y hy
    rw [hxmax]
    exact le_csSup hDbdd ⟨y, hy, rfl⟩
  have hLx : L ≤ F⟮x⟯ := by
    intro y hy
    have hx := key x hxL
    have hy' := key y hy
    haveI := isSeparable_adjoin_pair_of_isSeparable F E hx.2.1 hy'.2.1
    haveI : FiniteDimensional F F⟮x, y⟯ := finiteDimensional_adjoin (by
      rintro z (rfl | rfl)
      · exact hx.1
      · exact hy'.1)
    obtain ⟨α, hα⟩ := Field.exists_primitive_element F F⟮x, y⟯
    have hz : F⟮(α : E)⟯ = F⟮x, y⟯ := by
      simpa only [lift_adjoin_simple, lift_top] using congr_arg lift hα
    have hKL : F⟮x, y⟯ ≤ L := by
      rw [adjoin_le_iff]
      rintro z (rfl | rfl)
      · exact hxL
      · exact hy
    have hxK : F⟮x⟯ ≤ F⟮x, y⟯ := adjoin_simple_le_iff.2 (subset_adjoin F _ (by simp))
    have heq : F⟮x⟯ = F⟮x, y⟯ := by
      apply eq_of_le_of_finrank_le hxK
      rw [← hz]
      exact hle _ (hKL α.2)
    rw [heq]
    exact subset_adjoin F _ (by simp)
  haveI : FiniteDimensional F F⟮x⟯ := adjoin.finiteDimensional (key x hxL).1
  exact Module.Finite.of_injective (IntermediateField.inclusion hLx).toLinearMap
    (IntermediateField.inclusion_injective hLx)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GramDetIndexSublattice
section
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem gram_det_index_sublattice (U V ι κ : Type) [AddCommGroup U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : U →ₗ[ℤ] V) (u : ι → U) (v : κ → U) (hc : Fintype.card ι = Fintype.card κ)
    (hv : ∀ k, v k ∈ Submodule.span ℤ (Set.range u)) :
    ∃ m : ℕ, (Matrix.gram ℝ fun k => φ (v k)).det = (m : ℝ) ^ 2 * (Matrix.gram ℝ fun i => φ (u i)).det ∧
      ∀ i, (m : ℤ) • u i ∈ Submodule.span ℤ (Set.range v) := by
  let e : ι ≃ κ := Fintype.equivOfCardEq hc
  choose A hA using fun i => (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hv (e i))
  let Am : Matrix ι ι ℤ := Matrix.of A
  have hAm : ∀ i j, Am i j = A i j := fun _ _ => rfl
  let Ar : Matrix ι ι ℝ := Am.map (Int.castRingHom ℝ)
  have hAr : ∀ i j, Ar i j = (A i j : ℝ) := fun _ _ => rfl
  have hphi : ∀ i, φ (v (e i)) = ∑ j, (A i j : ℝ) • φ (u j) := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hA i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  have h1 : (Matrix.gram ℝ fun k => φ (v k)).submatrix e e
      = Ar * (Matrix.gram ℝ fun i => φ (u i)) * Arᵀ := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, hAr]
    rw [hphi i, hphi j, inner_sum]
    simp only [sum_inner, real_inner_smul_left, real_inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  have hdetA : Ar.det = (Am.det : ℝ) := by
    have := (Int.castRingHom ℝ).map_det Am
    simpa [Ar] using this.symm
  refine ⟨Am.det.natAbs, ?_, ?_⟩
  · have h2 := Matrix.det_submatrix_equiv_self e (Matrix.gram ℝ fun k => φ (v k))
    rw [← h2, h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdetA]
    have h3 : ((Am.det.natAbs : ℕ) : ℝ) ^ 2 = (Am.det : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [h3]; ring
  · intro i
    have hkey : Am.det • u i = ∑ k, Am.adjugate i k • v (e k) := by
      have h4 : ∀ j, (Am.adjugate * Am) i j = Am.det * (1 : Matrix ι ι ℤ) i j := by
        intro j
        rw [Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul]
      calc Am.det • u i = ∑ j, (Am.det * (1 : Matrix ι ι ℤ) i j) • u j := by
            simp [Matrix.one_apply, ite_smul]
        _ = ∑ j, (∑ k, Am.adjugate i k * A k j) • u j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← h4 j, Matrix.mul_apply]; rfl
        _ = ∑ k, Am.adjugate i k • v (e k) := by
            simp only [Finset.sum_smul, ← hA, Finset.smul_sum, mul_smul]
            exact Finset.sum_comm
    have hmem : Am.det • u i ∈ Submodule.span ℤ (Set.range v) := by
      rw [hkey]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)
    rcases Int.natAbs_eq Am.det with h | h
    · rw [← h]; exact hmem
    · have : ((Am.det.natAbs : ℕ) : ℤ) = -Am.det := by omega
      rw [this, neg_smul]
      exact Submodule.neg_mem _ hmem

end GlobalTheory
end

