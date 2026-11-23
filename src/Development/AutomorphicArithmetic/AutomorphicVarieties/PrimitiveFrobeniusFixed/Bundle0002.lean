module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

namespace UpperTheory.V.ML.PlaceBasics

section Rat

variable (l : ℕ) [hl : Fact l.Prime]

private theorem prime_l : Prime ((l : ℕ) : 𝓞 ℚ) := by
  have h : Prime ((l : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  rw [e]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr h

private noncomputable def vQ : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l l).ne_zero).mpr (prime_l l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l l).ne_zero

private theorem normV_vQ : normV (vQ l) = l := by
  have h : normV (vQ l) = Ideal.absNorm (vQ l).asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  rw [h]
  show Ideal.absNorm (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l
  rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
  simp

private theorem mem_vQ : ((l : ℕ) : 𝓞 ℚ) ∈ (vQ l).asIdeal := Ideal.mem_span_singleton_self _

variable {l} {Ω : Type} [Field Ω]

private theorem intCast_mem_vQ (n : ℤ) : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
  show ((n : ℤ) : 𝓞 ℚ) ∈ Ideal.span {((l : ℕ) : 𝓞 ℚ)} ↔ _
  rw [Ideal.mem_span_singleton]
  have e1 : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
  have e2 : ((n : ℤ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm n := by simp
  rw [e1, e2]
  exact map_dvd_iff Rat.ringOfIntegersEquiv.symm

private theorem val_intCast_le_one (A : ValuationSubring Ω) (n : ℤ) : A.valuation (n : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (intCast_mem A n)

private theorem not_of_coprime (A : ValuationSubring Ω) {m n : ℤ} (hc : IsCoprime m n)
    (hm : A.valuation (m : Ω) < 1) : ¬ A.valuation (n : Ω) < 1 := by
  intro h
  obtain ⟨a, b, hab⟩ := hc
  have h1 : A.valuation ((a : Ω) * (m : Ω) + (b : Ω) * (n : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A a)) hm
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one A b)) h
  have h2 : (a : Ω) * (m : Ω) + (b : Ω) * (n : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

private theorem val_intCast_lt_one_iff (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) (n : ℤ) :
    A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := by
  constructor
  · intro h
    by_contra hnd
    exact not_of_coprime A (((Nat.prime_iff_prime_int.mp hl.out).coprime_iff_not_dvd).mpr hnd)
      (by rwa [Int.cast_natCast]) h
  · rintro ⟨k, rfl⟩
    push_cast
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_intCast_le_one A k)) hA

private theorem isPlaceOver_vQ [Algebra ℚ Ω] (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = ((n : ℤ) : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, by
      have := Rat.ringOfIntegersEquiv.symm_apply_apply x
      rw [← this]; simp⟩
  rw [intCast_mem_vQ, ← val_intCast_lt_one_iff A hA]
  simp

end Rat

section Roots

variable {Ω : Type} [Field Ω] (A : ValuationSubring Ω)

private theorem val_root {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {ζ : Ω} (h : ζ ^ m = 1) : A.valuation ζ = 1 := by
  have hm : m ≠ 0 := by
    rintro rfl
    exact hv (by simp)
  have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact (pow_eq_one_iff_left hm).1 h1

private theorem one_sub_pow {η : Ω} (h1 : A.valuation η = 1) (h : A.valuation (η - 1) < 1) (i : ℕ) :
    A.valuation (1 - η ^ i) < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : 1 - η ^ (i + 1) = η * (1 - η ^ i) - (η - 1) := by ring
    rw [e]
    refine A.valuation.map_sub_lt ?_ h
    rw [map_mul, h1, one_mul]; exact ih

private theorem root_eq_one {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {η : Ω} (hη : η ^ m = 1)
    (h : A.valuation (η - 1) < 1) : η = 1 := by
  by_contra hne
  apply hv
  have hs : ∑ i ∈ Finset.range m, η ^ i = 0 := by
    have := mul_geom_sum η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have e : (m : Ω) = ∑ i ∈ Finset.range m, (1 - η ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [e]
  exact A.valuation.map_sum_lt one_ne_zero fun i _ => one_sub_pow A (val_root A hv hη) h i

private theorem root_eq {m : ℕ} (hv : ¬ A.valuation (m : Ω) < 1) {ξ ζ : Ω} (hξ : ξ ^ m = 1) (hζ : ζ ^ m = 1)
    (h : A.valuation (ξ - ζ) < 1) : ξ = ζ := by
  have h1 := val_root A hv hζ
  have h0 : ζ ≠ 0 := by
    rintro rfl
    simp at h1
  have e : ξ / ζ - 1 = (ξ - ζ) / ζ := by field_simp
  have : ξ / ζ = 1 := by
    refine root_eq_one A hv (by rw [div_pow, hξ, hζ, div_one]) ?_
    rw [e, map_div₀, h1, div_one]; exact h
  exact (div_eq_one_iff_eq h0).1 this

end Roots

section Conj

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (g : G ℚ Ω)

private theorem smul_mem (y : Ω) : g y ∈ g • A ↔ y ∈ A := by
  rw [← AlgEquiv.smul_def]
  exact ValuationSubring.smul_mem_pointwise_smul_iff

private theorem smul_le (y : Ω) : (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, smul_mem]

private theorem smul_lt (y : Ω) : (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', smul_mem, ← map_inv₀, smul_mem, map_eq_zero_iff _ g.injective]

private theorem smul_eq (y : Ω) : (g • A).valuation (g y) = 1 ↔ A.valuation y = 1 := by
  rw [eq_iff_le_not_lt, eq_iff_le_not_lt, smul_le, smul_lt]

private theorem dec_iff (x : G ℚ Ω) : x ∈ Dec (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Dec (F := ℚ) A := by
  rw [mem_Dec, mem_Dec, mul_smul, mul_smul, inv_smul_eq_iff]

private theorem pow_iff (x : G ℚ Ω) (q : ℕ) :
    (∀ y : Ω, (g • A).valuation y ≤ 1 → (g • A).valuation (x y - y ^ q) < 1) ↔
      ∀ y : Ω, A.valuation y ≤ 1 → A.valuation ((g⁻¹ * x * g) y - y ^ q) < 1 := by
  rw [g.surjective.forall]
  refine forall_congr' fun y => ?_
  have e : x (g y) - g y ^ q = g ((g⁻¹ * x * g) y - y ^ q) := by
    rw [map_sub, map_pow, ← AlgEquiv.mul_apply g, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
      AlgEquiv.mul_apply]
  rw [e, smul_le, smul_lt]

end Conj

end UpperTheory.V.ML.PlaceBasics

open UpperTheory.V.ML.PlaceBasics in
theorem UpperTheory.V.ML.placeBasic :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω],
    (∀ q : ℕ, q.Prime → ∃ A : ValuationSubring Ω, Over A q) ∧
    (∀ (A : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → ∃ φ : G ℚ Ω, IsFrob (F := ℚ) A q φ) ∧
    (∀ (A : ValuationSubring Ω) (m n : ℕ), Over A (m * n) ↔ Over A m ∨ Over A n) ∧
    (∀ (A : ValuationSubring Ω) (m n : ℕ), m.Coprime n → Over A m → ¬ Over A n) ∧
    (∀ (A : ValuationSubring Ω) (k : ℕ), ¬ Over A k → Ine (F := ℚ) A ≤ fixMu ℚ Ω k) ∧
    (∀ (A : ValuationSubring Ω) (k : ℕ) (ζ : Ω), ¬ Over A k → ζ ^ k = 1 → A.valuation (ζ - 1) < 1 → ζ = 1) ∧
    (∀ (A : ValuationSubring Ω) (q k : ℕ) (φ : G ℚ Ω), IsFrob (F := ℚ) A q φ → ¬ Over A k → Pows k q φ) ∧
    (∀ (A A' : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → Over A' q → ∃ g : G ℚ Ω, A' = g • A) ∧
    (∀ (A : ValuationSubring Ω) (q : ℕ), q.Prime → Over A q → ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v ∧ normV v = q ∧ (q : 𝓞 ℚ) ∈ v.asIdeal) ∧
    ∀ (A : ValuationSubring Ω) (g : G ℚ Ω), (∀ x, x ∈ Dec (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Dec (F := ℚ) A) ∧ (∀ x, x ∈ Ine (F := ℚ) (g • A) ↔ g⁻¹ * x * g ∈ Ine (F := ℚ) A) ∧
      (∀ q x, IsFrob (F := ℚ) (g • A) q x ↔ IsFrob (F := ℚ) A q (g⁻¹ * x * g)) ∧ (∀ y : Ω, (g • A).valuation (g y) < 1 ↔ A.valuation y < 1) ∧ ∀ y : Ω, (g • A).valuation (g y) = 1 ↔ A.valuation y = 1 := by
  intro Ω _ _ _
  refine ⟨fun q hq => ?_, fun A q hq hA => ?_, fun A m n => ?_, fun A m n hc hm => ?_, fun A k hk g hg x hx => ?_,
    fun A k ζ hk hζ h => root_eq_one A hk hζ h, fun A q k φ hφ hk x hx => ?_, fun A A' q hq hA hA' => ?_,
    fun A q hq hA => ?_, fun A g => ⟨dec_iff A g, fun x => ?_, fun q x => and_congr (dec_iff A g x) (pow_iff A g x q),
      smul_lt A g, smul_eq A g⟩⟩
  · haveI := Fact.mk hq
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω (vQ q)
    refine ⟨A, ?_⟩
    simpa using (hA ((q : ℕ) : 𝓞 ℚ)).2 (mem_vQ q)
  · haveI := Fact.mk hq
    obtain ⟨g, hg⟩ := exists_isFrob (isPlaceOver_vQ A hA)
    rw [normV_vQ] at hg
    exact ⟨g, hg⟩
  · have hm : A.valuation (m : Ω) ≤ 1 := by simpa using val_intCast_le_one A m
    have hn : A.valuation (n : Ω) ≤ 1 := by simpa using val_intCast_le_one A n
    simp only [Over, Nat.cast_mul, map_mul]
    refine ⟨fun h => ?_, fun h => h.elim (lt_of_le_of_lt (mul_le_of_le_one_right' hn))
      (lt_of_le_of_lt (mul_le_of_le_one_left' hm))⟩
    by_contra h'
    rw [not_or] at h'
    rw [hm.eq_of_not_lt h'.1, hn.eq_of_not_lt h'.2, one_mul] at h
    exact lt_irrefl _ h
  · have := not_of_coprime A (Nat.isCoprime_iff_coprime.2 hc) (by rwa [Int.cast_natCast])
    rwa [Int.cast_natCast] at this
  · exact root_eq A hk (by rw [← map_pow, hx, map_one]) hx (hg.2 x (val_root A hk hx).le)
  · exact root_eq A hk (by rw [← map_pow, hx, map_one]) (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow])
      (hφ.2 x (val_root A hk hx).le)
  · haveI := Fact.mk hq
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := ℚ) (isPlaceOver_vQ A hA) (isPlaceOver_vQ A' hA')
    exact ⟨g, hg.symm⟩
  · haveI := Fact.mk hq
    exact ⟨vQ q, isPlaceOver_vQ A hA, normV_vQ q, mem_vQ q⟩
  · have h := pow_iff A g x 1
    simp only [pow_one] at h
    exact and_congr (dec_iff A g x) h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.QocEquiv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise TensorProduct

section

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
  [Module.Finite ℤ_[l] O]

private theorem qoc_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  have hl : (l : O) ≠ 0 := by
    intro h0
    have hz : ∀ t : O ⊗[ℤ_[l]] (ℚ_[l] ⧸ ZlSub l), t = 0 := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rfl
      | tmul o q =>
        obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        have hlq : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
        have hr : (Submodule.Quotient.mk r : ℚ_[l] ⧸ ZlSub l) =
            (l : ℤ_[l]) • Submodule.Quotient.mk (r / l) := by
          rw [← Submodule.Quotient.mk_smul]
          congr 1
          rw [Algebra.smul_def, map_natCast, mul_div_cancel₀ _ hlq]
        rw [hr, ← TensorProduct.smul_tmul, Algebra.smul_def, map_natCast, h0, zero_mul,
          TensorProduct.zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    haveI : Subsingleton (QO l O) := ⟨fun x y => (hz x).trans (hz y).symm⟩
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have h4 := (UpperTheory.V.Base.qoFacts l O).2.2.2 ϖ
    rw [IsDiscreteValuationRing.addVal_uniformizer hϖ, Module.length_eq_zero] at h4
    exact zero_ne_one h4
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  rw [PadicInt.unitCoeff_spec hne, map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.mp hx with h | h
  · exact ((PadicInt.unitCoeff hne).isUnit.map (algebraMap ℤ_[l] O)).ne_zero h
  · exact hl ((pow_eq_zero_iff' (M₀ := O)).mp h).1

private theorem qoc_ann (w : QO l O) : ∃ a : O, a ≠ 0 ∧ ∀ y : O, y • w = 0 ↔ a ∣ y := by
  obtain ⟨n, hn⟩ := (UpperTheory.V.Base.qoFacts l O).2.1 w
  set I : Ideal O := LinearMap.ker (LinearMap.toSpanSingleton O (QO l O) w) with hI
  have key : ∀ y : O, y • w = 0 ↔ Submodule.IsPrincipal.generator I ∣ y := by
    intro y
    rw [← Ideal.mem_span_singleton, Ideal.span_singleton_generator, hI, LinearMap.mem_ker,
      LinearMap.toSpanSingleton_apply]
  refine ⟨Submodule.IsPrincipal.generator I, ?_, key⟩
  intro h0
  have h1 : ((l : O) ^ n) • w = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hn
  rw [key, h0, zero_dvd_iff] at h1
  have hl : (l : O) ≠ 0 := by
    intro h
    apply (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero : (l : ℤ_[l]) ≠ 0)
    apply qoc_inj l O
    rw [map_natCast, map_zero]
    exact h
  exact hl ((pow_eq_zero_iff' (M₀ := O)).mp h1).1

private theorem qoc_ex (a : O) (ha : a ≠ 0) : ∃ w : QO l O, ∀ y : O, y • w = 0 ↔ a ∣ y := by
  by_cases hu : IsUnit a
  · exact ⟨0, fun y => by simp [hu.dvd]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖa : ϖ ∣ a := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
    exact ENat.one_le_iff_ne_zero.mpr hu
  obtain ⟨b, rfl⟩ := hϖa
  have hb : b ≠ 0 := right_ne_zero_of_mul ha
  have hT : Module.length O (LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O)) = 1 := by
    rw [(UpperTheory.V.Base.qoFacts l O).2.2.2 ϖ, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  have hnt : Nontrivial (LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O)) := by
    rw [← Module.length_pos_iff (R := O), hT]
    exact zero_lt_one
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker (ϖ • LinearMap.id : QO l O →ₗ[O] QO l O))
  have hz1 : ϖ • (z : QO l O) = 0 := LinearMap.mem_ker.mp z.2
  have hz2 : (z : QO l O) ≠ 0 := fun h => hz (Subtype.ext h)
  obtain ⟨w, hw⟩ := (UpperTheory.V.Base.qoFacts l O).2.2.1 b hb (z : QO l O)
  obtain ⟨c, hc, hC⟩ := qoc_ann l O w
  refine ⟨w, fun y => ?_⟩
  have hca : c ∣ ϖ * b := (hC _).mp (by rw [mul_smul, hw, hz1])
  have hcb : ¬ c ∣ b := fun h => hz2 (by rw [← hw]; exact (hC b).mpr h)
  have hac : ϖ * b ∣ c := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd] at hca hcb ⊢
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_uniformizer hϖ, add_comm]
    exact Order.add_one_le_of_lt (not_le.mp hcb)
  rw [hC y]
  exact ⟨fun h => hac.trans h, fun h => hca.trans h⟩

private theorem length_quotient_span_eq_addVal' {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (ha : a ≠ 0) :
    Module.length R (R ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr u.isUnit, zero_add,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]

private theorem qoc_gen (a : O) (w : QO l O) (ha : a ≠ 0) (h : ∀ y : O, y • w = 0 ↔ a ∣ y) (w' : QO l O)
    (h' : a • w' = 0) : ∃ y : O, w' = y • w := by
  set T := LinearMap.ker (a • LinearMap.id : QO l O →ₗ[O] QO l O) with hT
  have hTlen : Module.length O T = IsDiscreteValuationRing.addVal O a :=
    (UpperTheory.V.Base.qoFacts l O).2.2.2 a
  have hfin : Module.length O T ≠ ⊤ := by
    rw [hTlen, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
    exact ha
  have hwT : w ∈ T := by simp [hT, (h a).mpr dvd_rfl]
  let g : O →ₗ[O] T := LinearMap.toSpanSingleton O T ⟨w, hwT⟩
  have hker : LinearMap.ker g = Ideal.span {a} := by
    ext y
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton, ← h y]
    simp [g, Subtype.ext_iff]
  have hrange : Module.length O (LinearMap.range g) = Module.length O T := by
    rw [← (LinearMap.quotKerEquivRange g).length_eq, hker, length_quotient_span_eq_addVal' a ha, hTlen]
  have htop : LinearMap.range g = ⊤ := by
    have hfl : IsFiniteLength O T := Module.length_ne_top_iff.mp hfin
    haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
    haveI := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
    by_contra hne
    have hlt := Submodule.length_lt hne
    rw [hrange] at hlt
    exact lt_irrefl _ hlt
  have hw'T : w' ∈ T := by simp [hT, h']
  have hmem : (⟨w', hw'T⟩ : T) ∈ LinearMap.range g := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
  exact ⟨y, by simpa [g] using (congrArg Subtype.val hy).symm⟩

end

theorem UpperTheory.V.ML.qoCyc :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O],
    (∀ w : QO l O, ∃ a : O, a ≠ 0 ∧ ∀ y : O, y • w = 0 ↔ a ∣ y) ∧ (∀ a : O, a ≠ 0 → ∃ w : QO l O, ∀ y : O, y • w = 0 ↔ a ∣ y) ∧
    (∀ (a : O) (w : QO l O), a ≠ 0 → (∀ y : O, y • w = 0 ↔ a ∣ y) → ∀ w' : QO l O, a • w' = 0 → ∃ y : O, w' = y • w) ∧
    (∀ w w' : QO l O, (∃ y : O, w' = y • w) ∨ ∃ y : O, w = y • w') ∧
    ∀ (V : Type) [AddCommGroup V] [Module O V] (f : V →ₗ[O] QO l O) (y : O), (∀ v, y • f v = 0) → Module.length O V ≤ Module.length O (LinearMap.ker f) + IsDiscreteValuationRing.addVal O y := by
  intro l _ O _ _ _ _ _
  refine ⟨qoc_ann l O, qoc_ex l O, fun a w ha h w' h' => qoc_gen l O a w ha h w' h', ?_, ?_⟩
  · intro w w'
    obtain ⟨a, ha, hA⟩ := qoc_ann l O w
    obtain ⟨b, hb, hB⟩ := qoc_ann l O w'
    rcases le_total (IsDiscreteValuationRing.addVal O a) (IsDiscreteValuationRing.addVal O b) with hab | hab
    · rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
      right
      exact qoc_gen l O b w' hb hB w ((hA b).mpr hab)
    · rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
      left
      exact qoc_gen l O a w ha hA w' ((hB a).mpr hab)
  · intro V _ _ f y hy
    have hle : LinearMap.range f ≤ LinearMap.ker (y • LinearMap.id : QO l O →ₗ[O] QO l O) := by
      rintro _ ⟨v, rfl⟩
      simp [hy v]
    rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _),
      (LinearMap.quotKerEquivRange f).length_eq, ← (UpperTheory.V.Base.qoFacts l O).2.2.2 y]
    exact add_le_add le_rfl
      (Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.RadEqv
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

private theorem cyc_pow {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (m : ℕ)
    (g : G ℚ Ω) (x : Ω) (hx : x ^ l ^ m = 1) :
    g x = x ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  exact cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω g) x hx

private theorem dvd_sub_val (l : ℕ) [Fact l.Prime] (m : ℕ) (z : ℤ_[l]) :
    (l : ℤ_[l]) ^ m ∣ z - ((PadicInt.toZModPow m z).val : ℤ_[l]) := by
  have h : PadicInt.toZModPow m (z - ((PadicInt.toZModPow m z).val : ℤ_[l])) = 0 := by
    simp
  have hk : z - ((PadicInt.toZModPow m z).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow (p := l) m) := h
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hk
  exact hk

theorem UpperTheory.V.ML.radEqv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O W : Type) [CommRing O] [Algebra ℤ_[l] O] [AddCommGroup W] [Module O W] (m F r : ℕ), F ≠ 0 → l ^ m ∣ F → r ≠ 0 → ∀ ρ : Ω, ρ ^ (l ^ m) = (r : Ω) →
    ∀ (γ : G ℚ Ω →* Oˣ) (f : G ℚ Ω → W), (∀ u ∈ fixMu ℚ Ω F, ∀ v ∈ fixMu ℚ Ω F, f (u * v) = f u + f v) → (∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, f (g * u * g⁻¹) = (γ g : O) • f u) →
    (∀ u ∈ fixMu ℚ Ω F, (l ^ m) • f u = 0) → (∀ u ∈ fixMu ℚ Ω F, u ρ = ρ → f u = 0) → ∀ g : G ℚ Ω, ∀ u ∈ fixMu ℚ Ω F, ((γ g : O) - (chiO ℚ Ω l O g : O)) • f u = 0 := by
  intro Ω _ _ _ l _ O W _ _ _ _ m F r hF hlF hr ρ hρ γ f hadd hconj htor hfixρ g u hu
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hmem : ∀ w : G ℚ Ω, w ∈ fixMu ℚ Ω F ↔ ∀ x : Ω, x ^ F = 1 → w x = x := fun w => Iff.rfl
  have hr0 : (r : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hr
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hρ
    exact hr0 hρ.symm
  have hroot : ∀ σ : G ℚ Ω, (σ ρ / ρ) ^ (l ^ m) = 1 := by
    intro σ
    rw [div_pow, ← map_pow, hρ, map_natCast, div_self hr0]
  have hfix : ∀ x : Ω, x ^ (l ^ m) = 1 → u x = x := by
    intro x hx
    obtain ⟨c, hc⟩ := hlF
    exact (hmem u).mp hu x (by rw [hc, pow_mul, hx, one_pow])
  obtain ⟨ζ, hζdef⟩ : ∃ ζ, ζ = u ρ / ρ := ⟨_, rfl⟩
  have hζ : ζ ^ (l ^ m) = 1 := hζdef ▸ hroot u
  have huρ : u ρ = ζ * ρ := by rw [hζdef, div_mul_cancel₀ _ hρ0]
  have hpow : ∀ n : ℕ, (u ^ n) ρ = ζ ^ n * ρ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, map_mul, map_pow, hfix ζ hζ, huρ, pow_succ]
      ring
  obtain ⟨k, hkdef⟩ : ∃ k, k = (PadicInt.toZModPow m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])).val := ⟨_, rfl⟩
  have hgζ : g ζ = ζ ^ k := by rw [hkdef]; exact cyc_pow l m g ζ hζ
  have hg : ∀ x : Ω, g (g⁻¹ x) = x := by
    intro x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
  have hconjρ : (g * u * g⁻¹) ρ = ζ ^ k * ρ := by
    obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = g⁻¹ ρ / ρ := ⟨_, rfl⟩
    have hξ : g⁻¹ ρ = ξ * ρ := by rw [hξdef, div_mul_cancel₀ _ hρ0]
    have hξ1 : ξ ^ (l ^ m) = 1 := hξdef ▸ hroot g⁻¹
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hξ, map_mul, hfix ξ hξ1, huρ,
      show ξ * (ζ * ρ) = ζ * (ξ * ρ) by ring, map_mul, ← hξ, hg, hgζ]
  have hgu : g * u * g⁻¹ ∈ fixMu ℚ Ω F := by
    rw [hmem]
    intro x hx
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, (hmem u).mp hu (g⁻¹ x) (by rw [← map_pow, hx, map_one]), hg]
  have hukm : u ^ k ∈ fixMu ℚ Ω F := Subgroup.pow_mem _ hu k
  obtain ⟨v, hvdef⟩ : ∃ v, v = (u ^ k)⁻¹ * (g * u * g⁻¹) := ⟨_, rfl⟩
  have hv : v ∈ fixMu ℚ Ω F := hvdef ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hukm) hgu
  have hvρ : v ρ = ρ := by
    rw [hvdef, AlgEquiv.mul_apply, hconjρ, ← hpow k, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hsplit : g * u * g⁻¹ = u ^ k * v := by rw [hvdef, mul_inv_cancel_left]
  have hf1 : f 1 = 0 := by
    have h1 := hadd 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at h1
    simpa using h1
  have hfpow : ∀ n : ℕ, f (u ^ n) = n • f u := by
    intro n
    induction n with
    | zero => rw [pow_zero, hf1, zero_smul]
    | succ n ih => rw [pow_succ, hadd _ (Subgroup.pow_mem _ hu n) _ hu, ih, succ_nsmul]
  have hγ : (γ g : O) • f u = k • f u := by
    rw [← hconj g u hu, hsplit, hadd _ hukm _ hv, hfixρ v hv hvρ, add_zero, hfpow]
  have hχ : (chiO ℚ Ω l O g : O) • f u = k • f u := by
    obtain ⟨t, ht⟩ := dvd_sub_val l m ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l])
    rw [← hkdef] at ht
    have hz : ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = (k : ℤ_[l]) + (l : ℤ_[l]) ^ m * t := sub_eq_iff_eq_add'.mp ht
    have hc : (chiO ℚ Ω l O g : O) = algebraMap ℤ_[l] O ((cycZ ℚ Ω l g : ℤ_[l]ˣ) : ℤ_[l]) := rfl
    have hlm : ((l : O) ^ m) • f u = 0 := by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul O (l ^ m) (f u), htor u hu]
    rw [hc, hz, map_add (f := _), map_mul, map_pow, map_natCast, map_natCast, add_smul, mul_comm, mul_smul, hlm,
      smul_zero, add_zero, Nat.cast_smul_eq_nsmul O k (f u)]
  rw [sub_smul, hγ, hχ, sub_self]
end

