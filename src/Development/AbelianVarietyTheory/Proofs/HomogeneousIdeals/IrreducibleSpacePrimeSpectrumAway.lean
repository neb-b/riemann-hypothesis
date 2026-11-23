module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsAdicCompleteComapConstantCoeff

@[expose] public section

open PowerSeries

noncomputable section

namespace GlobalTheory.ChartRing

section PrimeX

variable {O : Type*} [CommRing O] [IsDomain O]

instance isPrime_span_X : (Ideal.span {X} : Ideal O⟦X⟧).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime prime_X

omit [IsDomain O] in
theorem mem_span_X_iff {f : O⟦X⟧} : f ∈ (Ideal.span {X} : Ideal O⟦X⟧) ↔ constantCoeff f = 0 := by
  rw [Ideal.mem_span_singleton, X_dvd_iff]

theorem mem_primeCompl_span_X_iff {f : O⟦X⟧} :
    f ∈ (Ideal.span {X} : Ideal O⟦X⟧).primeCompl ↔ constantCoeff f ≠ 0 :=
  mem_span_X_iff.not

theorem algebraMap_X_pow_dvd_iff (M : Submonoid O⟦X⟧) (hM : ∀ m ∈ M, constantCoeff m ≠ 0)
    (S : Type*) [CommRing S] [Algebra O⟦X⟧ S] [IsLocalization M S] (a : ℕ) (f : O⟦X⟧) :
    algebraMap O⟦X⟧ S X ^ a ∣ algebraMap O⟦X⟧ S f ↔ X ^ a ∣ f := by
  refine ⟨fun ⟨z, hz⟩ => ?_, fun h => by simpa using map_dvd (algebraMap O⟦X⟧ S) h⟩
  obtain ⟨⟨g, s⟩, hgs⟩ := IsLocalization.surj M z
  have h1 : algebraMap O⟦X⟧ S (f * s) = algebraMap O⟦X⟧ S (X ^ a * g) := by
    rw [map_mul, map_mul, map_pow, hz, mul_assoc, hgs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).1 h1
  have h2 : X ^ a ∣ ((c * s : M) : O⟦X⟧) * f := ⟨c * g, by
    rw [Submonoid.coe_mul]; linear_combination hc⟩
  exact prime_X.pow_dvd_of_dvd_mul_left a (X_dvd_iff.not.2 (hM _ (c * s).2)) h2

variable (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [hS : IsLocalization.AtPrime S (Ideal.span {X} : Ideal O⟦X⟧)]

theorem algebraMap_X_pow_dvd_iff_atPrime (a : ℕ) (f : O⟦X⟧) :
    algebraMap O⟦X⟧ S X ^ a ∣ algebraMap O⟦X⟧ S f ↔ X ^ a ∣ f :=
  algebraMap_X_pow_dvd_iff _ (fun _ hm => mem_primeCompl_span_X_iff.1 hm) S a f

theorem comap_span_X_pow_atPrime (a : ℕ) :
    (Ideal.span {algebraMap O⟦X⟧ S X ^ a}).comap (algebraMap O⟦X⟧ S) = Ideal.span {X ^ a} := by
  ext f
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    algebraMap_X_pow_dvd_iff_atPrime]


theorem algebraMap_injective_atPrime_X : Function.Injective (algebraMap O⟦X⟧ S) :=
  IsLocalization.injective S (Ideal.span {X} : Ideal O⟦X⟧).primeCompl_le_nonZeroDivisors

theorem isUnit_algebraMap_atPrime_X {f : O⟦X⟧} (hf : constantCoeff f ≠ 0) :
    IsUnit (algebraMap O⟦X⟧ S f) :=
  IsLocalization.map_units S (⟨f, mem_primeCompl_span_X_iff.2 hf⟩ :
    (Ideal.span {X} : Ideal O⟦X⟧).primeCompl)

theorem associated_X_pow_order_atPrime {f : O⟦X⟧} (hf : f ≠ 0) :
    Associated (algebraMap O⟦X⟧ S X ^ f.order.toNat) (algebraMap O⟦X⟧ S f) := by
  conv_rhs => rw [← X_pow_order_mul_divXPowOrder (f := f), map_mul, map_pow]
  exact associated_mul_unit_right _ _
    (isUnit_algebraMap_atPrime_X S (constantCoeff_divXPowOrder_eq_zero_iff.not.2 hf))

theorem prime_algebraMap_X_atPrime : Prime (algebraMap O⟦X⟧ S X) := by
  have hne : algebraMap O⟦X⟧ S X ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_injective_atPrime_X S)).2 X_ne_zero
  rw [← Ideal.span_singleton_prime hne, ← Set.image_singleton, ← Ideal.map_span]
  exact IsLocalization.isPrime_of_isPrime_disjoint (Ideal.span {X} : Ideal O⟦X⟧).primeCompl S _
    inferInstance (Set.disjoint_left.2 fun _ h h' => h h')

theorem exists_associated_X_pow_atPrime {z : S} (hz : z ≠ 0) :
    ∃ n : ℕ, Associated (algebraMap O⟦X⟧ S X ^ n) z := by
  obtain ⟨⟨f, s⟩, hfs⟩ := IsLocalization.surj (Ideal.span {X} : Ideal O⟦X⟧).primeCompl z
  have hs := IsLocalization.map_units S s
  have hf : f ≠ 0 := by
    rintro rfl
    exact hz (hs.mul_left_eq_zero.1 (by simpa using hfs))
  refine ⟨_, (associated_X_pow_order_atPrime S hf).trans ?_⟩
  rw [← hfs]
  exact associated_mul_unit_left _ _ hs


include hS in
include O in
theorem isDiscreteValuationRing_atPrime_X [IsDomain S] : IsDiscreteValuationRing S :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, (prime_algebraMap_X_atPrime (O := O) S).irreducible,
      fun hz => exists_associated_X_pow_atPrime S hz⟩

instance : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {X} : Ideal O⟦X⟧)) :=
  isDiscreteValuationRing_atPrime_X (O := O) _

theorem addVal_algebraMap_atPrime_X [IsDomain S] [IsDiscreteValuationRing S] (f : O⟦X⟧) :
    IsDiscreteValuationRing.addVal S (algebraMap O⟦X⟧ S f) = f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨u, hu⟩ := associated_X_pow_order_atPrime S hf
  rw [IsDiscreteValuationRing.addVal_def _ u (prime_algebraMap_X_atPrime (O := O) S).irreducible
    _ (by rw [← hu, mul_comm]), coe_toNat_order hf]

end PrimeX

section FractionField

variable {O : Type*} [CommRing O] [IsDomain O] (K : Type*) [Field K] [Algebra O K]
  [IsFractionRing O K]


omit [IsDomain O] in
theorem order_map_of_injective {A : Type*} [CommRing A] {φ : O →+* A}
    (hφ : Function.Injective φ) (f : O⟦X⟧) : (f.map φ).order = f.order :=
  le_antisymm (le_order _ _ fun i hi => hφ (by simpa using coeff_of_lt_order i hi))
    (le_order_map φ)

omit [IsDomain O] in
theorem map_algebraMap_injective :
    Function.Injective (PowerSeries.map (algebraMap O K) : O⟦X⟧ →+* K⟦X⟧) :=
  PowerSeries.map_injective _ (IsFractionRing.injective O K)

omit [IsDomain O] in
theorem order_map_algebraMap (f : O⟦X⟧) : (f.map (algebraMap O K)).order = f.order :=
  order_map_of_injective (IsFractionRing.injective O K) f

theorem algebraMap_residueField_span_X (f : O⟦X⟧) :
    algebraMap O⟦X⟧ (Ideal.span {X} : Ideal O⟦X⟧).ResidueField f =
      algebraMap O (Ideal.span {X} : Ideal O⟦X⟧).ResidueField (constantCoeff f) := by
  rw [IsScalarTower.algebraMap_apply O O⟦X⟧, ← sub_eq_zero, ← map_sub,
    Ideal.algebraMap_residueField_eq_zero, mem_span_X_iff]
  simp

instance isFractionRing_residueField_span_X :
    IsFractionRing O (Ideal.span {X} : Ideal O⟦X⟧).ResidueField := by
  have : FaithfulSMul O (Ideal.span {X} : Ideal O⟦X⟧).ResidueField := by
    rw [faithfulSMul_iff_algebraMap_injective, injective_iff_map_eq_zero]
    intro a ha
    rw [IsScalarTower.algebraMap_apply O O⟦X⟧, Ideal.algebraMap_residueField_eq_zero,
      mem_span_X_iff] at ha
    simpa [PowerSeries.algebraMap_apply] using ha
  refine IsFractionRing.of_field _ _ fun z => ?_
  obtain ⟨x, y, -, rfl⟩ :=
    IsFractionRing.div_surjective (A := O⟦X⟧ ⧸ (Ideal.span {X} : Ideal O⟦X⟧)) z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨constantCoeff x, constantCoeff y, by
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      algebraMap_residueField_span_X, algebraMap_residueField_span_X]⟩


variable (O) in
def residueFieldSpanXEquiv : (Ideal.span {X} : Ideal O⟦X⟧).ResidueField ≃ₐ[O] K :=
  IsLocalization.algEquiv (nonZeroDivisors O) _ _

@[simp] theorem residueFieldSpanXEquiv_algebraMap (f : O⟦X⟧) :
    residueFieldSpanXEquiv O K (algebraMap O⟦X⟧ _ f) = algebraMap O K (constantCoeff f) := by
  rw [algebraMap_residueField_span_X, AlgEquiv.commutes]

variable (S : Type*) [CommRing S] [Algebra O⟦X⟧ S]
  [IsLocalization.AtPrime S (Ideal.span {X} : Ideal O⟦X⟧)]


end FractionField

section Away

open AlgebraicGeometry

universe u

variable {R : Type*} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away f S]
include hf

theorem isDomain_away : IsDomain S :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (M := Submonoid.powers f) S
    (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

theorem algebraMap_injective_away : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

theorem irreducibleSpace_primeSpectrum_away : IrreducibleSpace (PrimeSpectrum S) :=
  have := isDomain_away hf S
  inferInstance

theorem connectedSpace_primeSpectrum_away : ConnectedSpace (PrimeSpectrum S) :=
  have := irreducibleSpace_primeSpectrum_away hf S
  inferInstance

theorem denseRange_comap_away : DenseRange (PrimeSpectrum.comap (algebraMap R S)) := by
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot _).1 (algebraMap_injective_away hf S)]
  exact bot_le

omit hf

end Away

end GlobalTheory.ChartRing
