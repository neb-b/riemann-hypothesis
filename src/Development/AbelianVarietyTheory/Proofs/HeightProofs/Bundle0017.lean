module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardEqIffStabilizer
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.RaySplit

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.NT
open scoped IntermediateField Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_primesOver (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {Q : HeightOneSpectrum (𝓞 L) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal}.ncard =
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard := by
  have hinj : Function.Injective (fun Q : HeightOneSpectrum (𝓞 L) => Q.asIdeal) :=
    fun Q Q' h => HeightOneSpectrum.ext h
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨Q.isPrime, ⟨hQ.symm⟩⟩
  · rintro ⟨hP, hlies⟩
    refine ⟨⟨P, hP, ?_⟩, hlies.over.symm, rfl⟩
    rintro rfl
    apply 𝔭.ne_bot
    rw [hlies.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
private theorem ncard_primesOver_eq_finrank_iff_frob_eq_one {F R : Type} [Field F]
    [NumberField F] [Field R] [NumberField R] [Algebra F R] [IsGalois F R]
    {𝔭 : HeightOneSpectrum (𝓞 F)} (hu : _root_.GlobalTheory.NT.UnramIn R 𝔭) {σ : Gal(R/F)}
    (hσ : _root_.GlobalTheory.NT.IsFrob R 𝔭 σ) :
    (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank F R ↔ σ = 1 := by
  obtain ⟨P, hPp, hPo, hfrob⟩ := hσ
  haveI := hPp
  haveI := hPo
  have hPne : P ≠ ⊥ := by
    rintro rfl
    apply 𝔭.ne_bot
    rw [hPo.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _
  haveI : P.IsMaximal := hPp.isMaximal hPne
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  have he : 𝔭.asIdeal.ramificationIdxIn (𝓞 R) = 1 := by
    rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(R/F)) 𝔭.asIdeal P]
    have hbot : Ideal.inertia Gal(R/F) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro τ hτ
      exact hu τ ⟨P, hPp, hPo, fun x => (AddSubgroup.mem_inertia.mp hτ) x⟩
    rw [hbot, Subgroup.card_bot]
  have hf : 𝔭.asIdeal.inertiaDegIn (𝓞 R) = Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P Gal(R/F), ← Ideal.inertiaDeg_eq_inertiaDeg' 𝔭.asIdeal P,
      Ideal.inertiaDeg'_algebraMap]
  have hcount :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal (𝓞 R) Gal(R/F)
  rw [he, one_mul, hf, IsGalois.card_aut_eq_finrank] at hcount
  have hdeg : 0 < Module.finrank F R := Module.finrank_pos
  letI : Field (𝓞 F ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 R ⧸ P) := Ideal.Quotient.field _
  letI : Fintype (𝓞 F ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  letI : Fintype (𝓞 R ⧸ P) := Fintype.ofFinite _
  have hq : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hcard : Fintype.card (𝓞 R ⧸ P) =
      Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) ^ Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) :=
    Module.card_eq_pow_finrank
  have hq1 : 1 < Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := Fintype.one_lt_card
  have hsplit : (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank F R ↔
      Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) = 1 := by
    constructor
    · intro h
      rw [h] at hcount
      exact Nat.eq_of_mul_eq_mul_left hdeg (hcount.trans (mul_one _).symm)
    · intro h
      rw [h, mul_one] at hcount
      exact hcount
  rw [hsplit]
  constructor
  · intro h1
    have hcq : Fintype.card (𝓞 R ⧸ P) = Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := by
      rw [hcard, h1, pow_one]
    apply hu σ
    refine ⟨P, hPp, hPo, fun x => ?_⟩
    have hxq : x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, hq, ← hcq]
      exact FiniteField.pow_card _
    have hsum := P.add_mem (hfrob x) hxq
    rwa [sub_add_sub_cancel] at hsum
  · intro h1
    subst h1
    have hall : ∀ y : 𝓞 R ⧸ P, y ^ Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) = y := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hx := hfrob x
      rw [one_smul, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, hq] at hx
      exact hx.symm
    have hroots := Polynomial.card_le_degree_of_subset_roots
      (p := (X ^ Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) - X : (𝓞 R ⧸ P)[X])) (Z := Finset.univ)
      (fun y _ => by
        rw [Polynomial.mem_roots (Polynomial.X_pow_sub_X_ne_zero hq1)]
        simp [hall y])
    rw [Finset.card_univ, Polynomial.natDegree_X_pow_sub_X hq1, hcard] at hroots
    have hle := (Nat.pow_le_pow_iff_right hq1).mp (hroots.trans (pow_one _).symm.le)
    have hpos : 0 < Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) := by
      rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P)) with h0 | h0
      · rw [h0, mul_zero] at hcount
        omega
      · exact h0
    omega

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
private theorem eq_one_iff_forall_char_eq_one_of_finite_commutative {G : Type} [Group G] [Finite G]
    [IsMulCommutative G] (σ : G) : σ = 1 ↔ ∀ χ : G →* ℂˣ, χ σ = 1 := by
  refine ⟨fun h χ => by rw [h, map_one], fun h => ?_⟩
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := mul_comm' }
  by_contra hσ
  haveI : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hσ
  exact hχ (h χ)

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
private theorem heckeIdeal_asIdeal_eq_heckeVal {F R : Type} [Field F] [NumberField F]
    [Field R] [NumberField R] [Algebra F R] (χ : Gal(R/F) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    _root_.GlobalTheory.NT.heckeIdeal R χ 𝔭.asIdeal = _root_.GlobalTheory.NT.heckeVal R χ 𝔭 := by
  unfold _root_.GlobalTheory.NT.heckeIdeal
  have hirr : ∀ 𝔮 : HeightOneSpectrum (𝓞 F), Irreducible (Associates.mk 𝔮.asIdeal) := fun 𝔮 =>
    Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime 𝔮.ne_bot 𝔮.isPrime).irreducible
  rw [finprod_eq_single _ 𝔭]
  · rw [Associates.count_self (hirr 𝔭), pow_one]
  · intro 𝔮 h𝔮
    rw [Associates.count_eq_zero_of_ne (hirr 𝔮) (hirr 𝔭), pow_zero]
    intro h
    exact h𝔮 (HeightOneSpectrum.ext (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)))

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
private theorem false_of_ringHom_real_of_isTotallyComplex {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F]
    (φ : F →+* ℝ) : False := by
  have h := IsTotallyComplex.isComplex (InfinitePlace.mk ((algebraMap ℝ ℂ).comp φ))
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at h
  apply h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]


set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField Pointwise in
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] in
theorem _root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff : ∀ (K R : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (n : ℕ), 0 < n → _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) →
    ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ 𝔭.asIdeal →
      ({Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = 𝔭.asIdeal}.ncard = Module.finrank K R ↔
        ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ Ideal.span {(n : 𝓞 K)}) := by
  intro K R _ _ _ _ _ _ _ n _ hray 𝔭 hn𝔭
  obtain ⟨hunr, -, hart⟩ := hray
  have hnot : ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]
    exact hn𝔭
  have hcop : IsCoprime 𝔭.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := 𝔭.isMaximal.eq_of_le h le_sup_left
    apply hn𝔭
    rw [heq]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hu := hunr 𝔭 hnot
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.NT.exists_isFrob R 𝔭
  rw [_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_primesOver,
    ncard_primesOver_eq_finrank_iff_frob_eq_one hu hσ]
  have hchar : σ = 1 ↔
      ∀ χ : Gal(R/K) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal R χ 𝔭.asIdeal = 1 := by
    refine (eq_one_iff_forall_char_eq_one_of_finite_commutative σ).trans (forall_congr' fun χ => ?_)
    rw [heckeIdeal_asIdeal_eq_heckeVal, _root_.GlobalTheory.NT.heckeVal_of_unramIn R χ hu hσ,
      Units.val_eq_one]
  rw [hchar, hart 𝔭.asIdeal 𝔭.ne_bot hcop]
  constructor
  · rintro ⟨α, β, ⟨-, hβ, -, hβcop, hαβ, -⟩, hI⟩
    have hdvd : β ∣ α := by
      rw [← Ideal.span_singleton_le_span_singleton, ← hI]
      exact Submodule.mul_le.mpr fun a _ b hb => Ideal.mul_mem_left _ a hb
    obtain ⟨π, rfl⟩ := hdvd
    refine ⟨π, ?_, ?_⟩
    · have hβ0 : Ideal.span {β} ≠ 0 := by
        rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      apply mul_right_cancel₀ hβ0
      rw [hI, ← Ideal.span_singleton_mul_span_singleton, mul_comm]
    · rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at hβcop
      obtain ⟨u, hu', v, hv, huv⟩ := hβcop
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hu'
      have key : π - 1 = c * (β * π - β) + (π - 1) * v := by
        linear_combination (1 - π) * huv
      rw [key]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hαβ) (Ideal.mul_mem_left _ _ hv)
  · rintro ⟨π, hπ, hπ1⟩
    refine ⟨π, 1, ⟨?_, one_ne_zero, ?_, ?_, hπ1, fun φ => (false_of_ringHom_real_of_isTotallyComplex φ).elim⟩, ?_⟩
    · rintro rfl
      exact 𝔭.ne_bot (hπ.trans (Ideal.span_singleton_eq_bot.mpr rfl))
    · rw [← hπ]
      exact hcop
    · rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq]
      exact top_sup_eq _
    · rw [Ideal.span_singleton_one, Ideal.mul_top, hπ]

end GlobalTheory.FieldSize.RaySplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardPrimesEqFinrankOfFrobeniusFixes
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
open scoped Pointwise

namespace GlobalTheory.SplitCriterion

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N]

theorem mem_of_smul_eq (H : Subgroup (N ≃ₐ[K] N)) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ H) (P : Ideal (𝓞 N)) [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal]
    (τ : N ≃ₐ[K] N) (hτ : τ • P = P) : τ ∈ H := by
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 N ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (N ≃ₐ[K] N) P
  have hu : P.under (𝓞 K) = 𝔭.asIdeal := hPo.over.symm
  set q := Ideal.absNorm 𝔭.asIdeal with hq
  have hq' : q = Nat.card (𝓞 K ⧸ 𝔭.asIdeal) := by rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hσ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ q := fun x => by
    have := hσ x
    rw [hu, ← hq'] at this
    rw [← map_pow, Ideal.Quotient.eq]
    exact this
  have hσH : σ ∈ H := h σ ⟨P, hP, hPo, fun x => by
    rw [← Ideal.Quotient.eq, map_pow]; exact hσ' x⟩
  have hpow : ∀ (i : ℕ) (x : 𝓞 N), Ideal.Quotient.mk P ((σ ^ i) • x) = Ideal.Quotient.mk P x ^ (q ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro x; rw [pow_succ', mul_smul, hσ', ih, ← pow_mul, pow_succ]
  letI : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 N ⧸ P) := Ideal.Quotient.field _
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ 𝔭.asIdeal)
  have : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 K ⧸ 𝔭.asIdeal) p⟩
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (𝓞 K ⧸ 𝔭.asIdeal) p (𝓞 N ⧸ P)
    (Ideal.Quotient.stabilizerHom P 𝔭.asIdeal (N ≃ₐ[K] N) ⟨τ, hτ⟩)
  have hτ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (τ • x) = Ideal.Quotient.mk P x ^ (q ^ i) := fun x => by
    rw [hq', ← hi, Ideal.Quotient.stabilizerHom_apply]
    rfl
  have h1 : σ * τ * (σ ^ i)⁻¹ ∈ H := h _ ⟨P, hP, hPo, fun x => by
    rw [← Ideal.Quotient.eq, map_pow, mul_smul, mul_smul, hσ', hτ', ← hpow, smul_inv_smul]⟩
  have h2 := H.mul_mem (H.mul_mem (H.inv_mem hσH) h1) (H.pow_mem hσH i)
  simpa [mul_assoc] using h2

theorem ncard_primes_eq_finrank_of_frob_fix (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x) :
    {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard
      = Module.finrank K M := by
  have := 𝔭.isPrime
  have hH : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ M.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 (h σ hσ)
  obtain ⟨P, hP, hPo⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 N)))
  let f : (N ≃ₐ[K] N) → Ideal (𝓞 M) := fun σ => (σ⁻¹ • P).under (𝓞 M)
  have hker : ∀ σ τ, f σ = f τ ↔ σ⁻¹ * τ ∈ M.fixingSubgroup := by
    intro σ τ
    constructor
    · intro e
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 M) (𝓞 N) (N ≃ₐ[M] N)
        (σ⁻¹ • P) (τ⁻¹ • P) e
      have hg' : τ⁻¹ • P = (g.restrictScalars K) • (σ⁻¹ • P) := by
        rw [hg]; rfl
      have hgH : g.restrictScalars K ∈ M.fixingSubgroup :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩
      have h1 := mem_of_smul_eq M.fixingSubgroup 𝔭 hH (σ⁻¹ • P) (σ⁻¹ * τ * g.restrictScalars K) (by
        rw [mul_smul, ← hg', mul_smul, smul_inv_smul])
      exact (M.fixingSubgroup.mul_mem_cancel_right hgH).1 h1
    · intro e
      have e' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 e
      ext x
      simp only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]
      have : (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x := by
        apply RingOfIntegers.ext
        exact e' _ (x : M).2
      rw [mul_smul, inv_smul_eq_iff] at this
      rw [this]
  have hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨inferInstance, ⟨?_⟩⟩
      simp only [f]
      rw [Ideal.under_under]
      exact Ideal.LiesOver.over
    · rintro ⟨hQ, hQo⟩
      obtain ⟨P', hP', hPo'⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 N)))
      have : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q _
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P'
        (hPo.over.symm.trans this.over)
      exact ⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩
  have hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) ''
      {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩
    · rintro ⟨hQ, hQo⟩
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩
  rw [← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr,
    IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq,
    ← Nat.card_congr (Setoid.quotientKerEquivRange f)]
  have : Setoid.ker f = QuotientGroup.leftRel M.fixingSubgroup := by
    ext σ τ
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply, hker]
  rw [this]
  rfl

end GlobalTheory.SplitCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.QuotientEqLinearPowCharOfDerivativeEqZero
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory

theorem quotient_eq_linear_pow_char_of_derivative_eq_zero
    (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (A D : k[X]) (hD : D ≠ 0)
    (hA : A.natDegree ≤ p) (hDp : D.natDegree < p)
    (hder : derivative A * D = A * derivative D) (hnc : ¬ ∃ c : k, A = C c * D) :
    ∃ a b c : k, a ≠ 0 ∧ c ≠ 0 ∧ D = C c ∧ A = C c * (C a * X ^ p + C b) := by
  classical
  have hp : p.Prime := Fact.out
  have hA0 : A ≠ 0 := fun h => hnc ⟨0, by simp [h]⟩
  obtain ⟨A₁, D₁, hA₁, hD₁, hu⟩ := extract_gcd A D
  have hcop : IsCoprime A₁ D₁ := (gcd_isUnit_iff A₁ D₁).1 hu
  generalize gcd A D = g at hA₁ hD₁
  subst hA₁ hD₁
  have hg : g ≠ 0 := left_ne_zero_of_mul hD
  have hD1 : D₁ ≠ 0 := right_ne_zero_of_mul hD
  have hA1 : A₁ ≠ 0 := right_ne_zero_of_mul hA0
  have h1 : derivative A₁ * D₁ = A₁ * derivative D₁ := by
    have h2 : g ^ 2 * (derivative A₁ * D₁) = g ^ 2 * (A₁ * derivative D₁) := by
      simp only [derivative_mul] at hder
      linear_combination hder
    exact mul_left_cancel₀ (pow_ne_zero 2 hg) h2
  have hdvd : D₁ ∣ derivative D₁ :=
    hcop.symm.dvd_of_dvd_mul_left ⟨derivative A₁, by rw [← h1, mul_comm]⟩
  have hD' : derivative D₁ = 0 := by
    by_contra hne
    exact absurd (degree_le_of_dvd hdvd hne) (not_le.2 (degree_derivative_lt hD1))
  have hA' : derivative A₁ = 0 := by
    rw [hD', mul_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_right hD1
  rw [natDegree_mul hg hA1] at hA
  rw [natDegree_mul hg hD1] at hDp
  have eD := expand_contract p hD' hp.ne_zero
  have eA := expand_contract p hA' hp.ne_zero
  have nD := natDegree_expand p (contract p D₁)
  have nA := natDegree_expand p (contract p A₁)
  rw [eD] at nD
  rw [eA] at nA
  have hD0 : D₁.natDegree = 0 := by
    rcases Nat.eq_zero_or_pos (contract p D₁).natDegree with h | h
    · rw [nD, h, zero_mul]
    · have := Nat.le_mul_of_pos_left p h
      omega
  obtain ⟨d, rfl⟩ := natDegree_eq_zero.1 hD0
  have hd : d ≠ 0 := by
    rintro rfl
    exact hD1 (map_zero _)
  have hm : (contract p A₁).natDegree = 1 := by
    rcases Nat.lt_trichotomy (contract p A₁).natDegree 1 with h | h | h
    · exfalso
      have h0 : (contract p A₁).natDegree = 0 := by omega
      rw [h0, zero_mul] at nA
      obtain ⟨a, rfl⟩ := natDegree_eq_zero.1 nA
      refine hnc ⟨a * d⁻¹, ?_⟩
      have : (C a : k[X]) = C (a * d⁻¹) * C d := by
        rw [← map_mul, inv_mul_cancel_right₀ hd]
      rw [this]
      simp only [map_mul]
      ring
    · exact h
    · exfalso
      have h2 : 2 * p ≤ (contract p A₁).natDegree * p := Nat.mul_le_mul_right p h
      have := hp.pos
      omega
  rw [hm, one_mul] at nA
  have hg0 : g.natDegree = 0 := by omega
  obtain ⟨γ, rfl⟩ := natDegree_eq_zero.1 hg0
  have hγ : γ ≠ 0 := by
    rintro rfl
    exact hg (map_zero _)
  obtain ⟨a, ha, b, hab⟩ := natDegree_eq_one.1 hm
  refine ⟨a * d⁻¹, b * d⁻¹, γ * d, mul_ne_zero ha (inv_ne_zero hd), mul_ne_zero hγ hd,
    (map_mul _ _ _).symm, ?_⟩
  have hdd : (C d : k[X]) * C d⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  rw [← eA, ← hab]
  simp only [map_add (f := _), map_mul, expand_C, expand_X]
  linear_combination (-(C γ * (C a * X ^ p + C b))) * hdd

end GlobalTheory
end

