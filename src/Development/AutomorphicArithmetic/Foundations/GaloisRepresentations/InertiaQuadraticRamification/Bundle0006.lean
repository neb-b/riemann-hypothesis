module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0230
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0233
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0045
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ValuationLeOneOfInteger
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.AllUnr
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem unramifiedAt_of_dec_fixes (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (hA : IsPlaceOver A w)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  haveI : IsAlgClosure (maximalRealSubfield L) Ω :=
    ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans _ L Ω⟩
  have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield L))) := fun x => by
    rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
    exact hA (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x)
  obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 (maximalRealSubfield L))) w hAv hA
    fun σ hσ => hfix σ (Ine_le_Dec A hσ)
  exact Ideal.ramificationIdx_eq_one_iff.1 he

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.allUnr :
    SplitIff → AllUnr := by
  intro hS Y Ω _ _ _ _ _ T Q hQ w
  by_cases hw : IsSplitAt w
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact unramifiedAt_of_dec_fixes ↥Q.K Ω A w hA ((hS ↥Q.K Ω A w hA).1 hw)
  · exact (hQ.2.2.2.1 w hw).2.1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ApartUp
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_real_lift (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : 𝓞 (maximalRealSubfield K)) :
    ∃ y : 𝓞 (maximalRealSubfield M), algebraMap (𝓞 (maximalRealSubfield M)) (𝓞 M) y =
      algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x) := by
  set y₀ : 𝓞 M := algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x) with hy₀
  have hz : (y₀ : M) = algebraMap K M (((x : maximalRealSubfield K)) : K) := rfl
  have hmem : (y₀ : M) ∈ maximalRealSubfield M := by
    rw [hz]
    exact (mem_maximalRealSubfield_iff _).2 fun φ =>
      (mem_maximalRealSubfield_iff _).1 (x : maximalRealSubfield K).2 (φ.comp (algebraMap K M))
  have hint : IsIntegral ℤ (⟨(y₀ : M), hmem⟩ : maximalRealSubfield M) :=
    (isIntegral_algebraMap_iff (B := M) ).1
      (RingOfIntegers.isIntegral_coe y₀)
  exact ⟨⟨⟨(y₀ : M), hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.apartUp :
    ApartUp := by
  intro K M _ _ _ _ _ _ _
  refine ⟨fun w₁ w₂ hap h => hap ?_, fun v => ?_⟩
  · apply HeightOneSpectrum.ext
    apply Ideal.ext
    intro x
    obtain ⟨y, hy⟩ := exists_real_lift K M x
    have h' : y ∈ (w₁.under (𝓞 (maximalRealSubfield M))).asIdeal ↔
        y ∈ (w₂.under (𝓞 (maximalRealSubfield M))).asIdeal := by rw [h]
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, hy] at h' ⊢
    exact h'
  · have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 M)) := FaithfulSMul.algebraMap_injective _ _
    have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 M)) ≤ v.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le
    haveI := v.isMaximal
    obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 M) v.asIdeal hker
    have hne : Q ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [← hQm, Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
    refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal]
    exact hQm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.CharOrd
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_injective_char (p : ℕ) [Fact p.Prime] :
    ∃ lam0 : (ZMod p)ˣ →* ℂˣ, Function.Injective lam0 :=
  _root_.UpperTheory.Reformulated.B.ExistsInjectiveCharacter.exists_injective_char p

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.charOrd : CharOrd := by
  intro p _ ℓ k a hℓ hdvd
  obtain ⟨lam0, hinj⟩ := exists_injective_char p
  have hm0 : 0 < orderOf (a ^ 2) := orderOf_pos _
  have h2m : orderOf a ∣ 2 * orderOf (a ^ 2) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  have hlk : ℓ ^ k ∣ orderOf (a ^ 2) := by
    have h1 : ℓ ^ (k + 1) ∣ 2 * orderOf (a ^ 2) := hdvd.trans h2m
    by_cases h2 : ℓ = 2
    · subst h2
      rw [pow_succ, mul_comm] at h1
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    · have hc : Nat.Coprime (ℓ ^ (k + 1)) 2 :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hℓ Nat.prime_two).mpr h2)
      exact (Dvd.intro _ (pow_succ ℓ k).symm).trans (hc.dvd_of_dvd_mul_left h1)
  obtain ⟨e, he⟩ := hlk
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      omega
    · exact h
  have hlpos : 0 < ℓ ^ k := pow_pos hℓ.pos k
  refine ⟨lam0 ^ (2 * e), ?_, ?_⟩
  · rw [MonoidHom.pow_apply, pow_mul, ← map_pow]
    simp
  · have h1 : (lam0 ^ (2 * e)) a = (lam0 (a ^ 2)) ^ e := by
      rw [MonoidHom.pow_apply, pow_mul, ← map_pow]
    have h2 : orderOf (lam0 (a ^ 2)) = ℓ ^ k * e := by
      rw [orderOf_injective lam0 hinj, he]
    rw [h1, orderOf_pow' _ hepos.ne', h2, Nat.gcd_eq_right (Dvd.intro_left _ rfl),
      Nat.mul_div_cancel _ hepos]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Double
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem over_under {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
  rw [IsScalarTower.algebraMap_apply F K Ω]
  exact h (algebraMap (𝓞 F) (𝓞 K) x)

private theorem smul_congr {K K' Ω : Type} [Field K] [Field K'] [Field Ω] [Algebra K Ω] [Algebra K' Ω]
    (A : ValuationSubring Ω) (g : G K Ω) (g' : G K' Ω) (hg : ∀ x, g x = g' x) : g • A = g' • A := by
  apply SetLike.coe_injective
  rw [ValuationSubring.coe_pointwise_smul, ValuationSubring.coe_pointwise_smul]
  ext x
  simp only [Set.mem_smul_set, AlgEquiv.smul_def, hg]

private theorem mem_real_of_sq {Y : Type} [Field Y] {δ : Y} {q : ℕ} (hq : 0 < q) (hδ : δ ^ 2 = (q : Y)) :
    δ ∈ maximalRealSubfield Y :=
  _root_.UpperTheory.Reformulated.B.Qh55.mem_real_of_sq hq hδ

private theorem algebraMap_mem_real {E Y : Type} [Field E] [Field Y] [Algebra E Y] {x : E}
    (hx : x ∈ maximalRealSubfield E) : algebraMap E Y x ∈ maximalRealSubfield Y :=
  (mem_maximalRealSubfield_iff _).2 fun φ => (mem_maximalRealSubfield_iff x).1 hx (φ.comp (algebraMap E Y))

private theorem apart_of_moves {E Y Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Y] [NumberField Y] [IsCMField Y]
    [Field Ω] [Algebra E Y] [Algebra E Ω] [Algebra Y Ω] [IsScalarTower E Y Ω] [IsAlgClosure Y Ω] {δ : Y} {q : ℕ} (hq : 0 < q)
    (hδ : δ ^ 2 = (q : Y)) (A : ValuationSubring Ω) (σ : G E Ω) (hσ : σ (algebraMap Y Ω δ) = -algebraMap Y Ω δ)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield E) A, g (algebraMap Y Ω δ) = algebraMap Y Ω δ)
    {w₁ w₂ : HeightOneSpectrum (𝓞 Y)} (hw₁ : IsPlaceOver A w₁) (hw₂ : IsPlaceOver (σ • A) w₂) : GlobalTheory.Cong.Apart w₁ w₂ := by
  intro hv
  haveI : IsAlgClosure (maximalRealSubfield Y) Ω :=
    ⟨IsAlgClosure.isAlgClosed Y, Algebra.IsAlgebraic.trans _ Y Ω⟩
  have h1 := over_under (F := maximalRealSubfield Y) hw₁
  have h2 := over_under (F := maximalRealSubfield Y) hw₂
  rw [← hv] at h2
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver h1 h2
  have hδr : δ ∈ maximalRealSubfield Y := mem_real_of_sq hq hδ
  have hρδ : ρ (algebraMap Y Ω δ) = algebraMap Y Ω δ := ρ.commutes (⟨δ, hδr⟩ : maximalRealSubfield Y)
  have hρF : ∀ x : maximalRealSubfield E, ρ.toRingEquiv (algebraMap (maximalRealSubfield E) Ω x) =
      algebraMap (maximalRealSubfield E) Ω x := fun x => by
    have h := ρ.commutes (⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ : maximalRealSubfield Y)
    have e : algebraMap (maximalRealSubfield Y) Ω ⟨algebraMap E Y x, algebraMap_mem_real x.2⟩ =
        algebraMap (maximalRealSubfield E) Ω x := by
      change algebraMap Y Ω (algebraMap E Y x) = algebraMap E Ω x
      exact (IsScalarTower.algebraMap_apply E Y Ω _).symm
    rw [e] at h
    exact h
  let ρ' : G (maximalRealSubfield E) Ω := AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρF
  let σ' : G (maximalRealSubfield E) Ω := σ.restrictScalars _
  have hg : ρ'⁻¹ * σ' ∈ Dec (F := maximalRealSubfield E) A := mem_Dec.2 (by
    rw [mul_smul, inv_smul_eq_iff, smul_congr A σ' σ (fun _ => rfl), ← hρ, smul_congr A ρ' ρ (fun _ => rfl)])
  have h3 := hfix _ hg
  have h4 : σ' (algebraMap Y Ω δ) = ρ' (algebraMap Y Ω δ) := by
    have := congrArg ρ' h3
    rwa [AlgEquiv.mul_apply, ← AlgEquiv.mul_apply ρ', mul_inv_cancel, AlgEquiv.one_apply] at this
  have h5 : -algebraMap Y Ω δ = algebraMap Y Ω δ := by
    have a : σ' (algebraMap Y Ω δ) = σ (algebraMap Y Ω δ) := rfl
    have b : ρ' (algebraMap Y Ω δ) = ρ (algebraMap Y Ω δ) := rfl
    rw [a, b, hσ, hρδ] at h4
    exact h4
  haveI : CharZero Y := algebraRat.charZero Y
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Y Ω).injective
  have h6 : algebraMap Y Ω δ = 0 := self_eq_neg.1 h5.symm
  have h7 : δ = 0 := (map_eq_zero _).1 h6
  rw [h7] at hδ
  have : (q : Y) = 0 := by simpa using hδ.symm
  exact hq.ne' (by exact_mod_cast this)

theorem double : Double := by
  intro E Ω _ _ _ _ _ _ T Q h0 t ht
  obtain ⟨⟨δ, ⟨⟨q, hq, hδ⟩, _, s, hs, hsδ⟩, hfix⟩, _, _⟩ := h0
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω t
  let σ : G E Ω := AlgEquiv.ofRingEquiv (f := s) (fun x => hs (algebraMap E Ω) x)
  have hA' : IsPlaceOver (σ • A) t := GlobalTheory.NormalClosureSolv.isPlaceOver_smul' hA σ
  obtain ⟨w₁, hw₁⟩ := GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA
  obtain ⟨w₂, hw₂⟩ := GlobalTheory.AbOverSubfield.exists_place_between (K := ↥Q.K) hA'
  exact ⟨w₁, w₂, eq_of_isPlaceOver (over_under hw₁) hA, eq_of_isPlaceOver (over_under hw₂) hA',
    apart_of_moves hq hδ A σ hsδ (hfix t ht A hA) hw₁ hw₂⟩

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.KumMove
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.kumMove :
    MoveRoot → NormVal → KumMove := by
  intro hMR hNV Ω _ _ _ U hU ℓ q hℓ hq
  obtain ⟨b, σ0, hσ0U, hσ0⟩ := hMR Ω U hU ℓ hℓ
  obtain ⟨D, hDpos, hD⟩ := hNV Ω U hU q hq
  obtain ⟨e, D', hD'ℓ, hDe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hDpos.ne' ℓ hℓ.one_lt.ne'
  refine ⟨b + e, fun k hk ζ y hζ hy => ?_⟩
  by_contra hcon
  push_neg at hcon
  haveI : NeZero (ℓ ^ k) := ⟨pow_ne_zero _ hℓ.ne_zero⟩
  have hpow : ∀ τ : G ℚ Ω, ∃ a, τ ζ = ζ ^ a := by
    intro τ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := τ ζ)
      (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  have hact : ∀ (τ : G ℚ Ω) (a : ℕ), τ ζ = ζ ^ a → ∀ ω : Ω, ω ^ (ℓ ^ k) = 1 → τ ω = ω ^ a := by
    intro τ a ha ω hω
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hω
    rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]
  have comm : ∀ σ ∈ U, ∀ τ ∈ U, σ (τ y) = τ (σ y) := by
    intro σ hσ τ hτ
    obtain ⟨a, ha⟩ := hpow σ
    obtain ⟨c, hc⟩ := hpow τ
    have h1 : ((τ * σ)⁻¹ * (σ * τ)) ζ = ζ := by
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
        AlgEquiv.mul_apply, hc, ha, map_pow, map_pow, ha, hc, ← pow_mul, ← pow_mul, mul_comm]
    have h2 := hcon _ (U.mul_mem (U.inv_mem (U.mul_mem hτ hσ)) (U.mul_mem hσ hτ)) h1
    rwa [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, AlgEquiv.mul_apply,
      AlgEquiv.mul_apply] at h2
  have hq0 : (q : Ω) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hy
    exact hq0 hy.symm
  obtain ⟨a0, ha0⟩ := hpow σ0
  obtain ⟨a, ha, ha1⟩ : ∃ a, σ0 ζ = ζ ^ a ∧ 1 ≤ a :=
    ⟨a0 + ℓ ^ k, by rw [ha0, pow_add, hζ.pow_eq_one, mul_one],
      by have := Nat.one_le_pow k ℓ hℓ.pos; omega⟩
  have hjk : ℓ ^ (b + e) ∣ ℓ ^ k := pow_dvd_pow ℓ hk
  have hzfix : ∀ τ ∈ U, τ (σ0 y / y ^ a) = σ0 y / y ^ a := by
    intro τ hτ
    have hτy : (τ y) ^ (ℓ ^ (b + e)) = y ^ (ℓ ^ (b + e)) := by
      rw [← map_pow, hy, map_natCast]
    obtain ⟨χ, hτy'⟩ : ∃ χ, τ y = y * χ := ⟨τ y / y, by field_simp⟩
    have hχj : χ ^ ℓ ^ (b + e) = 1 := by
      rw [hτy', mul_pow] at hτy
      exact mul_left_cancel₀ (pow_ne_zero _ hy0) (hτy.trans (mul_one _).symm)
    have hχ1 : χ ^ (ℓ ^ k) = 1 := by
      obtain ⟨m, hm⟩ := hjk
      rw [hm, pow_mul, hχj, one_pow]
    have hχ0 : χ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ hℓ.ne_zero)] at hχ1
      exact zero_ne_one hχ1
    rw [map_div₀, map_pow, comm τ hτ σ0 hσ0U, hτy', map_mul, hact σ0 a ha χ hχ1, mul_pow]
    exact mul_div_mul_right _ _ (pow_ne_zero _ hχ0)
  have hzeq : (σ0 y / y ^ a) ^ (ℓ ^ (b + e)) * (q : Ω) ^ (a - 1) = 1 := by
    have hσy : (σ0 y) ^ (ℓ ^ (b + e)) = q := by rw [← map_pow, hy, map_natCast]
    rw [div_pow, hσy, ← pow_mul', pow_mul, hy]
    have hqa : (q : Ω) ^ a = (q : Ω) ^ (a - 1) * q := by
      rw [← pow_succ, Nat.sub_add_cancel ha1]
    rw [hqa]
    field_simp
  have hdiv := hD _ (ℓ ^ (b + e)) (a - 1) hzfix hzeq
  have hb : ℓ ^ b ∣ a - 1 := by
    rw [pow_add, hDe] at hdiv
    have h' : ℓ ^ b * ℓ ^ e ∣ ((a - 1) * D') * ℓ ^ e := by
      have : (a - 1) * (ℓ ^ e * D') = ((a - 1) * D') * ℓ ^ e := by ring
      rwa [this] at hdiv
    have h'' := Nat.dvd_of_mul_dvd_mul_right (pow_pos hℓ.pos e) h'
    exact (Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hD'ℓ)).dvd_of_dvd_mul_right h''
  obtain ⟨t, ht⟩ := hb
  have hbk : b ≤ k := by omega
  have hξ : IsPrimitiveRoot (ζ ^ ℓ ^ (k - b)) (ℓ ^ b) := by
    have := hζ.pow_of_dvd (p := ℓ ^ (k - b)) (pow_ne_zero _ hℓ.ne_zero)
      (pow_dvd_pow ℓ (Nat.sub_le k b))
    rwa [Nat.pow_div (Nat.sub_le k b) hℓ.pos, Nat.sub_sub_self hbk] at this
  apply hσ0 _ hξ
  rw [map_pow, ha, ← pow_mul]
  have h1 : a = 1 + ℓ ^ b * t := by rw [← ht]; omega
  have h2 : a * ℓ ^ (k - b) = ℓ ^ (k - b) + ℓ ^ k * t := by
    rw [h1, add_mul, one_mul, mul_comm (ℓ ^ b) t, mul_assoc, ← pow_add,
      Nat.add_sub_cancel' hbk, mul_comm t]
  rw [h2, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.MoveRoot
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.moveRoot :
    MoveRoot := by
  intro Ω _ _ _ U hU ℓ hℓ
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨E, hEfin, hEsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 (hU.mem_nhds U.one_mem)
  haveI := hEfin
  set b := Module.finrank ℚ E + 2 with hb
  have hn : 0 < ℓ ^ b := pow_pos hℓ.pos b
  haveI : NeZero ((ℓ ^ b : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  obtain ⟨ζ0, hζ0⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ b) Ω)
    (Polynomial.degree_cyclotomic_pos _ Ω hn).ne'
  have hprim : IsPrimitiveRoot ζ0 (ℓ ^ b) := Polynomial.isRoot_cyclotomic_iff.1 hζ0
  have hnot : ζ0 ∉ E := by
    intro hmem
    have h0 := minpoly.natDegree_le (A := ℚ) (⟨ζ0, hmem⟩ : E)
    have h0' := IntermediateField.minpoly_eq (K := ℚ) (S := E) ⟨ζ0, hmem⟩
    have h1 : (minpoly ℚ ζ0).natDegree ≤ Module.finrank ℚ E := h0' ▸ h0
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hprim hn,
      Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow hℓ (by omega)] at h1
    have h2 : b - 1 < ℓ ^ (b - 1) := Nat.lt_pow_self hℓ.one_lt
    have h3 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    have h4 : ℓ ^ (b - 1) ≤ Module.finrank ℚ E :=
      (Nat.le_mul_of_pos_right _ h3).trans h1
    generalize ℓ ^ (b - 1) = N at h2 h4
    omega
  have hex : ∃ σ ∈ E.fixingSubgroup, σ ζ0 ≠ ζ0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    rw [← InfiniteGalois.fixedField_fixingSubgroup E, IntermediateField.mem_fixedField_iff]
    exact hcon
  obtain ⟨σ, hσE, hσ⟩ := hex
  refine ⟨b, σ, hEsub hσE, fun ζ hζ hfix => hσ ?_⟩
  haveI : NeZero (ℓ ^ b) := ⟨hn.ne'⟩
  obtain ⟨m, -, hm⟩ := hζ.eq_pow_of_pow_eq_one hprim.pow_eq_one
  rw [← hm, map_pow, hfix]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormVal
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.normVal :
    NormVal := by
  intro Ω _ _ _ U hU q hq
  classical
  set K : IntermediateField ℚ Ω := IntermediateField.fixedField U with hK
  have hfix : K.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩
  have hfin : FiniteDimensional ℚ K := by
    rw [← InfiniteGalois.isOpen_iff_finite, hfix]
    exact hU
  have hq0 : q ≠ 0 := by omega
  have hpp : q.minFac.Prime := Nat.minFac_prime (by omega)
  haveI : Fact q.minFac.Prime := ⟨hpp⟩
  have ha : 0 < padicValNat q.minFac q := by
    rw [Nat.padicValNat_def]
    exact one_le_multiplicity_of_dvd hq0 (Nat.minFac_dvd q)
  refine ⟨Module.finrank ℚ K * padicValNat q.minFac q, Nat.mul_pos Module.finrank_pos ha, ?_⟩
  intro z n c hz hzq
  rcases n with _ | k
  · have h1 : ((q ^ c : ℕ) : Ω) = ((1 : ℕ) : Ω) := by simpa using hzq
    have h2 : q ^ c = 1 := Nat.cast_injective h1
    rcases (Nat.pow_eq_one.1 h2) with h | h
    · omega
    · simp [h]
  have hzK : z ∈ K := (IntermediateField.mem_fixedField_iff U z).2 hz
  set w : K := ⟨z, hzK⟩ with hwdef
  have hw : w ^ (k + 1) * (algebraMap ℚ K (q : ℚ)) ^ c = 1 := by
    apply Subtype.ext
    simpa [hwdef] using hzq
  have hN := congrArg (Algebra.norm ℚ) hw
  rw [map_mul, map_pow, map_pow, Algebra.norm_algebraMap, map_one] at hN
  have hNw : Algebra.norm ℚ w ≠ 0 := by
    intro h0
    rw [h0, zero_pow (Nat.succ_ne_zero k), zero_mul] at hN
    exact zero_ne_one hN
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hv := congrArg (padicValRat q.minFac) hN
  rw [padicValRat.mul (pow_ne_zero _ hNw) (pow_ne_zero _ (pow_ne_zero _ hqQ)),
    padicValRat.pow, padicValRat.pow, padicValRat.pow, padicValRat.one,
    padicValRat.of_nat] at hv
  have hd : ((k + 1 : ℕ) : ℤ) ∣ ((c * (Module.finrank ℚ K * padicValNat q.minFac q) : ℕ) : ℤ) := by
    refine ⟨-padicValRat q.minFac (Algebra.norm ℚ w), ?_⟩
    rw [Nat.padicValNat_def, Nat.cast_mul, Nat.cast_mul]
    linear_combination hv
  exact Int.natCast_dvd_natCast.1 hd
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.SatSplit
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem satSplit : SatSplit := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hD a π P hP B hB
  obtain ⟨i, hi, hi', hiv⟩ := splitIso_holds K M Ω A v w hv hw hD
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL K a π v
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL M a P w
  obtain ⟨e, he⟩ := hP v w i hi hi' σ σ' hσ hσ'
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  have hq : normV w = normV v ^ 1 := degOf K M Ω A v w hv hw (fun τ hτ => hD τ (Ine_le_Dec A hτ)) φ 1 one_pos hφ
    fun k => ⟨fun _ => one_dvd k, fun _ => hD _ (pow_mem (show φ ∈ Dec (F := K) A from hφ.1) k)⟩
  rw [pow_one] at hq
  refine ((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake M a P w σ' hσ').1 B).2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hiv ?_ e (fun g x => (he g x).symm)
    (((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake K a π v σ hσ).1 B).1 hB))
  first | exact hq | (unfold normV at hq; simp only [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hq)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

