module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers

@[expose] public section

noncomputable section
namespace GlobalTheory.NT.Model
open NumberField IsDedekindDomain GlobalTheory.NT

theorem absNorm_eq (p : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm p.asIdeal = (Rat.HeightOneSpectrum.primesEquiv p : ℕ) := by
  have h1 : p.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator p : ℕ) : 𝓞 ℚ)} := by
    have h2 := congrArg (Ideal.comap (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)))
      (Rat.HeightOneSpectrum.span_natGenerator p)
    rw [Ideal.comap_map_of_bijective _ (RingEquiv.bijective _)] at h2
    rw [← h2, ← Ideal.map_symm, Ideal.map_span, Set.image_singleton]
    simp
  rw [h1, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  rfl

theorem pow_eq_pow_iff_modEq_of_isPrimitiveRoot {R : Type} [CommRing R] [IsDomain R] {ζ : R} {m : ℕ} [NeZero m] (h : IsPrimitiveRoot ζ m)
    {a b : ℕ} : ζ ^ a = ζ ^ b ↔ a ≡ b [MOD m] := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨m, NeZero.pos m, h.pow_eq_one⟩
  rw [h.eq_orderOf]
  exact hfin.pow_eq_pow_iff_modEq

private theorem mulSupport_heckeVal_pow_count_finite {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (χ : (L ≃ₐ[K] L) →* ℂˣ) {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    (Function.mulSupport fun 𝔭 : HeightOneSpectrum (𝓞 K) =>
      heckeVal L χ 𝔭 ^ (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors).Finite := by
  refine (Ideal.finite_factors hI).subset fun 𝔭 h => ?_
  simp only [Function.mem_mulSupport] at h
  have h0 : (Associates.mk 𝔭.asIdeal).count (Associates.mk I).factors ≠ 0 := fun h0 => h (by rw [h0, pow_zero])
  exact (Associates.count_ne_zero_iff_dvd hI 𝔭.irreducible).mp h0

section Cyc
open IsCyclotomicExtension.Rat

variable {K : Type} (L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem heckeIdeal_mul (χ : (L ≃ₐ[K] L) →* ℂˣ) {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) :
    heckeIdeal L χ (I * J) = heckeIdeal L χ I * heckeIdeal L χ J := by
  unfold heckeIdeal
  rw [← finprod_mul_distrib (mulSupport_heckeVal_pow_count_finite L χ hI) (mulSupport_heckeVal_pow_count_finite L χ hJ)]
  refine finprod_congr fun 𝔭 => ?_
  rw [← Associates.mk_mul_mk, Associates.count_mul (Associates.mk_ne_zero.mpr hI)
    (Associates.mk_ne_zero.mpr hJ) (Associates.irreducible_mk.mpr 𝔭.irreducible), pow_add]

theorem heckeIdeal_prime (χ : (L ≃ₐ[K] L) →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 K)) :
    heckeIdeal L χ 𝔮.asIdeal = heckeVal L χ 𝔮 := by
  unfold heckeIdeal
  rw [finprod_eq_single _ 𝔮 fun 𝔭 h => ?_]
  · rw [Associates.count_self (Associates.irreducible_mk.mpr 𝔮.irreducible), pow_one]
  · have hne : Associates.mk 𝔭.asIdeal ≠ Associates.mk 𝔮.asIdeal := fun heq =>
      h (IsDedekindDomain.HeightOneSpectrum.ext
        (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp heq)))
    rw [Associates.count_eq_zero_of_ne (Associates.irreducible_mk.mpr 𝔭.irreducible)
      (Associates.irreducible_mk.mpr 𝔮.irreducible) hne, pow_zero]

theorem heckeIdeal_top (χ : (L ≃ₐ[K] L) →* ℂˣ) : heckeIdeal L χ 1 = 1 := by
  unfold heckeIdeal
  rw [Associates.mk_one, Associates.factors_one]
  refine finprod_eq_one_of_forall_eq_one fun 𝔭 => ?_
  rw [Associates.count_zero (Associates.irreducible_mk.mpr 𝔭.irreducible), pow_zero]

private theorem galEquivZMod_eq_of_sub_zeta_pow_mem (m : ℕ) [NeZero m] (F : Type) [Field F] [NumberField F]
    [IsCyclotomicExtension {m} ℚ F] (𝔭 : HeightOneSpectrum (𝓞 ℚ))
    (hp : (Ideal.absNorm 𝔭.asIdeal).Coprime m) (P : Ideal (𝓞 F)) (hPp : P.IsPrime)
    (hLies : P.LiesOver 𝔭.asIdeal) (σ : F ≃ₐ[ℚ] F) (e : ℕ)
    (hmem : σ • (IsCyclotomicExtension.zeta_spec m ℚ F).toInteger -
      (IsCyclotomicExtension.zeta_spec m ℚ F).toInteger ^ e ∈ P) :
    ((IsCyclotomicExtension.Rat.galEquivZMod m F σ : (ZMod m)ˣ) : ZMod m) = e := by
  have hζ := (IsCyclotomicExtension.zeta_spec m ℚ F).toInteger_isPrimitiveRoot

  have hpP : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 F) ∈ P := by
    have h1 : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) ∈ 𝔭.asIdeal := Ideal.absNorm_mem _
    have h3 : algebraMap (𝓞 ℚ) (𝓞 F) ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) ∈ P :=
      (le_of_eq hLies.over : 𝔭.asIdeal ≤ P.under (𝓞 ℚ)) h1
    rwa [map_natCast] at h3
  have hcopP : (Ideal.absNorm P).Coprime m := by
    have hd : Ideal.absNorm P ∣ Ideal.absNorm 𝔭.asIdeal ^ Module.finrank ℤ (𝓞 F) := by
      rw [← Ideal.absNorm_span_natCast]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hpP)
    exact Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left _ hp)

  have h₀ := hζ.idealQuotient_mk (fun h1 => hPp.ne_top (Ideal.absNorm_eq_one_iff.mp h1)) hcopP
  rw [IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq m F σ hζ.pow_eq_one, ← Ideal.Quotient.eq,
    map_pow, map_pow] at hmem
  have hmod := (pow_eq_pow_iff_modEq_of_isPrimitiveRoot h₀).mp hmem
  rwa [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val] at hmod

variable (m : ℕ) [NeZero m] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F]

theorem gal_of_isFrob (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (hp : (Ideal.absNorm 𝔭.asIdeal).Coprime m) {σ : F ≃ₐ[ℚ] F}
    (h : IsFrob F 𝔭 σ) : ((galEquivZMod m F σ : (ZMod m)ˣ) : ZMod m) = (Ideal.absNorm 𝔭.asIdeal : ℕ) := by
  unfold IsFrob at h
  obtain ⟨P, hPp, hLies, hP⟩ := h
  exact galEquivZMod_eq_of_sub_zeta_pow_mem m F 𝔭 hp P hPp hLies σ _ (hP _)
end Cyc

section Cyc2
open IsCyclotomicExtension.Rat
variable (m : ℕ) [NeZero m] (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F]

theorem unramIn_cyc (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (hp : (Ideal.absNorm 𝔭.asIdeal).Coprime m) : UnramIn F 𝔭 := by
  unfold UnramIn
  intro σ hσ
  unfold InInertia at hσ
  obtain ⟨P, hPp, hLies, hP⟩ := hσ
  have h1 := galEquivZMod_eq_of_sub_zeta_pow_mem m F 𝔭 hp P hPp hLies σ 1 (by rw [pow_one]; exact hP _)
  have h2 : galEquivZMod m F σ = 1 := Units.ext (by rw [h1]; simp)
  exact (MulEquiv.map_eq_one_iff _).mp h2

def galChar (ψ : DirichletCharacter ℂ m) : (F ≃ₐ[ℚ] F) →* ℂˣ :=
  (MulChar.toUnitHom ψ).comp (galEquivZMod m F).toMonoidHom

theorem heckeVal_galChar (ψ : DirichletCharacter ℂ m) (𝔭 : HeightOneSpectrum (𝓞 ℚ))
    (hp : (Ideal.absNorm 𝔭.asIdeal).Coprime m) :
    heckeVal F (galChar m F ψ) 𝔭 = ψ (Ideal.absNorm 𝔭.asIdeal : ℕ) := by

  have hex : ∃ σ, IsFrob F 𝔭 σ := by
    have := 𝔭.isMaximal
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) 𝔭.asIdeal
    have : Finite (𝓞 F ⧸ Q) :=
      Ring.HasFiniteQuotients.finiteQuotient (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q)
    have := IsCyclotomicExtension.isGalois {m} ℚ F
    have hact : ∀ (τ : F ≃ₐ[ℚ] F) (y : 𝓞 F), galRestrict (𝓞 ℚ) ℚ F (𝓞 F) τ y = τ • y := fun τ y =>
      NumberField.RingOfIntegers.ext (by exact algebraMap_galRestrict_apply (A := 𝓞 ℚ) (K := ℚ) (L := F) (B := 𝓞 F) τ y)
    letI := IsIntegralClosure.MulSemiringAction (𝓞 ℚ) ℚ F (𝓞 F)
    have : SMulCommClass (F ≃ₐ[ℚ] F) (𝓞 ℚ) (𝓞 F) :=
      ⟨fun σ a x => map_smul (galRestrict (𝓞 ℚ) ℚ F (𝓞 F) σ) a x⟩
    have : Algebra.IsInvariant (𝓞 ℚ) (𝓞 F) (F ≃ₐ[ℚ] F) := Algebra.isInvariant_of_isGalois (𝓞 ℚ) ℚ F (𝓞 F)
    obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 ℚ) (F ≃ₐ[ℚ] F) Q
    refine ⟨σ, Q, hQm.isPrime, hQ, fun x => ?_⟩
    have h1 := hσ x
    rw [← hQ.over, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, MulSemiringAction.toAlgHom_apply] at h1
    have h2 : galRestrict (𝓞 ℚ) ℚ F (𝓞 F) σ x - x ^ Ideal.absNorm 𝔭.asIdeal ∈ Q := h1
    rwa [hact] at h2
  have hin : ∀ σ, InInertia F 𝔭 σ → galChar m F ψ σ = 1 := fun σ hσ => by
    rw [unramIn_cyc m F 𝔭 hp σ hσ, map_one]
  have hcond : (∀ σ, InInertia F 𝔭 σ → galChar m F ψ σ = 1) ∧ ∃ σ, IsFrob F 𝔭 σ := ⟨hin, hex⟩
  unfold heckeVal
  rw [dite_eq_left hcond]
  have hs := gal_of_isFrob m F 𝔭 hp hcond.2.choose_spec
  simp only [galChar, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulChar.coe_toUnitHom]
  rw [hs]

theorem heckeIdeal_galChar (ψ : DirichletCharacter ℂ m) (I : Ideal (𝓞 ℚ)) (hI : I ≠ 0)
    (hp : (Ideal.absNorm I).Coprime m) : heckeIdeal F (galChar m F ψ) I = ψ (Ideal.absNorm I : ℕ) := by

  let g : Ideal (𝓞 ℚ) →* ℂ := ψ.toMonoidHom.comp
    ((Nat.castRingHom (ZMod m)).toMonoidHom.comp (Ideal.absNorm (S := 𝓞 ℚ)).toMonoidHom)
  have hg : ∀ J, g J = ψ (Ideal.absNorm J : ℕ) := fun J => rfl
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 ℚ) => v.maxPowDividing I).Finite := by
    refine (Ideal.finite_factors hI).subset fun v hv => ?_
    simp only [Function.mem_mulSupport] at hv
    have h0 : (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 := fun h0 =>
      hv (by rw [HeightOneSpectrum.maxPowDividing, h0, pow_zero])
    exact (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp h0
  have hterm : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      heckeVal F (galChar m F ψ) v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors =
        g (v.maxPowDividing I) := fun v => by
    rw [HeightOneSpectrum.maxPowDividing, map_pow, hg]
    by_cases hk : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0
    · rw [hk, pow_zero, pow_zero]
    · have hdvd : v.asIdeal ∣ I := (Associates.count_ne_zero_iff_dvd hI v.irreducible).mp hk
      have hcop : (Ideal.absNorm v.asIdeal).Coprime m :=
        Nat.Coprime.coprime_dvd_left (Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)) hp
      rw [heckeVal_galChar m F ψ v hcop]
  unfold heckeIdeal
  rw [finprod_congr hterm, ← g.map_finprod hfin, Ideal.finprod_heightOneSpectrum_factorization hI, hg]

theorem absNorm_span_int (a : ℤ) : Ideal.absNorm (Ideal.span {(a : 𝓞 ℚ)}) = a.natAbs := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 ℚ)), Algebra.norm_algebraMap,
    NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]

theorem exists_int (α : 𝓞 ℚ) : ∃ a : ℤ, α = a := by
  obtain ⟨a, ha⟩ := Rat.int_algebraMap_surjective (𝓞 ℚ) α
  exact ⟨a, by rw [← ha, eq_intCast]⟩

theorem int_dvd_of {a b : ℤ} (h : (a : 𝓞 ℚ) ∣ b) : a ∣ b := by
  simpa using map_dvd (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h

theorem isModulus_galChar (ψ : DirichletCharacter ℂ m) :
    IsModulus F (galChar m F ψ) (Ideal.span {((m : ℤ) : 𝓞 ℚ)}) := by
  have hm0 : ((m : ℤ) : 𝓞 ℚ) ≠ 0 := by simpa using NeZero.ne m
  unfold IsModulus
  refine ⟨?_, fun 𝔭 h𝔭 => ?_, fun α β hab => ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact hm0
  ·
    have hpr : (Ideal.absNorm 𝔭.asIdeal).Prime := by
      rw [absNorm_eq]
      exact (Rat.HeightOneSpectrum.primesEquiv 𝔭).2
    have hcop : (Ideal.absNorm 𝔭.asIdeal).Coprime m := by
      rw [Nat.Prime.coprime_iff_not_dvd hpr]
      rintro ⟨k, hk⟩
      apply h𝔭
      rw [Ideal.dvd_span_singleton]
      have hmk : ((m : ℤ) : 𝓞 ℚ) = ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 ℚ) * (k : 𝓞 ℚ) := by
        rw [Int.cast_natCast, hk, Nat.cast_mul]
      rw [hmk]
      exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
    rw [heckeVal_galChar m F ψ 𝔭 hcop]
    have hu : IsUnit ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ZMod m) := by
      rw [← ZMod.coe_unitOfCoprime _ hcop]
      exact Units.isUnit _
    exact (hu.map ψ).ne_zero
  ·
    unfold RayPair at hab
    obtain ⟨hα, hβ, hcα, hcβ, hd, hpos⟩ := hab
    obtain ⟨a, rfl⟩ := exists_int α
    obtain ⟨b, rfl⟩ := exists_int β
    have hcopZ : ∀ c : ℤ, IsCoprime (Ideal.span {(c : 𝓞 ℚ)}) (Ideal.span {((m : ℤ) : 𝓞 ℚ)}) →
        (c.natAbs).Coprime m := by
      intro c hc
      rw [Ideal.isCoprime_span_singleton_iff] at hc
      obtain ⟨u, v, huv⟩ := hc
      obtain ⟨u', rfl⟩ := exists_int u
      obtain ⟨v', rfl⟩ := exists_int v
      have h1 : u' * c + v' * m = 1 := by exact_mod_cast huv
      exact Int.isCoprime_iff_gcd_eq_one.mp ⟨u', v', h1⟩
    have hne : ∀ c : ℤ, (c : 𝓞 ℚ) ≠ 0 → Ideal.span {(c : 𝓞 ℚ)} ≠ 0 := fun c hc => by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hc
    rw [heckeIdeal_galChar m F ψ _ (hne a hα) (by rw [absNorm_span_int]; exact hcopZ a hcα),
      heckeIdeal_galChar m F ψ _ (hne b hβ) (by rw [absNorm_span_int]; exact hcopZ b hcβ),
      absNorm_span_int, absNorm_span_int]
    have hdvd : (m : ℤ) ∣ a - b := int_dvd_of (by push_cast; exact Ideal.mem_span_singleton.mp hd)
    have hab : 0 < a * b := by
      have h := hpos (Rat.castHom ℝ)
      have e1 : (Rat.castHom ℝ) ((a : 𝓞 ℚ) : ℚ) = (a : ℝ) := by simp
      have e2 : (Rat.castHom ℝ) ((b : 𝓞 ℚ) : ℚ) = (b : ℝ) := by simp
      rw [e1, e2] at h
      exact_mod_cast h
    have key : ((a.natAbs : ℤ) : ZMod m) = ((b.natAbs : ℤ) : ZMod m) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      rcases mul_pos_iff.mp hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · rw [Int.natAbs_of_nonneg ha.le, Int.natAbs_of_nonneg hb.le, ← neg_sub]
        exact dvd_neg.mpr hdvd
      · rw [Int.ofNat_natAbs_of_nonpos ha.le, Int.ofNat_natAbs_of_nonpos hb.le, neg_sub_neg]
        exact hdvd
    have key' : ((a.natAbs : ℕ) : ZMod m) = ((b.natAbs : ℕ) : ZMod m) := by
      rwa [Int.cast_natCast, Int.cast_natCast] at key
    rw [key']

theorem condNorm_galChar_le (ψ : DirichletCharacter ℂ m) : condNorm F (galChar m F ψ) ≤ m := by
  unfold condNorm
  have hmem : Ideal.absNorm (Ideal.span {((m : ℤ) : 𝓞 ℚ)}) ∈
      {n | ∃ 𝔪, IsModulus F (galChar m F ψ) 𝔪 ∧ Ideal.absNorm 𝔪 = n} :=
    ⟨_, isModulus_galChar m F ψ, rfl⟩
  refine (Nat.sInf_le hmem).trans ?_
  rw [absNorm_span_int]
  simp

theorem eq_one_of_isModulus (ψ : DirichletCharacter ℂ m) {𝔪 : Ideal (𝓞 ℚ)} (h : IsModulus F (galChar m F ψ) 𝔪)
    (c : ℕ) (hc : (1 + Ideal.absNorm 𝔪 * c).Coprime m) : ψ ((1 + Ideal.absNorm 𝔪 * c : ℕ) : ZMod m) = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 1 + Ideal.absNorm 𝔪 * c := ⟨_, rfl⟩
  rw [← ha] at hc ⊢
  have hmem : ((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ) ∈ 𝔪 := by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem 𝔪)
  have hα0 : ((a : ℕ) : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by rw [ha]; omega)
  have hsub : ((a : ℕ) : 𝓞 ℚ) - 1 = ((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ) := by
    rw [ha]
    push_cast
    ring

  have hcop : IsCoprime (Ideal.span {((a : ℕ) : 𝓞 ℚ)}) 𝔪 := by
    rw [Ideal.isCoprime_iff_exists]
    refine ⟨(a : 𝓞 ℚ), Ideal.mem_span_singleton_self _, -((Ideal.absNorm 𝔪 * c : ℕ) : 𝓞 ℚ),
      𝔪.neg_mem hmem, ?_⟩
    rw [← hsub]
    ring
  have hray : RayPair 𝔪 ((a : ℕ) : 𝓞 ℚ) 1 := by
    unfold RayPair
    refine ⟨hα0, one_ne_zero, hcop, ?_, ?_, fun φ => ?_⟩
    · rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq, top_sup_eq]
    · rw [hsub]
      exact hmem
    · have hpos : 0 < a := by omega
      simpa using hpos
  unfold IsModulus at h
  have heq := h.2.2 _ _ hray
  have hN : Ideal.absNorm (Ideal.span {((a : ℕ) : 𝓞 ℚ)}) = a := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one]
  have hI : Ideal.span {((a : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hα0
  have key := heckeIdeal_galChar m F ψ _ hI (by rw [hN]; exact hc)
  rw [hN] at key
  rw [← key, heq, Ideal.span_singleton_one, ← Ideal.one_eq_top, heckeIdeal_top]

end Cyc2

theorem condNorm_four (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] (ψ : DirichletCharacter ℂ 4)
    (hψ : ψ 3 ≠ 1) : condNorm F (galChar 4 F ψ) = 4 := by
  apply le_antisymm (condNorm_galChar_le 4 F ψ)
  unfold condNorm
  refine le_csInf ⟨_, _, isModulus_galChar 4 F ψ, rfl⟩ ?_
  rintro n ⟨𝔪, h𝔪, rfl⟩
  have hne : Ideal.absNorm 𝔪 ≠ 0 := by
    have h := h𝔪
    unfold IsModulus at h
    exact fun h0 => h.1 (Ideal.absNorm_eq_zero_iff.mp h0)

  by_contra hlt
  push Not at hlt
  have key : ∀ k : ℕ, (k : ZMod 4) = 3 → ψ (k : ZMod 4) = 1 → ψ 3 = 1 := fun k hk h => hk ▸ h
  apply hψ
  have hcases : Ideal.absNorm 𝔪 = 1 ∨ Ideal.absNorm 𝔪 = 2 ∨ Ideal.absNorm 𝔪 = 3 := by omega
  rcases hcases with h | h | h
  · exact key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 2 (by rw [h]; decide))
  · exact key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 1 (by rw [h]; decide))
  · exact key _ (by rw [h]; decide) (eq_one_of_isModulus 4 F ψ h𝔪 2 (by rw [h]; decide))

theorem bigQ_four (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {4} ℚ F] : bigQ ℚ F = 4 := by

  have hall : ∀ χ : (F ≃ₐ[ℚ] F) →* ℂˣ, condNorm F χ ≤ 4 := fun χ => by
    have hχ : galChar 4 F (MulChar.ofUnitHom (χ.comp (IsCyclotomicExtension.Rat.galEquivZMod 4 F).symm.toMonoidHom)) = χ := by
      refine MonoidHom.ext fun σ => Units.ext ?_
      simp only [galChar, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe, MulEquiv.symm_apply_apply]
    rw [← hχ]
    exact condNorm_galChar_le 4 F _

  let ψ4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
  have h3 : ψ4 3 ≠ 1 := by
    have e : ZMod.χ₄ 3 = -1 := by decide
    rw [MulChar.ringHomComp_apply, e]
    norm_num
  have hsup : (⨆ χ : (F ≃ₐ[ℚ] F) →* ℂˣ, condNorm F χ) = 4 := by
    apply le_antisymm (ciSup_le hall)
    exact (condNorm_four F ψ4 h3).symm.le.trans
      (le_ciSup ⟨4, by rintro _ ⟨χ, rfl⟩; exact hall χ⟩ (galChar 4 F ψ4))
  unfold bigQ
  rw [hsup]
  simp

end GlobalTheory.NT.Model
end
