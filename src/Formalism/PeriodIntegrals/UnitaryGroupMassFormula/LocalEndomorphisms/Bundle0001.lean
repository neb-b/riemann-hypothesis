module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.ValSurjective
public import Formalism.PeriodIntegrals.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.HenselRoot
section
open NumberField IsDedekindDomain Polynomial Filter Topology

namespace PI.LocalEndW

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem norm_le_one_of_mem (a : v.adicCompletionIntegers F) : ‖(a : v.adicCompletion F)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr a.2

theorem mem_pow_smul_top_iff (ϖ : v.adicCompletionIntegers F) (hϖ : ϖ ≠ 0) (n : ℕ)
    (x : v.adicCompletionIntegers F) :
    x ∈ ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F)) ↔
      ‖(x : v.adicCompletion F)‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers (K := F) (v := v)).dvd_iff_le, ← norm_pow,
    Valued.toNormedField.norm_le_iff]
  simp

theorem isAdicComplete (ϖ : v.adicCompletionIntegers F) (hϖ : ϖ ≠ 0)
    (h1 : ‖(ϖ : v.adicCompletion F)‖ < 1) :
    IsAdicComplete (Ideal.span {ϖ}) (v.adicCompletionIntegers F) := by
  have hr0 : 0 < ‖(ϖ : v.adicCompletion F)‖ := norm_pos_iff.mpr (fun h => hϖ (Subtype.ext h))
  have key : ∀ (n : ℕ) (x y : v.adicCompletionIntegers F),
      x ≡ y [SMOD ((Ideal.span {ϖ}) ^ n • ⊤ : Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F))] ↔
        ‖(x : v.adicCompletion F) - y‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := by
    intro n x y
    rw [SModEq.sub_mem, mem_pow_smul_top_iff v ϖ hϖ]
    simp
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h : ∀ n : ℕ, ‖(x : v.adicCompletion F)‖ ≤ ‖(ϖ : v.adicCompletion F)‖ ^ n := fun n => by
      simpa using (key n x 0).mp (hx n)
    have hx0 : ‖(x : v.adicCompletion F)‖ ≤ 0 :=
      ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le h1) h
    exact Subtype.ext (norm_le_zero_iff.mp hx0)
  · intro f hf
    have hc : ∀ n : ℕ, dist (f n : v.adicCompletion F) (f (n + 1)) ≤ 1 * ‖(ϖ : v.adicCompletion F)‖ ^ n := fun n => by
      rw [dist_eq_norm, one_mul]
      exact (key n _ _).mp (hf n.le_succ)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ 1 h1 hc)
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm (fun n => norm_le_one_of_mem v (f n))
    refine ⟨⟨L, Valued.toNormedField.norm_le_one_iff.mp hL1⟩, fun n => ?_⟩
    rw [key]
    have ht : Tendsto (fun m => ‖(f n : v.adicCompletion F) - f m‖) atTop (𝓝 ‖(f n : v.adicCompletion F) - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    exact le_of_tendsto ht (eventually_atTop.mpr ⟨n, fun m hm => (key n _ _).mp (hf hm)⟩)

theorem henselRoot : HenselRoot := by
  intro F _ _ v ℓ u hℓ hu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have hϖ1 : ‖(ϖ : v.adicCompletion F)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff]
    have hnu : ¬ IsUnit ϖ := hϖ.not_isUnit
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hnu
    exact lt_of_le_of_ne ϖ.2 hnu
  have := isAdicComplete v ϖ hϖ.ne_zero hϖ1
  have hu1 : Valued.v u ≤ 1 := by
    have hsplit : u = (u - 1) + 1 := by ring
    rw [hsplit]
    exact (Valuation.map_add _ _ _).trans (max_le hu.le (by simp))
  have hℓ0 : ℓ ≠ 0 := by
    rintro rfl
    simp at hℓ
  have hev : ((X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F))).eval 1 ∈ Ideal.span {ϖ} := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    intro h
    have h' : Valued.v (u - 1) = 1 := by
      rw [← Valuation.map_neg]
      simpa using h
    exact hu.ne h'
  have hdu : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ}) ((derivative (X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F))).eval 1)) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C,
      eval_pow, eval_X, one_pow, mul_one]
    apply IsUnit.map
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    simpa using hℓ
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian (I := Ideal.span {ϖ})
    (X ^ ℓ - C (⟨u, hu1⟩ : v.adicCompletionIntegers F)) (monic_X_pow_sub_C _ hℓ0) 1 hev hdu
  refine ⟨a, ?_⟩
  have ha' : a ^ ℓ = (⟨u, hu1⟩ : v.adicCompletionIntegers F) := by
    simpa [Polynomial.IsRoot, sub_eq_zero] using ha
  simpa using congrArg Subtype.val ha'

end PI.LocalEndW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.IntVal
section
open NumberField IsDedekindDomain WithZero

namespace PI.LocalEndW

section
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

lemma val_natCast (n : ℕ) :
    Valued.v ((n : v.adicCompletion F)) = v.intValuation (n : 𝓞 F) := by
  have h := v.valuedAdicCompletion_eq_valuation (K := F) (n : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h
  simpa using h

lemma exists_N : ∃ N : ℕ, 0 < N ∧ ∃ m : ℕ, 0 < m ∧
    Valued.v ((N : v.adicCompletion F)) = exp (-(m : ℤ)) ∧
    ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → Valued.v ((ℓ : v.adicCompletion F)) = 1 := by
  set N := Ideal.absNorm v.asIdeal with hN
  have hNmem : ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hNpos : 0 < N := by
    rw [Nat.pos_iff_ne_zero, hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hN0 : ((N : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hlt : v.intValuation (N : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hNmem
  have hne : v.intValuation (N : 𝓞 F) ≠ 0 := v.intValuation_ne_zero _ hN0
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (N : 𝓞 F) = exp k := ⟨_, (exp_log hne).symm⟩
  have hk0 : k < 0 := by rw [hk, ← exp_zero, exp_lt_exp] at hlt; exact hlt
  refine ⟨N, hNpos, (-k).toNat, by omega, ?_, ?_⟩
  · rw [val_natCast, hk]; congr 1; omega
  · intro ℓ hℓ hNℓ
    rw [val_natCast, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl, Ideal.mem_primeCompl_iff]
    intro hmem
    have hcop : Nat.Coprime ℓ N :=
      (Nat.Prime.coprime_iff_not_dvd hℓ).2 (Nat.not_dvd_of_pos_of_lt hNpos hNℓ)
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (a : 𝓞 F) * (ℓ : 𝓞 F) + (b : 𝓞 F) * (N : 𝓞 F) = 1 := by
      have := congrArg (Int.cast : ℤ → 𝓞 F) hab
      push_cast at this
      exact this
    have : (1 : 𝓞 F) ∈ v.asIdeal := by
      rw [← h1]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hmem) (v.asIdeal.mul_mem_left _ hNmem)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

lemma le_one_of_pow_eq {N ℓ m : ℕ} (hm : 0 < m) (hmℓ : m < ℓ)
    (hN : Valued.v ((N : v.adicCompletion F)) = exp (-(m : ℤ)))
    {y z : v.adicCompletion F} (h : z ^ ℓ = 1 + N * y ^ ℓ) : Valued.v y ≤ 1 := by
  by_contra hy
  rw [not_le] at hy
  have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v y = exp a := ⟨_, (exp_log hy0).symm⟩
  have ha1 : 0 < a := by rw [ha, ← exp_zero, exp_lt_exp] at hy; exact hy
  have hNy : Valued.v ((N : v.adicCompletion F) * y ^ ℓ) = exp ((ℓ : ℤ) * a - m) := by
    rw [map_mul, map_pow, hN, ha, ← exp_nsmul, ← exp_add]; congr 1; simp; ring
  have hgt : Valued.v (1 : v.adicCompletion F) < Valued.v ((N : v.adicCompletion F) * y ^ ℓ) := by
    rw [hNy, map_one, ← exp_zero, exp_lt_exp]; nlinarith
  have hsum : Valued.v (1 + (N : v.adicCompletion F) * y ^ ℓ) = exp ((ℓ : ℤ) * a - m) := by
    rw [Valuation.map_add_eq_of_lt_right _ hgt, hNy]
  have hz0 : Valued.v z ≠ 0 := by
    intro h0
    rw [← h, map_pow, h0, zero_pow (by omega)] at hsum
    exact exp_ne_zero hsum.symm
  obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v z = exp c := ⟨_, (exp_log hz0).symm⟩
  rw [← h, map_pow, hc, ← exp_nsmul, exp_inj] at hsum
  simp only [nsmul_eq_mul] at hsum
  have hd : (ℓ : ℤ) ∣ (m : ℤ) := ⟨a - c, by linarith⟩
  have := Int.le_of_dvd (by omega) hd
  omega

end

theorem intOfHensel : IntOfHensel := by
  intro hH F _ _ v τ x hx
  obtain ⟨N, hNpos, m, hm, hNv, hℓ⟩ := exists_N v
  obtain ⟨ℓ, hge, hprime⟩ := Nat.exists_infinite_primes (N + m + 1)
  have hℓ1 := hℓ ℓ hprime (by omega)
  have hu : Valued.v ((1 + (N : v.adicCompletion F) * x ^ ℓ) - 1) < 1 := by
    rw [add_sub_cancel_left, map_mul, map_pow, hNv]
    calc exp (-(m : ℤ)) * Valued.v x ^ ℓ ≤ exp (-(m : ℤ)) * 1 :=
          by gcongr; exact pow_le_one₀ zero_le hx
      _ < 1 := by rw [mul_one, ← exp_zero, exp_lt_exp]; omega
  obtain ⟨z, hz⟩ := hH F v ℓ _ hℓ1 hu
  have hτ : (τ z) ^ ℓ = 1 + (N : v.adicCompletion F) * (τ x) ^ ℓ := by
    rw [← map_pow, hz, map_add (f := _), map_one, map_mul, map_natCast, map_pow]
  exact le_one_of_pow_eq v hm (by omega) hNv hτ

theorem valOfInt : ValOfInt := by
  intro hI F _ _ v τ x
  obtain ⟨N, hNpos, m, hm, hNv, -⟩ := exists_N v
  have h1 : ∀ y : v.adicCompletion F, Valued.v y = 1 → Valued.v (τ y) = 1 := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have ht : Valued.v (τ y) ≠ 0 := by simp [hy0]
    apply le_antisymm (hI F v τ y hy.le)
    have h2 := hI F v τ y⁻¹ (by rw [map_inv₀, hy, inv_one])
    rw [map_inv₀, map_inv₀] at h2
    calc (1 : ℤᵐ⁰) = Valued.v (τ y) * (Valued.v (τ y))⁻¹ := (mul_inv_cancel₀ ht).symm
      _ ≤ Valued.v (τ y) * 1 := by gcongr
      _ = _ := mul_one _
  by_cases hx : x = 0
  · simp [hx]
  have hx0 : Valued.v x ≠ 0 := by simpa using hx
  have htx0 : Valued.v (τ x) ≠ 0 := by simp [hx]
  obtain ⟨a, ha⟩ : ∃ a : ℤ, Valued.v x = exp a := ⟨_, (exp_log hx0).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, Valued.v (τ x) = exp b := ⟨_, (exp_log htx0).symm⟩
  have hy : Valued.v (x ^ m * (N : v.adicCompletion F) ^ a) = 1 := by
    rw [map_mul, map_pow, map_zpow₀, ha, hNv, ← exp_nsmul, ← exp_zsmul, ← exp_add, ← exp_zero]
    congr 1; simp; ring
  have hτy := h1 _ hy
  rw [map_mul, map_pow, map_zpow₀, map_natCast, map_mul, map_pow, map_zpow₀, hb, hNv, ← exp_nsmul,
    ← exp_zsmul, ← exp_add, ← exp_zero, exp_inj] at hτy
  simp only [nsmul_eq_mul, smul_eq_mul] at hτy
  have hmb : (m : ℤ) * (b - a) = 0 := by linarith
  rcases mul_eq_zero.1 hmb with h | h
  · omega
  · rw [ha, hb]; congr 1; linarith

end PI.LocalEndW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.IsUniformInducingOfVal
section
open NumberField IsDedekindDomain Uniformity

namespace PI.LocalEndW

theorem isUniformInducing_of_val {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (τ : v.adicCompletion F →+* v.adicCompletion F) (hτ : ∀ x, Valued.v (τ x) = Valued.v x) :
    IsUniformInducing τ := by
  have hb := Valued.hasBasis_uniformity (v.adicCompletion F) _
  have hτ' : ∀ y, Valued.v.restrict (τ y) = Valued.v.restrict y := fun y =>
    le_antisymm
      (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))
      (not_lt.1 fun h => lt_irrefl (Valued.v y) (by rw [Valuation.restrict_lt_iff, hτ] at h; exact h))
  refine ⟨(hb.comap _).ext hb (fun γ _ => ⟨γ, trivial, ?_⟩) (fun γ _ => ⟨γ, trivial, ?_⟩)⟩
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
    rw [← map_sub, hτ']
    exact hp
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hp ⊢
    rwa [← map_sub, hτ'] at hp

theorem valContinuous : ValContinuous := fun _ _ _ _ τ hτ => (isUniformInducing_of_val τ hτ).uniformContinuous.continuous

end PI.LocalEndW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.LocalEndHomeoOf
section
open NumberField IsDedekindDomain

namespace PI.LocalEndW

theorem localEndHomeo_of (hA : HenselRoot) (hB1 : IntOfHensel) (hB2 : ValOfInt)
    (hC1 : ValContinuous) (hC2 : ValSurjective) : PI.LocalEndHomeo := by
  have hV : ValPreserved := hB2 (hB1 hA)
  intro F _ _ v τ
  have hτv : ∀ x, Valued.v (τ x) = Valued.v x := hV F v τ
  have hsurj := hC2 F v τ hτv
  let e := RingEquiv.ofBijective τ ⟨τ.injective, hsurj⟩
  refine ⟨hC1 F v τ hτv, e.symm.toRingHom, ?_, fun a => e.apply_symm_apply a⟩
  apply hC1 F v
  intro x
  have := hτv (e.symm x)
  rw [show τ (e.symm x) = x from e.apply_symm_apply x] at this
  exact this.symm

end PI.LocalEndW
end

