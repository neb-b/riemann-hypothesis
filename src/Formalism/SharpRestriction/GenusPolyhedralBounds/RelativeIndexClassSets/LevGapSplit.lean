module

public import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Gaps.LevGap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.MainNotions.Gaps.LG
open scoped Pointwise

theorem int_dvd_of_mem_span {E : Type*} [Field E] [NumberField E] (N a : ℤ)
    (h : (a : 𝓞 E) ∈ Ideal.span {(N : 𝓞 E)}) : N ∣ a := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  by_cases hN : N = 0
  · subst hN
    simp only [Int.cast_zero, mul_zero] at hz
    have : a = 0 := by exact_mod_cast hz.symm
    simp [this]
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN
  have hzE' : (z : E) * (N : E) = (a : E) := by
    have := congrArg (fun t : 𝓞 E => (t : E)) hz
    simpa using this
  have hzE : (z : E) = algebraMap ℚ E ((a : ℚ) / N) := by
    rw [map_div₀, eq_div_iff (by simpa using hNE)]
    simpa using hzE'
  have hint : IsIntegral ℤ ((a : ℚ) / N) := by
    have : IsIntegral ℤ (z : E) := RingOfIntegers.isIntegral_coe z
    rw [hzE] at this
    exact (isIntegral_algebraMap_iff ).1 this
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨m, ?_⟩
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have : (a : ℚ) = N * m := by
    have h2 : (m : ℚ) = (a : ℚ) / N := by simpa using hm
    rw [h2]; field_simp
  exact_mod_cast this

theorem norm_congr_one {E : Type*} [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (T M : ℕ) (pz : 𝓞 E)
    (hpz : (pz : E) * c (pz : E) = (T : E)) (hcong : (pz - 1) ∈ Ideal.span {(M : 𝓞 E)}) :
    (M : ℤ) ∣ (T : ℤ) - 1 := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hcong
  set c' : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv (c : E ≃+* E) with hc'
  have hT : (T : 𝓞 E) = pz * c' pz := by
    apply RingOfIntegers.ext
    have : ((c' pz : 𝓞 E) : E) = c (pz : E) := rfl
    show ((T : 𝓞 E) : E) = (pz : E) * ((c' pz : 𝓞 E) : E)
    rw [this, hpz]; simp
  have hp : pz = 1 + y * M := by rw [hy]; ring
  have hcp : c' pz = 1 + c' y * M := by rw [hp]; simp
  apply int_dvd_of_mem_span (E := E)
  rw [Ideal.mem_span_singleton']
  refine ⟨y + c' y + y * c' y * M, ?_⟩
  push_cast
  rw [hT, hcp]
  linear_combination (-(1 + c' y * M)) * hp

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem liesOver_of_natCast_mem {K : Type} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  refine ⟨?_⟩
  have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 K) p ∈ v.asIdeal
    simpa using hv
  have := v.isPrime
  exact hpM.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle

end Gen

section Fix

variable {E : Type} [Field E] [NumberField E] (F : Subfield E) [NumberField F]

variable {F} (c : E ≃ₐ[ℚ] E) (hF : ∀ x : E, x ∈ F ↔ c x = x) (hc : ∀ x : E, c (c x) = x)




end Fix

section HostInst

variable {R : Ranks} (H : Host R) (T : ℕ) (pz : 𝓞 H.E)
  (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
  (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})

include hpz hcong

theorem T_congr : ((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : ℤ) ∣ (T : ℤ) - 1 :=
  norm_congr_one H.conj T _ pz hpz hcong

theorem T_split_E (hT : T.Prime) :
    {v : HeightOneSpectrum (𝓞 H.E) | (T : 𝓞 H.E) ∈ v.asIdeal}.ncard = Module.finrank ℚ H.E := by
  have : Fact T.Prime := ⟨hT⟩
  have hm : T ≡ 1 [MOD H.condN] := by
    refine Nat.ModEq.symm (Nat.modEq_iff_dvd.2 ?_)
    exact (Int.natCast_dvd_natCast.2 (Dvd.intro _ rfl)).trans (T_congr H T pz hpz hcong)
  have h1 : H.condN ≠ 1 := by
    intro h
    have hq : H.q ∣ H.condN := ⟨H.QS * H.d, by show H.QS * H.q * H.d = _; ring⟩
    rw [h] at hq
    exact H.hypOdd.1.one_lt.ne' (Nat.dvd_one.1 hq)
  refine placesOver_ncard_of_split H T ?_
  rw [hm, Nat.one_mod_eq_one.2 h1]

end HostInst

section HostGal

variable {R : Ranks} (H : Host R)

theorem conj_eq_sigmaOf : H.conj = H.sigmaOf (R.cc) := rfl

theorem sigmaOf_mul (g h : R.GG) : H.sigmaOf (g * h) = H.sigmaOf g * H.sigmaOf h :=
  map_mul (H.gal).symm g h

theorem sigmaOf_injective : Function.Injective H.sigmaOf := (H.gal).symm.injective

end HostGal

section Deg

variable {K : Type} [Field K] [NumberField K]

theorem image_places_eq_primesOver (p : ℕ) (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | (p : 𝓞 K) ∈ v.asIdeal} =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  ext I
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_of_natCast_mem p hp v hv⟩
  · rintro ⟨hI, hIl⟩
    have hI0 : I ≠ ⊥ := by
      rintro rfl
      have h0 : Ideal.span {(p : ℤ)} = ⊥ := by
        rw [hIl.over]; exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
      exact hpZ.ne_zero (Ideal.span_singleton_eq_bot.1 h0)
    refine ⟨⟨I, hI, hI0⟩, ?_, rfl⟩
    change ((p : ℕ) : 𝓞 K) ∈ I
    have : (p : ℤ) ∈ I.under ℤ := by rw [← hIl.over]; exact Ideal.mem_span_singleton_self _
    simpa using this

theorem ram_inertia_of_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    v.asIdeal.ramificationIdx ℤ = 1 ∧ v.asIdeal.inertiaDeg ℤ = 1 := by
  classical
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hpM : (Ideal.span {(p : ℤ)}).IsMaximal :=
    hpI.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
  rw [RingOfIntegers.rank, ← hs, ← Set.ncard_image_of_injective _
    (fun v w h => HeightOneSpectrum.ext h), image_places_eq_primesOver p hp,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones] at hsum
  have hle : ∀ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rintro ⟨q, hq, hql⟩
    exact Nat.mul_pos (Ideal.ramificationIdx_pos (R := ℤ) q) (Ideal.inertiaDeg_pos q ℤ)
  have hall := (Finset.sum_eq_sum_iff_of_le (fun q _ => hle q)).1 hsum.symm
    ⟨v.asIdeal, v.isPrime, liesOver_of_natCast_mem p hp v hv⟩ (Finset.mem_univ _)
  exact ⟨Nat.dvd_one.1 ⟨_, hall⟩, Nat.dvd_one.1 ⟨_, hall.trans (mul_comm _ _)⟩⟩

theorem intValuation_of_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) :
    v.intValuation (p : 𝓞 K) = WithZero.exp (-1 : ℤ) := by
  have := v.isPrime
  have hr : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hmap : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hne : (Ideal.span {((p : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hr
  have := liesOver_of_natCast_mem p hp v hv
  have he := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {((p : ℕ) : ℤ)})
    v.asIdeal hne
  rw [hmap, (ram_inertia_of_split p hp hs v hv).1] at he
  rw [v.intValuation_eq_exp_neg_multiplicity hr, ← he]
  rfl

theorem natCast_notMem_sq_of_split (p : ℕ) (hp : p.Prime)
    (hs : {v : HeightOneSpectrum (𝓞 K) | (p : 𝓞 K) ∈ v.asIdeal}.ncard = Module.finrank ℚ K)
    (v : HeightOneSpectrum (𝓞 K)) (hv : (p : 𝓞 K) ∈ v.asIdeal) : (p : 𝓞 K) ∉ v.asIdeal ^ 2 := by
  intro h
  have h1 := (v.intValuation_le_pow_iff_mem (p : 𝓞 K) 2).2 h
  rw [intValuation_of_split p hp hs v hv, WithZero.exp_le_exp] at h1
  norm_num at h1

end Deg

section Two

variable {E : Type} [Field E] [NumberField E] {F : Subfield E} [NumberField F]
  (c : E ≃ₐ[ℚ] E) (hF : ∀ x : E, x ∈ F ↔ c x = x) (hc : ∀ x : E, c (c x) = x)


end Two

section HostDeg

variable {R : Ranks} (H : Host R)

end HostDeg

end Formalism.MainNotions.Gaps.LevGap

end
