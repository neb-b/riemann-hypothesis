module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.ToricVarieties.Dimension
section
namespace GroundTheory.Arith.Toric

universe u

open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra

section IntegralDim

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

theorem ringKrullDim_le_of_isIntegral : ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ hpq =>
    Ideal.IsIntegral.comap_lt_comap (R := R) hpq

theorem exists_ltSeries_lift (hinj : Function.Injective (algebraMap R A))
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ l' : LTSeries (PrimeSpectrum A), l'.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R A) l'.last = l.last := by
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, -, hQ, hQx⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal (⊥ : Ideal A)
      (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
    exact ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, PrimeSpectrum.ext hQx⟩
  | snoc p x hx ih =>
    obtain ⟨l', hlen, hlast⟩ := ih
    have hle : l'.last.asIdeal.comap (algebraMap R A) ≤ x.asIdeal := by
      have := congrArg PrimeSpectrum.asIdeal hlast
      rw [PrimeSpectrum.comap_asIdeal] at this
      rw [this]
      exact le_of_lt hx
    obtain ⟨Q, hQle, hQ, hQx⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal l'.last.asIdeal hle
    have hlt : l'.last < ⟨Q, hQ⟩ := by
      refine lt_of_le_of_ne hQle fun h => ?_
      have h1 : PrimeSpectrum.comap (algebraMap R A) l'.last = x := by
        rw [h]; exact PrimeSpectrum.ext hQx
      exact (ne_of_lt hx) (hlast.symm.trans h1)
    exact ⟨l'.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], PrimeSpectrum.ext (by simpa using hQx)⟩

theorem ringKrullDim_le_of_isIntegral_of_injective (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim R ≤ ringKrullDim A := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l => ?_
  obtain ⟨l', hlen, -⟩ := exists_ltSeries_lift hinj l
  exact le_iSup_of_le l' (by rw [hlen])

theorem ringKrullDim_eq_of_isIntegral (hinj : Function.Injective (algebraMap R A)) :
    ringKrullDim A = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral (ringKrullDim_le_of_isIntegral_of_injective hinj)

end IntegralDim

section Trdeg

variable {k G : Type u} [CommRing k] [IsDomain k] [AddCommGroup G] [Module.Free ℤ G]

variable [Module.Finite ℤ G]

end Trdeg

section Dim

variable {k N : Type u} [Field k] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]

end Dim

end GroundTheory.Arith.Toric
end

-- bundled from GroundTheory.ArithmeticGeometry.ToricVarieties.KrullDomain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Toric

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]


omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] in
theorem smul_mk_eq_zero_iff {b r y : A} :
    r • (Ideal.Quotient.mk (Ideal.span {b}) y) = 0 ↔ b ∣ r * y := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

theorem height_eq_one_of_isAssociatedPrime {b : A} (hb : b ≠ 0) {P : Ideal A}
    (hP : IsAssociatedPrime P (A ⧸ Ideal.span {b})) : P.height = 1 := by
  classical
  obtain ⟨hPp, yb, hPy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective yb
  have hmem : ∀ r, r ∈ P ↔ b ∣ r * y := by
    intro r
    rw [hPy, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_mk_eq_zero_iff]
  have hbP : b ∈ P := (hmem b).2 (dvd_mul_right b y)
  have hP0 : P ≠ ⊥ := fun h => hb (by rw [h] at hbP; exact (Submodule.mem_bot _).1 hbP)
  by_cases hcase : ∀ r s : A, r ∈ P → r * y = b * s → s ∈ P
  · exfalso
    let K := FractionRing A
    have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have hN0 : N ≠ ⊥ := by
      intro h
      have : algebraMap A K b ∈ N := Submodule.mem_map.2 ⟨b, hbP, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hb (hinj (by rw [this, map_zero]))
    have hbK : algebraMap A K b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hint : IsIntegral A (algebraMap A K y / algebraMap A K b) := by
      refine isIntegral_of_smul_mem_submodule N hN0 hNfg _ ?_
      intro n hn
      obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      refine Submodule.mem_map.2 ⟨s, hcase r s hr hs, ?_⟩
      change algebraMap A K s = (algebraMap A K y / algebraMap A K b) * algebraMap A K r
      rw [div_mul_eq_mul_div, eq_div_iff hbK, ← map_mul, ← map_mul, mul_comm y r, hs, mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hyz : y = b * z := by
      apply hinj
      rw [map_mul, hz, mul_div_cancel₀ _ hbK]
    apply hPp.ne_top
    rw [Ideal.eq_top_iff_one, hmem, one_mul, hyz]
    exact dvd_mul_right b z
  · push Not at hcase
    obtain ⟨r₀, s₀, hr₀, hrs, hs₀⟩ := hcase
    have hmin : P ∈ (Ideal.span {r₀}).minimalPrimes := by
      refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 hr₀⟩, fun Q hQ hQP => ?_⟩
      obtain ⟨hQp, hQr⟩ := hQ
      intro r hr
      obtain ⟨s, hs⟩ := (hmem r).1 hr
      have key : r * s₀ = r₀ * s := by
        apply mul_left_cancel₀ hb
        calc b * (r * s₀) = r * (b * s₀) := by ring
          _ = r * (r₀ * y) := by rw [hrs]
          _ = r₀ * (r * y) := by ring
          _ = b * (r₀ * s) := by rw [hs]; ring
      have hin : r * s₀ ∈ Q := by
        rw [key]
        exact Q.mul_mem_right s ((Ideal.span_singleton_le_iff_mem _).1 hQr)
      exact (hQp.mem_or_mem hin).resolve_right fun h => hs₀ (hQP h)
    have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {r₀}) P hmin
    have hne : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.1 h)
    exact le_antisymm hle (Order.one_le_iff_ne_zero.2 hne)

theorem mem_range_of_forall_height_one {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (x : K) (h : ∀ p : Ideal A, p.IsPrime → p.height = 1 →
      ∃ a s : A, s ∉ p ∧ x * algebraMap A K s = algebraMap A K a) :
    x ∈ (algebraMap A K).range := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hbK : algebraMap A K b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))
  by_cases hab : b ∣ a
  · obtain ⟨c, rfl⟩ := hab
    exact ⟨c, by rw [map_mul, mul_div_cancel_left₀ _ hbK]⟩
  · exfalso
    have hne : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hab
    obtain ⟨P, hP, hcol⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hne
    obtain ⟨a', s, hs, hx⟩ := h P hP.isPrime (height_eq_one_of_isAssociatedPrime hb0 hP)
    apply hs
    apply hcol
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_mk_eq_zero_iff, mul_comm]
    refine ⟨a', hinj ?_⟩
    rw [map_mul, map_mul, ← hx, div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hbK]

end GroundTheory.Arith.Toric
end

