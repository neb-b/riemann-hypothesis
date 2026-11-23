module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.QuotientMetricDivisors.Bundle0002
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002

@[expose] public section

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.DivAssembly
section
open Finset

noncomputable section

namespace Formalism.DivisionValues

theorem divisor_inequality_assembly : DivAssembly := by
  intro J Pl _ _ TT _ muC mu0 Lpass logκ Fo Eb hu hP mlam e6 eP logOm logT kk hK eK pq a w phν nν fa
    eE δ h1 h2 h3 h4 h5 h6 h7 h8
  have hpt : ∀ j ρ, pq j * w j ρ * logOm + phν j ρ - fa j ρ - nν j ρ * logOm ≤
      (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) - a ρ * logOm else 0) + eE j ρ +
        |pq j - kk| * |w j ρ| * |logOm| + |δ j ρ| * |logOm| := by
    intro j ρ
    have e7 := h7 j ρ
    rw [h8 j ρ]
    have hA : (pq j - kk) * w j ρ * logOm ≤ |pq j - kk| * |w j ρ| * |logOm| := by
      calc _ ≤ |(pq j - kk) * w j ρ * logOm| := le_abs_self _
        _ = _ := by rw [abs_mul, abs_mul]
    have hB : -(δ j ρ * logOm) ≤ |δ j ρ| * |logOm| := by rw [← abs_mul]; exact neg_le_abs _
    split_ifs at e7 ⊢ with hρ <;> linarith
  have hsum : ∑ j, ∑ ρ, (pq j * w j ρ * logOm + phν j ρ - fa j ρ - nν j ρ * logOm) ≤
      ∑ j, ∑ ρ, ((if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) - a ρ * logOm else 0) + eE j ρ +
        |pq j - kk| * |w j ρ| * |logOm| + |δ j ρ| * |logOm|) :=
    sum_le_sum fun j _ => sum_le_sum fun ρ _ => hpt j ρ
  have hite : (∑ ρ : Pl, (if ρ ∈ TT then Formalism.LatticeIndexTer.ph (a ρ) - a ρ * logOm else 0)) =
      ∑ t ∈ TT, (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) := by
    rw [← sum_filter]
    congr 1
    ext x; simp
  have hK' : ∑ j, hK j ≤ ∑ j, ((∑ ρ, (phν j ρ - nν j ρ * logOm)) + eK j) :=
    sum_le_sum fun j _ => h4 j
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum hK'
  rw [hite] at hsum
  have hTT : ∑ t ∈ TT, ((Fintype.card J : ℝ) * (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) - a t * logT) =
      (Fintype.card J : ℝ) * ∑ t ∈ TT, (Formalism.LatticeIndexTer.ph (a t) - a t * logOm) - ∑ t ∈ TT, a t * logT := by
    rw [sum_sub_distrib, mul_sum]
  rw [hTT]
  linarith

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondComplementParameterBounds
section
open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

namespace PlaceSumConjugation

section Places

variable {K : Type} [Field K] [NumberField K]

theorem vw_nat_nonneg (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ vw w (g : K) := by
  unfold vw
  have h : (g : K) = algebraMap (𝓞 K) K (g : 𝓞 K) := by simp
  rw [h, ← FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.count_coe_nonneg

theorem lw_pos (w : HeightOneSpectrum (𝓞 K)) : 0 < lw w := by
  unfold lw
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  have h2 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
    exact_mod_cast (by omega : 1 < Ideal.absNorm w.asIdeal)
  apply div_pos (Real.log_pos h2)
  exact_mod_cast Module.finrank_pos

theorem plOver_mem {g : ℕ} (hg : 0 < g) (w : HeightOneSpectrum (𝓞 K)) (h : PlOver g w) :
    (g : 𝓞 K) ∈ w.asIdeal := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold PlOver vw at h
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ] at h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    exact_mod_cast h
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h1
  exact h1

end Places

section Star

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_conj_nat (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    vw (conjPl w) (g : K) = vw w (g : K) := by
  rw [← ValuationRepresentative.vw_star, star_natCast]

end Star

end PlaceSumConjugation

open PlaceSumConjugation

theorem places_over_coprime : PlOverCoprime := by
  unfold PlOverCoprime
  intro K _ _ g g' hcop w ⟨h1, h2⟩
  have hpos : ∀ n : ℕ, PlOver n w → 0 < n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      unfold PlOver vw at hn
      first | simp [FractionalIdeal.count_zero] at hn | (unfold FractionalIdeal.count at hn; simp at hn)
    · exact h0
  have m1 := plOver_mem (hpos g h1) w h1
  have m2 := plOver_mem (hpos g' h2) w h2
  have hab : (Nat.gcdA g g') * (g : ℤ) + (Nat.gcdB g g') * (g' : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab g g'
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    push_cast at this
    linarith
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : 𝓞 K) = ((Nat.gcdA g g' : ℤ) : 𝓞 K) * (g : 𝓞 K) + ((Nat.gcdB g g' : ℤ) : 𝓞 K) * (g' : 𝓞 K) := by
    exact_mod_cast hab.symm
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m1) (Ideal.mul_mem_left _ _ m2)

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.VwEqZeroOfNotMem
section
open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ValuationZeroReduction

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_eq_zero_of_not_mem (w : HeightOneSpectrum (𝓞 K)) (s : 𝓞 K) (hs : s ∉ w.asIdeal) :
    vw w (s : K) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {s} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hs0
  classical
  have hnd : ¬ w.asIdeal ∣ Ideal.span {s} := by
    rw [Ideal.dvd_span_singleton]; exact hs
  have hirr : Irreducible w.asIdeal := (Ideal.prime_of_isPrime w.ne_bot w.isPrime).irreducible
  have hc := mt (Associates.count_ne_zero_iff_dvd hJ hirr).mp hnd
  push_neg at hc
  unfold vw
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w hJ, Nat.cast_eq_zero]
  convert hc

end ValuationZeroReduction

theorem reduction_first_step : StepA := by
  intro K _ _ _ w n D M π ι B P ζ σ hζ hvζ hP hM x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ w.asIdeal := hs
  obtain ⟨y, hy, hyx⟩ := hsx
  obtain ⟨F, hF, hFy⟩ := hy
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hFy hyx
  have hs0 : s ≠ 0 := fun h => hs' (h ▸ w.asIdeal.zero_mem)
  have hsK : algebraMap (𝓞 K) K s ≠ 0 := by
    intro h; apply hs0; apply IsFractionRing.injective (𝓞 K) K; rw [map_zero]; exact h
  have hPF : P F = ζ * (algebraMap (𝓞 K) K s * B x) := by
    rw [hP F, hFy, hyx, ← algebraMap_smul K s x, map_smul, smul_eq_mul]
  have hvmul : ∀ a b : K, a ≠ 0 → b ≠ 0 → vw w (a * b) = vw w a + vw w b := by
    intro a b ha hb
    unfold vw
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K w
      (fun h => ha (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))
      (fun h => hb (FractionalIdeal.spanSingleton_eq_zero_iff.mp h))]
  have hv0 : vw w (algebraMap (𝓞 K) K s) = 0 := ValuationZeroReduction.vw_eq_zero_of_not_mem w s hs'
  by_cases hBx : B x = 0
  · exact Or.inl hBx
  · right
    have hPF0 : P F ≠ 0 := by rw [hPF]; exact mul_ne_zero hζ (mul_ne_zero hsK hBx)
    rcases hM F hF with h0 | hσ
    · exact absurd h0 hPF0
    · rw [hPF, hvmul _ _ hζ (mul_ne_zero hsK hBx), hvmul _ _ hsK hBx, hvζ, hv0] at hσ
      simpa using hσ

end Formalism.DivisionValues
end
end

