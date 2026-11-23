module

public import Formalism.GaussValuationBounds.Statement
public import Formalism.WindowSums.PowerSeriesRelationList
public import Formalism.FrobeniusContraction.Bundle0001
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound
public import Mathlib
public import Formalism.FrobeniusContraction.HighestWeightResidueAvoids
public import Formalism.GaussValuationBounds.Bundle0001
public import Formalism.GaussValuationBounds.GaussValueContraction.TruncationExponentBounds

@[expose] public section

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.PhiIterXProof
section
noncomputable section

namespace Formalism.NOK

open PowerSeries

theorem base_p_succ {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (B : Formalism.WachCohomologyFacts.Base O A) (s : ℕ) : B.p (s + 1) = B.φ (B.p s) := by
  simp [Formalism.WachCohomologyFacts.Base.p]
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

theorem phiIterX_proof : PhiIterX := by
  intro O A _ _ _ B j
  have hp0 : B.p 0 = B.X + B.ℓ := by simp [Formalism.WachCohomologyFacts.Base.p, Formalism.WachCohomologyFacts.Base.q]
  induction j with
  | zero => exact ⟨1, isUnit_one, by simp⟩
  | succ j ih =>
    obtain ⟨v, hv, hj⟩ := ih
    refine ⟨B.φ v * B.u, (hv.map B.φ).mul B.8, ?_⟩
    rw [Function.iterate_succ_apply', hj, map_mul, map_mul, map_prod, B.12, Finset.prod_range_succ']
    simp only [map_pow, ← base_p_succ]
    rw [hp0]
    ring

theorem psIdeal_proof : PsIdeal := by
  intro O A _ _ _ B s
  have hX : ∀ s, (⇑B.φ)^[s] B.X ∈ Ideal.span {(B.ℓ : A), B.X ^ B.ℓ ^ s} := by
    intro s
    induction s with
    | zero => exact Ideal.subset_span (by simp)
    | succ s ih =>
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp ih
      have hℓ1 : B.ℓ - 1 + 1 = B.ℓ := Nat.sub_add_cancel B.2.one_lt.le
      have hXpow : B.X ^ B.ℓ = B.X ^ (B.ℓ - 1) * B.X := by rw [← pow_succ, hℓ1]
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (B.X + (B.ℓ : A)) B.X (B.ℓ - 1)
      have e3 : B.φ B.X = B.u * B.X ^ B.ℓ + B.u * B.X * c * (B.ℓ : A) := by
        rw [B.12, hXpow]
        linear_combination (B.u * B.X) * hc
      obtain ⟨e, he⟩ := sub_dvd_pow_sub_pow (B.φ B.X) (B.u * B.X ^ B.ℓ) (B.ℓ ^ s)
      have e1 : (⇑B.φ)^[s + 1] B.X = B.φ a * B.ℓ + B.φ b * (B.φ B.X) ^ B.ℓ ^ s := by
        rw [Function.iterate_succ_apply', ← hab, map_add (f := _), map_mul, map_mul, map_pow, map_natCast]
      have e4 : B.X ^ B.ℓ ^ (s + 1) = (B.X ^ B.ℓ) ^ B.ℓ ^ s := by rw [← pow_mul, pow_succ']
      refine Ideal.mem_span_pair.mpr ⟨B.φ a + B.φ b * (B.u * B.X * c) * e, B.φ b * B.u ^ B.ℓ ^ s, ?_⟩
      rw [e1, e4]
      linear_combination (-(B.φ b)) * he - (B.φ b * e) * e3
  have hadd : ∀ s, (⇑B.φ)^[s] (B.X + (B.ℓ : A)) = (⇑B.φ)^[s] B.X + B.ℓ := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', map_add (f := _), map_natCast]
  simp only [Formalism.WachCohomologyFacts.Base.p, Formalism.WachCohomologyFacts.Base.q]
  rw [hadd]
  exact Ideal.add_mem _ (hX s) (Ideal.subset_span (by simp))

theorem dUDeg_proof : DUDeg := by
  intro O _ _ ϖ hϖ ℓ p₀ p₁ v₀ v₁ w s₀ s₁ b₀ b₁ hs hb hv₀ hv₁ hw h₀ h₁ hmem
  haveI hpr : (Ideal.span {ϖ}).IsPrime := (Ideal.span_singleton_prime hϖ.ne_zero).mpr hϖ
  have hϖ0 : (Ideal.Quotient.mk (Ideal.span {ϖ})) ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ)
  have hred : ∀ (p v : PowerSeries O) (N : ℕ), p - v * X ^ N ∈ Ideal.span {C ϖ} →
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p = PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) v * X ^ N := by
    intro p v N h
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨q, hq⟩ := h
    have h0 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) hq
    simp only [map_mul, map_sub, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero, zero_mul] at h0
    exact sub_eq_zero.mp h0
  have hℓ : 1 ≤ ℓ := Nat.pos_of_ne_zero (fun h => by simp [h] at hb)
  have h1 : ℓ ^ s₀ * ℓ ≤ ℓ ^ s₁ := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right hℓ hs
  have h2 : 0 < ℓ ^ s₀ := pow_pos hℓ _
  have hlt : ℓ ^ s₀ * b₀ < ℓ ^ s₁ * b₁ := by nlinarith
  rw [Ideal.mem_span_pair] at hmem
  obtain ⟨a, b, hab⟩ := hmem
  have hm := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) hab
  simp only [map_add (f := _), map_mul, map_pow, PowerSeries.map_C, hϖ0, map_zero, mul_zero, zero_add] at hm
  rw [hred p₀ v₀ _ h₀, hred p₁ v₁ _ h₁, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← mul_assoc] at hm
  have hc := congrArg (PowerSeries.coeff (ℓ ^ s₀ * b₀)) hm
  rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', if_neg (not_le.mpr hlt), if_pos le_rfl,
    Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply] at hc
  have hu : IsUnit (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) w * PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) v₀ ^ b₀) :=
    (hw.map _).mul ((hv₀.map _).pow _)
  exact (hu.map PowerSeries.constantCoeff).ne_zero hc.symm

end Formalism.NOK
end
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.ScaledPowMemSpanCeil
section
namespace Formalism.NOK

theorem scaledPowMemSpanCeil : Trunc := by
  intro A _ ℓ _ hℓ X u p y M j hj hq r
  have hnum := truncationExponentBounds ℓ hℓ y M j r hj
  set c := ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊ with hc
  set σ := sigNOK ℓ y M j with hσ
  have hL : (0 : ℝ) < (ℓ : ℝ) ^ (j - 1) := by positivity
  have hℓ1 : 1 ≤ ℓ := by omega
  by_cases hry : (ℓ - 1) * r < y
  · have h1 : (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) ≤ σ := by
      have h2 := hnum.2
      have h3 : ((ℓ : ℝ) - 1) * r - y - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ 0 := by
        have h4 : (((ℓ - 1) * r : ℕ) : ℝ) < y := by exact_mod_cast hry
        push_cast [Nat.cast_sub hℓ1] at h4
        have h5 : (0 : ℝ) ≤ M / (ℓ : ℝ) ^ (j - 1) := by positivity
        linarith
      rw [max_eq_left h3, sub_zero] at h2
      exact h2
    have hcs : c ≤ σ := Nat.ceil_le.mpr h1
    rw [← Nat.add_sub_cancel' hcs, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · push_neg at hry
    obtain ⟨m, hm⟩ : ∃ m, (ℓ - 1) * r = y + m := ⟨(ℓ - 1) * r - y, by omega⟩
    have hmR : ((ℓ : ℝ) - 1) * r - y = m := by
      have h6 := congrArg (Nat.cast : ℕ → ℝ) hm
      push_cast [Nat.cast_sub hℓ1] at h6
      linarith

    have key : (ℓ : A) ^ σ * X ^ r * p (j - 1) ^ m ∈ Ideal.span {(ℓ : A) ^ c, X ^ M} := by
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hq
      rw [← hab, add_pow, Finset.mul_sum]
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hX : M ≤ r + ℓ ^ (j - 1) * (m - k)
      · have e : (ℓ : A) ^ σ * X ^ r * ((a * ℓ) ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) * (m.choose k : A)) =
            X ^ M * (X ^ (r + ℓ ^ (j - 1) * (m - k) - M) *
              ((ℓ : A) ^ σ * (a * ℓ) ^ k * b ^ (m - k) * (m.choose k : A))) := by
          rw [← mul_assoc (X ^ M), ← pow_add, Nat.add_sub_cancel' hX, pow_add, pow_mul]
          ring
        rw [e]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
      · have hcs : c ≤ σ + k := by
          apply Nat.ceil_le.mpr
          have h2 := hnum.2
          have h5 : ((ℓ ^ (j - 1) * (m - k) : ℕ) : ℝ) < M := by
            exact_mod_cast (by omega : ℓ ^ (j - 1) * (m - k) < M)
          push_cast [Nat.cast_sub hk'] at h5
          have h7 : (m : ℝ) - k ≤ M / (ℓ : ℝ) ^ (j - 1) := by
            rw [le_div_iff₀ hL]
            linarith [mul_comm ((ℓ : ℝ) ^ (j - 1)) ((m : ℝ) - k)]
          have hmax : max 0 (((ℓ : ℝ) - 1) * r - y - M / (ℓ : ℝ) ^ (j - 1)) ≤ k :=
            max_le (Nat.cast_nonneg _) (by rw [hmR]; linarith)
          push_cast
          linarith
        have e : (ℓ : A) ^ σ * X ^ r * ((a * ℓ) ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) * (m.choose k : A)) =
            (ℓ : A) ^ c * ((ℓ : A) ^ (σ + k - c) * (X ^ r * a ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) *
              (m.choose k : A))) := by
          rw [← mul_assoc ((ℓ : A) ^ c) ((ℓ : A) ^ (σ + k - c)), ← pow_add, Nat.add_sub_cancel' hcs]
          ring
        rw [e]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have hj1 : j = (j - 1) + 1 := by omega
    have hprod : (∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r =
        (∏ s ∈ Finset.range j, p s ^ y) * ((∏ s ∈ Finset.range (j - 1), p s ^ m) * p (j - 1) ^ m) := by
      rw [← Finset.prod_pow]
      have e1 : ∀ s, (p s ^ (ℓ - 1)) ^ r = p s ^ y * p s ^ m := fun s => by
        rw [← pow_mul, hm, pow_add]
      simp_rw [e1]
      rw [Finset.prod_mul_distrib]
      congr 1
      conv_lhs => rw [hj1]
      rw [Finset.prod_range_succ]
    have heq : (ℓ : A) ^ σ * (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r =
        ((ℓ : A) ^ σ * X ^ r * p (j - 1) ^ m) * (∏ s ∈ Finset.range j, p s ^ y) *
          (u ^ r * ∏ s ∈ Finset.range (j - 1), p s ^ m) := by
      rw [mul_pow, mul_pow, hprod]
      ring
    rw [heq]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp key
    rw [← hαβ]
    exact Ideal.mem_span_pair.mpr ⟨α * ∏ s ∈ Finset.range j, p s ^ y, β, by ring⟩

end Formalism.NOK
end

