module

public import Mathlib
public import ReciprocityTheory.DualLattices.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
section
namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

def LowBStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 3 ≤ p → v (p : C) = 1 → ∀ (d M : ℕ) (dp : Fin d → ℤ) (c : Fin d → ℕ → Fin d → C),
      (∀ a, -1 ≤ dp a) → (∀ a, c a 0 = Pi.single a 1) →
      (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) →
      (∀ a, 0 ≤ dp a → c a 1 = 0 ∧
        (∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) ∧
        (∀ b, c a 2 b ≠ 0 → dp a - 1 ≤ dp b)) →
      ∀ (ρ : Fin M → ℝ), (∀ m, 0 ≤ ρ m) → ∀ z : Fin d → MvPowerSeries (Fin M) C,
        (∀ b (α : Fin M →₀ ℕ), Finsupp.degree α ≠ 1 → coeff α (z b) = 0) →
        (∀ b, OrdGe v ρ (z b) (radius p (dp b))) →
        ∃ t : Fin d → MvPowerSeries (Fin M) C, (∀ b, constantCoeff (t b) = 0) ∧
          (∀ b, lgSum p c t b = z b) ∧ (∀ b, OrdGe v ρ (t b) (radius p (dp b))) ∧
          ∀ f : MvPowerSeries (Fin d) C, MvIsInt v f → OrdGe v ρ (subst t f) 0

def FactorialWeightedSumBound : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (M : ℕ) (ρ : Fin M → ℝ)
    (g : MvPowerSeries (Fin M) C), OrdGe v ρ g 0 → ∀ (P : MvPolynomial (Fin M) ℤ) (B : ℝ),
      (∀ α ∈ P.support, (((B + ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤
          v ((∏ m, (α m).factorial : ℕ) : C)) →
      ((B : ℝ) : WithTop ℝ) ≤ v (∑ α ∈ P.support,
          ((P.coeff α : ℤ) : C) * ((∏ m, (α m).factorial : ℕ) : C) * coeff α g)

def FactorialMultiindexBound : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 3 ≤ p → v (p : C) = 1 → ∀ (i cr K ex : ℕ), cr ≤ i →
      ∀ α : Fin i × Fin i →₀ ℕ, Finsupp.degree α = i * ex →
        (∀ e : Fin i, ∑ c : Fin i, α (e, c) ≤ ex) →
        (∑ x : Fin i × Fin i, (if x.1.val < cr then radius p (-1) else radius p K) * α x ≤
            i * ex * radius p K + ex * cr * (radius p (-1) - radius p K)) ∧
        (((i * ex / ((p : ℝ) - 1) - (i : ℝ) ^ 2 * Real.logb p (ex + 1) : ℝ)) : WithTop ℝ) ≤
            v ((∏ x, (α x).factorial : ℕ) : C)

def RadiusExponentInequality : Prop :=
  ∀ (p i cr K ex : ℕ), 3 ≤ p → 1 ≤ ex → cr ≤ i → ex ≤ p ^ (2 * K + 1) →
    (K = 0 ∨ p ^ (2 * K - 1) < ex) →
    ((i : ℝ) - cr) * ex * p / ((p : ℝ) ^ 2 - 1) - (i : ℝ) ^ 2 * (Real.logb p ex + 1) ≤
        i * ex / ((p : ℝ) - 1) - (i : ℝ) ^ 2 * Real.logb p (ex + 1) - i * ex * radius p K
          - ex * cr * (radius p (-1) - radius p K) ∧
      (K : ℝ) + 1 ≤ 3 / 2 + Real.logb p ex / 2

end

end ReciprocityTheory.ChartRestriction.G.Sh
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
section
namespace ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps

open ReciprocityTheory.PGsh PowerSeries

noncomputable section

section Coeff

variable {K : Type*} [Field K]

theorem coeff_pow_gap (f : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (a : K)
    (h0 : coeff 0 f = 0) (h1 : coeff 1 f = a) (hg : ∀ j, 2 ≤ j → j < M → coeff j f = 0)
    (n : ℕ) (hn : 2 ≤ n) : coeff M (f ^ n) = if n = M then a ^ M else 0 := by
  have hX : (X : PowerSeries K) ∣ f :=
    X_dvd_iff.mpr (by rw [← coeff_zero_eq_constantCoeff_apply]; exact h0)
  obtain ⟨g, rfl⟩ := hX
  have hg0 : coeff 0 g = a := by
    rw [← h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]
  have hd : (X : PowerSeries K) ^ (M - 1) ∣ g - C a := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, coeff_C]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp [hg0]
    · rw [if_neg hm0.ne', sub_zero, ← coeff_succ_X_mul]
      exact hg (m + 1) (by omega) (by omega)
  have hdn : (X : PowerSeries K) ^ (M - 1) ∣ g ^ n - C a ^ n :=
    dvd_trans hd (sub_dvd_pow_sub_pow _ _ n)
  rw [mul_pow, coeff_X_pow_mul']
  by_cases hle : n ≤ M
  · rw [if_pos hle]
    by_cases heq : n = M
    · subst heq
      rw [if_pos rfl, Nat.sub_self, coeff_zero_eq_constantCoeff_apply, map_pow,
        ← coeff_zero_eq_constantCoeff_apply, hg0]
    · rw [if_neg heq]
      have h1' := (X_pow_dvd_iff.mp hdn) (M - n) (by omega)
      rw [map_sub, ← map_pow, coeff_C, if_neg (by omega), sub_zero] at h1'
      exact h1'
  · rw [if_neg hle, if_neg (by omega)]

theorem coeff_subst_gap (lg P : PowerSeries K) (M : ℕ) (hM : 2 ≤ M) (b : K)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1) (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0)
    (hP0 : coeff 0 P = 0) (hP1 : coeff 1 P = b) (hPg : ∀ j, 2 ≤ j → j < M → coeff j P = 0) :
    coeff M (subst P lg) = coeff M P + coeff M lg * b ^ M := by
  have hs : HasSubst P :=
    HasSubst.of_constantCoeff_zero' (by rw [← coeff_zero_eq_constantCoeff_apply]; exact hP0)
  rw [coeff_subst' hs]
  have hsupp : (Function.support fun d : ℕ => coeff d lg • coeff M (P ^ d)) ⊆
      ↑(Finset.range (M + 1)) := by
    intro d hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    simp only
    rw [coeff_pow_gap P M hM b hP0 hP1 hPg d (by omega), if_neg (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_range_succ,
    Finset.sum_eq_single 1]
  · rw [coeff_pow_gap P M hM b hP0 hP1 hPg M hM, if_pos rfl]
    simp [hl1]
  · intro d hd hd1
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      subst this; rw [hl0, zero_smul]
    · rw [hlg d h (Finset.mem_range.mp hd), zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem coeff_expComp_gap [CharZero K] (Ω : K) (lg : PowerSeries K) (M : ℕ) (hM : 2 ≤ M)
    (hl0 : coeff 0 lg = 0) (hl1 : coeff 1 lg = 1)
    (hlg : ∀ j, 2 ≤ j → j < M → coeff j lg = 0) :
    coeff M (expComp Ω lg) = Ω * coeff M lg + Ω ^ M / (M.factorial : K) := by
  rw [expComp, coeff_mk, Finset.sum_range_succ, Finset.sum_eq_single 1]
  · rw [coeff_pow_gap lg M hM 1 hl0 hl1 hlg M hM, if_pos rfl]
    simp
  · intro d hd hd1
    rcases Nat.lt_or_ge d 2 with h | h
    · have : d = 0 := by omega
      have hM0 : M ≠ 0 := by omega
      subst this; simp [coeff_one, hM0]
    · rw [coeff_pow_gap lg M hM 1 hl0 hl1 hlg d h,
        if_neg (by have := Finset.mem_range.mp hd; omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

end Coeff

section Val

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

theorem exists_real {x : K} (hx : x ≠ 0) : ∃ r : ℝ, v x = r := by
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((v.top_iff).not.mpr hx)
  exact ⟨r, hr.symm⟩

theorem nsmul_one_coe (n : ℕ) : n • (1 : WithTop ℝ) = ((n : ℝ) : WithTop ℝ) := by
  rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]

theorem natCast_nonneg (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact v.map_le_add ih (le_of_eq v.map_one.symm)

theorem intCast_nonneg (n : ℤ) : 0 ≤ v (n : K) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using natCast_nonneg v m
  · simpa [v.map_neg] using natCast_nonneg v m

theorem natCast_eq_zero_of_coprime {p : ℕ} (hp1 : v (p : K) = 1) {c : ℕ}
    (hc : Nat.Coprime p c) : v (c : K) = 0 := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have hK : (a : K) * p + b * c = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hab
  have h0 := natCast_nonneg v c
  refine le_antisymm ?_ h0
  by_contra hlt
  rw [not_le] at hlt
  have h1 : 0 < v ((a : K) * p) := by
    rw [v.map_mul, hp1]
    calc (0 : WithTop ℝ) < 1 := by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
      _ = 0 + 1 := (zero_add 1).symm
      _ ≤ v (a : K) + 1 := add_le_add_left (intCast_nonneg v a) 1
  have h2 : 0 < v ((b : K) * c) := by
    rw [v.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_left (intCast_nonneg v b))
  have h3 := v.map_add ((a : K) * p) ((b : K) * c)
  rw [hK, v.map_one] at h3
  exact absurd h3 (not_le.mpr (lt_min h1 h2))

theorem natCast_eq_factorization {p : ℕ} (hp : p.Prime) (hp1 : v (p : K) = 1) {m : ℕ}
    (hm : m ≠ 0) : v (m : K) = ((m.factorization p : ℝ) : WithTop ℝ) := by
  have e := Nat.ordProj_mul_ordCompl_eq_self m p
  have hc := Nat.coprime_ordCompl hp hm
  conv_lhs => rw [← e]
  rw [Nat.cast_mul, Nat.cast_pow, v.map_mul, v.map_pow, hp1,
    natCast_eq_zero_of_coprime v hp1 hc, add_zero, nsmul_one_coe]

theorem eq_of_nonneg_add {x y : K} {A B : ℝ} (hA : A < 0) (hx : v x = A) (hy : v y = B)
    (h : 0 ≤ v (x + y)) : A = B := by
  by_contra hne
  have hd : v x ≠ v y := by rw [hx, hy]; exact fun e => hne (WithTop.coe_injective e)
  rw [v.map_add_of_distinct_val hd, hx, hy, ← WithTop.coe_min] at h
  have h' : (0 : ℝ) ≤ min A B := by exact_mod_cast h
  exact absurd h' (not_le.mpr (lt_of_le_of_lt (min_le_left A B) hA))

theorem add_eq_of_lt {x y : K} {A B : ℝ} (hx : v x = A) (hy : v y = B) (h : A < B) :
    v (x + y) = A := by
  have hd : v x ≠ v y := by rw [hx, hy]; exact fun e => h.ne (WithTop.coe_injective e)
  rw [v.map_add_of_distinct_val hd, hx, hy, ← WithTop.coe_min, min_eq_left h.le]

theorem div_eq_coe {x y : K} (hy : y ≠ 0) {A B : ℝ} (hx : v x = A) (hyv : v y = B) :
    v (x / y) = ((A - B : ℝ) : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := exists_real v (inv_ne_zero hy)
  have h1 : v (y * y⁻¹) = 0 := by rw [mul_inv_cancel₀ hy, v.map_one]
  rw [v.map_mul, hyv, hc, ← WithTop.coe_add] at h1
  have h2 : B + c = 0 := WithTop.coe_eq_zero.mp h1
  rw [div_eq_mul_inv, v.map_mul, hx, hc, ← WithTop.coe_add]
  congr 1
  linarith

end Val

section ZetaNonvanishing₂

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))

end ZetaNonvanishing₂

end

end ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps
end

