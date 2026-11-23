module

public import Formalism.RankGapBounds.Bundle0001

@[expose] public section

-- bundled from Formalism.RankGapBounds.RankGapProofs.CardLargePrimeFactorsLeOneHolds
section
open Real Finset

namespace Formalism.RankGapBounds.ChebyshevFactorialBounds

theorem chebyshevThetaLe_holds : ChebyshevTheta := by
  intro n
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at h
  exact h

end Formalism.RankGapBounds.ChebyshevFactorialBounds
end

-- bundled from Formalism.RankGapBounds.RankGapProofs.FourNotDvdOddSqAddOne
section
namespace Formalism.RankGapBounds.LocalQuadraticParts

lemma zmod_int_eq_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = 1) ↔ (n : ℤ) ∣ x - 1 := by
  rw [← sub_eq_zero, ← Int.cast_one, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma zmod_int_eq_neg_one_iff (n : ℕ) (x : ℤ) : ((x : ZMod n) = -1) ↔ (n : ℤ) ∣ x + 1 := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← Int.cast_one, ← Int.cast_add, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma zmod_nat_eq_one_iff (n l : ℕ) : ((l : ZMod n) = 1) ↔ (n : ℤ) ∣ (l : ℤ) - 1 := by
  have h := zmod_int_eq_one_iff n (l : ℤ)
  simpa using h

lemma zmod_nat_eq_neg_one_iff (n l : ℕ) : ((l : ZMod n) = -1) ↔ (n : ℤ) ∣ (l : ℤ) + 1 := by
  have h := zmod_int_eq_neg_one_iff n (l : ℤ)
  simpa using h

lemma four_not_dvd_odd_sq_add_one (y : ℤ) (hy : Odd y) : ¬ (4 : ℤ) ∣ y ^ 2 + 1 := by
  obtain ⟨k, rfl⟩ := hy
  have h : (2 * k + 1) ^ 2 + 1 = 4 * (k ^ 2 + k) + 2 := by ring
  rw [h]
  generalize k ^ 2 + k = t
  omega

lemma sq_sub_one_dvd_iff (x : ℤ) (hx : Odd x) (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℤ) ^ (m + 1) ∣ x ^ 2 - 1 ↔ ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, rfl⟩ := hx
  have e1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
  have e2 : 2 * k + 1 - 1 = 2 * k := by ring
  have e3 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  have p1 : (2 : ℤ) ^ (n + 1 + 1) = 4 * 2 ^ n := by ring
  have p2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [e1, e2, e3, p1, p2, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  constructor
  · intro h
    rcases Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      have hc : IsCoprime ((2 : ℤ) ^ n) (k + 1) := by
        apply IsCoprime.pow_left
        refine ⟨-b, 1, ?_⟩
        rw [hb]
        ring
      exact hc.dvd_of_dvd_mul_right h
    · right
      have hc : IsCoprime ((2 : ℤ) ^ n) k := by
        apply IsCoprime.pow_left
        refine ⟨-b, 1, ?_⟩
        rw [hb]
        ring
      exact hc.dvd_of_dvd_mul_left h
  · rintro (h | h)
    · exact dvd_mul_of_dvd_left h _
    · exact dvd_mul_of_dvd_right h _

lemma pow_two_pow_pm_iff (j : ℕ) : ∀ (x : ℤ), Odd x → ∀ m : ℕ, 1 ≤ m →
    (((2 : ℤ) ^ (m + j) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (m + j) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1)) := by
  induction j with
  | zero => intro x _ m _; simp
  | succ j ih =>
    intro x hx m hm
    have hy : Odd (x ^ (2 ^ j)) := hx.pow
    have hpow : x ^ (2 ^ (j + 1)) = (x ^ (2 ^ j)) ^ 2 := by rw [pow_succ, pow_mul]
    have hnot : ¬ (2 : ℤ) ^ (m + (j + 1)) ∣ (x ^ (2 ^ j)) ^ 2 + 1 := by
      intro h
      apply four_not_dvd_odd_sq_add_one _ hy
      refine dvd_trans ?_ h
      have : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_dvd_pow 2 (by omega)
    rw [hpow, ← ih x hx m hm, show m + (j + 1) = m + j + 1 by omega,
      ← sq_sub_one_dvd_iff _ hy (m + j) (by omega)]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h (by rw [show m + j + 1 = m + (j + 1) by omega]; exact hnot)
    · intro h
      exact Or.inl h

lemma pm_iff (e j : ℕ) (hj : j ≤ e) (x : ℤ) (hx : Odd x) :
    (((2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ (e + 2) ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ (e + 2 - j) ∣ x - 1 ∨ (2 : ℤ) ^ (e + 2 - j) ∣ x + 1)) := by
  have h := pow_two_pow_pm_iff j x hx (e + 2 - j) (by omega)
  rw [show e + 2 - j + j = e + 2 by omega] at h
  exact h

lemma units_zpow_neg_one_iff (n : ℕ) (u : (ZMod n)ˣ) :
    (∃ k : ℤ, (-1 : (ZMod n)ˣ) ^ k = u) ↔ (u = 1 ∨ u = -1) := by
  constructor
  · rintro ⟨k, rfl⟩
    rcases Int.even_or_odd k with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · rintro (rfl | rfl)
    · exact ⟨0, zpow_zero _⟩
    · exact ⟨1, zpow_one _⟩

lemma hOf_pow_eq_one_iff (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) :
    (hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = 1 ∨
        (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = -1) := by
  unfold hOf
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff,
    units_zpow_neg_one_iff]
  have hv : ((ZMod.unitOfCoprime l hl ^ (2 ^ j) : (ZMod (4 * 2 ^ e))ˣ) : ZMod (4 * 2 ^ e)) =
      (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) := by
    simp [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  constructor
  · rintro (h | h)
    · left
      rw [← hv, h, Units.val_one]
    · right
      rw [← hv, h, Units.val_neg, Units.val_one]
  · rintro (h | h)
    · left
      apply Units.ext
      rw [hv, h, Units.val_one]
    · right
      apply Units.ext
      rw [hv, h, Units.val_neg, Units.val_one]

lemma odd_of_coprime (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Odd (l : ℤ) := by
  have h2 : ¬ 2 ∣ l := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hl)
      (dvd_mul_of_dvd_left (by norm_num) _)
    omega
  exact Int.odd_iff.mpr (by omega)

theorem powTwoPowEqOneIff_holds : OrdersIff := by
  intro e j l hl hj
  rw [hOf_pow_eq_one_iff, zmod_int_eq_one_iff, zmod_int_eq_neg_one_iff, zmod_nat_eq_one_iff,
    zmod_nat_eq_neg_one_iff]
  push_cast
  rw [show (4 : ℤ) * 2 ^ e = 2 ^ (e + 2) by ring]
  exact pm_iff e j hj l (odd_of_coprime e l hl)

end Formalism.RankGapBounds.LocalQuadraticParts
end

-- bundled from Formalism.RankGapBounds.RankGapProofs.WeightedMeanData
section
open Real

namespace Formalism.RankGapBounds.WeightedMeanData

noncomputable section

section Means

variable {ι : Type} [Fintype ι]

lemma sum_pos_of_pos [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) : 0 < ∑ i, d i :=
  Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty

lemma wmean_mono {d X Y : ι → ℝ} (hd : ∀ i, 0 < d i) (h : ∀ i, X i ≤ Y i) :
    wmean d X ≤ wmean d Y := by
  unfold wmean
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right
    (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hd i).le)
    (inv_nonneg.mpr (Finset.sum_nonneg fun i _ => (hd i).le))

lemma wmean_add (d X Y : ι → ℝ) : wmean d (fun i => X i + Y i) = wmean d X + wmean d Y := by
  simp only [wmean, mul_add, Finset.sum_add_distrib, add_div]

lemma wmean_const [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ) :
    wmean d (fun _ => c) = c := by
  have hS : ∑ i, d i ≠ 0 := (sum_pos_of_pos hd).ne'
  simp only [wmean]
  rw [div_eq_iff hS, ← Finset.sum_mul]
  ring

lemma wmean_le_const [Nonempty ι] {d X : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ)
    (h : ∀ i, X i ≤ c) : wmean d X ≤ c := by
  have h1 := wmean_mono (X := X) (Y := fun _ => c) hd h
  have h3 := wmean_const hd c
  linarith

lemma sub_wmean_le [Nonempty ι] {d X Y : ι → ℝ} (hd : ∀ i, 0 < d i) (c : ℝ)
    (h : ∀ i, c - Y i ≤ X i) : c - wmean d Y ≤ wmean d X := by
  have h1 := wmean_mono (X := fun _ => c) (Y := fun i => X i + Y i) hd
    (fun i => by show c ≤ X i + Y i; linarith [h i])
  have h2 := wmean_add d X Y
  have h3 := wmean_const hd c
  linarith

end Means

lemma phi_bound {u H X b U : ℝ} (hu : 0 ≤ u) (hH : 0 < H) (hHX : H ≤ X * b) (hb : 0 < b)
    (hX : 0 < X) (huU : u ≤ U) :
    u * Real.log (1 + H / u) ≤ Real.log (1 + X) * (U + b) := by
  have hL : 0 < Real.log (1 + X) := Real.log_pos (by linarith)
  have hX1 : 0 < 1 + X := by linarith
  rcases hu.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact mul_nonneg hL.le (by linarith)
  · have hw0 : 0 ≤ (1 + X)⁻¹ := inv_nonneg.mpr hX1.le
    have hw1 : (1 + X) * (1 + X)⁻¹ = 1 := mul_inv_cancel₀ hX1.ne'
    have hb0 : 1 - (1 + X)⁻¹ ≤ Real.log (1 + X) := by
      have := Real.log_le_sub_one_of_pos (inv_pos.mpr hX1)
      rw [Real.log_inv] at this
      linarith
    have h1 : 0 < 1 + H / u := by
      have := div_nonneg hH.le hpos.le
      linarith
    have ha : Real.log (1 + H / u) ≤ Real.log (1 + X) + ((1 + H / u) * (1 + X)⁻¹ - 1) := by
      have := Real.log_le_sub_one_of_pos (mul_pos h1 (inv_pos.mpr hX1))
      rw [Real.log_mul h1.ne' (inv_pos.mpr hX1).ne', Real.log_inv] at this
      linarith
    have hyu : u * (H / u) = H := by
      rw [mul_comm, div_mul_eq_mul_div, mul_div_assoc, div_self hpos.ne', mul_one]
    have i1 := mul_le_mul_of_nonneg_left ha hu
    have e1 : u * (Real.log (1 + X) + ((1 + H / u) * (1 + X)⁻¹ - 1))
        = u * Real.log (1 + X) + u * (1 + X)⁻¹ + H * (1 + X)⁻¹ - u := by
      linear_combination (1 + X)⁻¹ * hyu
    have i2 := mul_le_mul_of_nonneg_right huU hL.le
    have hXw : X * (1 + X)⁻¹ = 1 - (1 + X)⁻¹ := by linear_combination hw1
    have hwle : (1 + X)⁻¹ ≤ 1 := by linarith [mul_nonneg hX.le hw0]
    have i3 : 0 ≤ u * (1 - (1 + X)⁻¹) := mul_nonneg hu (by linarith)
    have i4 : H * (1 + X)⁻¹ ≤ b * (1 - (1 + X)⁻¹) := by
      rw [← hXw]
      have := mul_le_mul_of_nonneg_right hHX hw0
      linarith
    have i5 := mul_le_mul_of_nonneg_left hb0 hb.le
    linarith

namespace Data

variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable (D : Data U0 W Top m f) (C : Consts)

def abelian₂ (u0 : U0) : ℝ :=
  (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)) + (m : ℝ) * D.lg
    - C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k) - 2 * D.logGam / ((f : ℝ) * D.k)

def SDiv : ℝ := ∑ t, (m : ℝ) * (ph (D.aT t) - D.aT t * D.logOm)

def EDiv : ℝ :=
  C.cDiv * D.nT * D.a * D.La + C.cDiv * (m : ℝ) * (D.B0 + D.Nc) * D.x ^ (C.eDiv * D.ε)

def K3 : ℝ :=
  C.cSlope * D.nT * D.a * D.La * (2 + (m : ℝ) / D.k) + D.Vvar C + C.cSl1 * (m : ℝ) * D.B0

lemma nT_nonneg : 0 ≤ D.nT := by
  exact Nat.cast_nonneg _

lemma sumA_nonneg (hS : D.HidaSetting C) : 0 ≤ D.sumA := by
  obtain ⟨-, -, -, -, -, -, -, haT, -⟩ := hS
  exact Finset.sum_nonneg fun t _ => haT t

lemma sum_aT_mul (g : ℝ) : ∑ t, D.aT t * g = D.sumA * g := by
  simp only [Data.sumA, Finset.sum_mul]

lemma uF_nonneg (hS : D.HidaSetting C) (u0 : U0) : 0 ≤ D.uF u0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hd, -, hmu, -⟩ := hS
  unfold Data.uF Data.s
  have hle : ∀ u : W u0, D.muN u0 u - D.h u0 u ≤
      Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) := by
    intro u
    have h1 : D.muN u0 u - D.h u0 u ≤ D.muMaxN u0 u - D.h u0 u := by linarith [hmu u0 u]
    exact h1.trans (Finset.le_sup' (fun u : W u0 => D.muMaxN u0 u - D.h u0 u) (Finset.mem_univ u))
  have := wmean_le_const (d := D.d u0) (X := fun u => D.muN u0 u - D.h u0 u) (hd u0) _ hle
  linarith

lemma key_identity (hv : 0 < D.v) (hf : 0 < f) (u0 : U0) (hw : ∀ j ρ, 0 < D.w u0 j ρ) :
    D.SDiv - D.sumA * D.abelian₂ C u0 + (m : ℝ) * D.sumA * D.lg =
      D.Main u0 + D.sumA * (C.cCount * (D.L + (m : ℝ) ^ 2 * D.L / D.k)
        + 2 * D.logGam / ((f : ℝ) * D.k)) := by
  have hfR : (f : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  have hcard : ∀ c : ℝ, ∑ _j : Fin m, c = (m : ℝ) * c := fun c => by simp
  have hcardf : ∀ c : ℝ, ∑ _ρ : Fin f, c = (f : ℝ) * c := fun c => by simp
  have hpi : Real.log (π / D.v) = Real.log π - Real.log D.v :=
    Real.log_div Real.pi_ne_zero hv.ne'
  have hff : 1 / (f : ℝ) * (f : ℝ) = 1 := by rw [one_div, inv_mul_cancel₀ hfR]
  have h1 : ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)
      = ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)
        + (m : ℝ) * (Real.log D.v - Real.log π) := by
    rw [← hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : ∑ ρ : Fin f, Real.log (D.w u0 j ρ * D.v / π)
        = ∑ ρ : Fin f, Real.log (D.w u0 j ρ) + (f : ℝ) * (Real.log D.v - Real.log π) := by
      rw [← hcardf, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [Real.log_div (mul_pos (hw j ρ) hv).ne' Real.pi_ne_zero,
        Real.log_mul (hw j ρ).ne' hv.ne']
      ring
    rw [e1]
    linear_combination (Real.log D.v - Real.log π) * hff
  have h2 : D.SDiv = (m : ℝ) * ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL)
      - (m : ℝ) * (Real.log π - Real.log D.v) * D.sumA := by
    unfold Data.SDiv Data.sumA
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [ph, Data.logOm]
    rw [hpi]
    ring
  have hMj : ∀ j : Fin m, ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL
        - (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ))
      = ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL)
        - D.sumA * ((1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ)) := by
    intro j
    unfold Data.sumA
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have h3 : D.Main u0 = (m : ℝ) * ∑ t, D.aT t * (Real.log (D.aT t) - 1 - D.gam + D.LpL)
      - D.sumA * ∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (D.w u0 j ρ) := by
    unfold Data.Main
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hMj j), Finset.sum_sub_distrib,
      hcard, ← Finset.mul_sum]
  unfold Data.abelian₂
  linear_combination h2 - D.sumA * h1 - h3

end Data

end

end Formalism.RankGapBounds.WeightedMeanData
end

