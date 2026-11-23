module

public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
public import Formalism.WindowSums.PowerSeriesRelationList
public import Mathlib
public import Formalism.TruncatedSeriesCounting.Bundle0001

@[expose] public section

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.LemmaGVal
section
namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

open Finset

private lemma sum_shift_val (ℓ : ℕ) (j₀ : ℤ) (T : Finset ℤ) :
    ∑ j ∈ T, padicValInt ℓ (j₀ - j) = ∑ i ∈ T.image (fun j => j₀ - j), padicValInt ℓ i := by
  rw [Finset.sum_image]
  intro a _ b _ h
  simp only at h
  omega

theorem g_coeff_valuation_statement : LemmaGVal := by
  intro ℓ _ h η S b a S₂ hb hbS hS₂ j₀ hj₀
  rw [Finset.mem_Icc] at hj₀
  obtain ⟨hj1, hj2⟩ := hj₀
  have hℓ : (2 : ℝ) ≤ ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).two_le
  have hmem : ∀ j ∈ S₂, ((b : ℤ) + 1 ≤ j ∧ j ≤ (b : ℤ) + S + a) ∨
      (1 - (η : ℤ) ≤ j ∧ j ≤ (η : ℤ) + a) := by
    intro j hj
    have := hS₂ hj
    simpa only [Finset.mem_union, Finset.mem_Icc] using this
  set T₁ : Finset ℤ := (Finset.Icc ((b : ℤ) - a + 1) b).erase j₀ ∪
    S₂.filter (fun j => (b : ℤ) < j) with hT₁
  set T₂ : Finset ℤ := S₂.filter (fun j => ¬ (b : ℤ) < j) with hT₂
  have hsplit : (∑ j ∈ (Finset.Icc ((b : ℤ) - a + 1) (b : ℤ)).erase j₀, padicValInt ℓ (j₀ - j)) +
      ∑ j ∈ S₂, padicValInt ℓ (j₀ - j) =
      ∑ j ∈ T₁, padicValInt ℓ (j₀ - j) + ∑ j ∈ T₂, padicValInt ℓ (j₀ - j) := by
    rw [← Finset.sum_filter_add_sum_filter_not S₂ (fun j => (b : ℤ) < j), ← add_assoc, hT₁,
      hT₂, Finset.sum_union]
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase hx)).2
    have h2 := (Finset.mem_filter.mp hx').2
    omega
  rw [hsplit, sum_shift_val, sum_shift_val]
  have c1 : T₁.image (fun j => j₀ - j) ⊆
      Finset.Ico (j₀ - b - S - a) (j₀ - b - S - a + ((2 * a + S : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Ico]
    push_cast
    rw [hT₁, Finset.mem_union] at hj
    rcases hj with hj | hj
    · have := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)
      omega
    · have h1 := (Finset.mem_filter.mp hj).2
      have h2 := hmem j (Finset.mem_filter.mp hj).1
      omega
  have c2 : (0 : ℤ) ∉ T₁.image (fun j => j₀ - j) := by
    intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, hj0⟩ := hi
    rw [hT₁, Finset.mem_union] at hj
    rcases hj with hj | hj
    · have := Finset.ne_of_mem_erase hj
      omega
    · have h1 := (Finset.mem_filter.mp hj).2
      omega
  have c3 : ∀ i ∈ T₁.image (fun j => j₀ - j), |i| ≤ ((2 * (h + η) : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    push_cast
    rw [hT₁, Finset.mem_union] at hj
    rw [abs_le]
    rcases hj with hj | hj
    · have := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hj)
      constructor <;> omega
    · have h1 := (Finset.mem_filter.mp hj).2
      have h2 := hmem j (Finset.mem_filter.mp hj).1
      constructor <;> omega
  have d1 : T₂.image (fun j => j₀ - j) ⊆
      Finset.Ico (j₀ - η - a) (j₀ - η - a + ((2 * η + a : ℕ) : ℤ)) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_Ico]
    push_cast
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    omega
  have d2 : (0 : ℤ) ∉ T₂.image (fun j => j₀ - j) := by
    intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, hj0⟩ := hi
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    omega
  have d3 : ∀ i ∈ T₂.image (fun j => j₀ - j), |i| ≤ ((2 * (h + η) : ℕ) : ℤ) := by
    intro i hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    push_cast
    rw [abs_le]
    have h1 := (Finset.mem_filter.mp hj).2
    have h2 := hmem j (Finset.mem_filter.mp hj).1
    constructor <;> omega
  have w1 := Formalism.WindowSums.arc_WindowSum ℓ (j₀ - b - S - a) (2 * a + S) (2 * (h + η)) _ c1 c2 c3
  have w2 := Formalism.WindowSums.arc_WindowSum ℓ (j₀ - η - a) (2 * η + a) (2 * (h + η)) _ d1 d2 d3
  have hDpos : (1 : ℝ) ≤ ((2 * (h + η) : ℕ) : ℝ) := by
    have : 1 ≤ 2 * (h + η) := by omega
    exact_mod_cast this
  have hlog : 0 ≤ Real.logb ℓ ((2 * (h + η) : ℕ) : ℝ) := Real.logb_nonneg (by linarith) hDpos
  have hlam : lam ℓ (h + η) = Real.logb ℓ ((2 * (h + η) : ℕ) : ℝ) + 1 := by
    simp only [lam]
    push_cast
    ring_nf
  have hsum : ((2 * a + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) + ((2 * η + a : ℕ) : ℝ) / ((ℓ : ℝ) - 1) =
      (3 * (a : ℝ) + (S : ℝ) + 2 * (η : ℝ)) / ((ℓ : ℝ) - 1) := by
    rw [← add_div]
    push_cast
    ring_nf
  rw [hlam]
  push_cast at w1 w2 hlog hsum ⊢
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.QNumericalIdentity
section
namespace Formalism.TruncatedSeriesCounting.X

theorem q_numerical_identity : QaNum := by
  intro ℓ hℓ H' H eW hH heW
  unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast (by omega : 1 < ℓ)
  have hd : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hdiv : ((H' / (ℓ - 1) : ℕ) : ℝ) ≤ (H' : ℝ) / ((ℓ : ℝ) - 1) := by
    have h := Nat.cast_div_le (m := H') (n := ℓ - 1) (α := ℝ)
    rwa [Nat.cast_sub (by omega : 1 ≤ ℓ), Nat.cast_one] at h
  have hlog : Real.logb ℓ ((H' : ℝ) + 1) ≤ Real.logb ℓ (2 * (H : ℝ)) + 1 := by
    rcases Nat.eq_zero_or_pos H with h0 | hpos
    · subst h0
      have h0' : H' = 0 := by omega
      subst h0'
      simp
    · have h1 : (H' : ℝ) + 1 ≤ 2 * H := by
        have h2 : (H' : ℝ) ≤ H := by exact_mod_cast hH
        have h3 : (1 : ℝ) ≤ H := by exact_mod_cast hpos
        linarith
      have h4 := Real.logb_le_logb_of_le hℓ1 (by positivity) h1
      linarith
  have hfrac : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤
      (H : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have heq : (H' : ℝ) / ((ℓ : ℝ) - 1) + (H' : ℝ) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
        (H' : ℝ) * (2 * ℓ - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
      have := hd.ne'
      field_simp
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ (pow_pos hd 2).le
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hH) (by linarith)
  push_cast
  linarith

end Formalism.TruncatedSeriesCounting.X
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.RrBound
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

open Finset

private theorem geom_sum_range_mul_one_sub (x : ℝ) :
    ∀ n : ℕ, Finset.sum (range n) (fun i => x ^ i) * (1 - x) = 1 - x ^ n := fun
  | 0 => by simp
  | n + 1 => by rw [sum_range_succ, add_mul, geom_sum_range_mul_one_sub x n, pow_succ]; ring

theorem tsum_le_two_level (x A B D : ℝ) (j : ℕ) (f : ℕ → ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hA0 : 0 ≤ A) (hf0 : ∀ a, 0 ≤ f a) (hfB : ∀ a, f a ≤ (B + D) * x ^ a)
    (hfA : ∀ a, a < j → f a ≤ (A + D) * x ^ a) :
    ∑' a, f a ≤ (A + B * x ^ j + D) * (1 - x)⁻¹ := by
  have hx1' : 0 < 1 - x := by linarith
  have hgeo : Summable (fun a : ℕ => (B + D) * x ^ a) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left (B + D)
  have hsum : Summable f := Summable.of_nonneg_of_le hf0 hfB hgeo
  have hsplit : Finset.sum (range j) f + ∑' a, f (a + j) = ∑' a, f a := by
    exact hsum.sum_add_tsum_nat_add j
  have hshift : Summable (fun a => f (a + j)) := by
    exact (summable_nat_add_iff j).mpr hsum
  have hg2 : HasSum (fun a : ℕ => (B + D) * x ^ j * x ^ a) ((B + D) * x ^ j * (1 - x)⁻¹) :=
    (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
  have h2 : ∑' a, f (a + j) ≤ (B + D) * x ^ j * (1 - x)⁻¹ :=
    hasSum_le (fun a => by
      calc f (a + j) ≤ (B + D) * x ^ (a + j) := hfB (a + j)
        _ = (B + D) * x ^ j * x ^ a := by rw [pow_add]; ring) hshift.hasSum hg2
  have h1 : Finset.sum (range j) f ≤ (A + D) * Finset.sum (range j) (fun a => x ^ a) := by
    rw [mul_sum]
    exact sum_le_sum fun a ha => hfA a (mem_range.mp ha)
  have hS' : Finset.sum (range j) (fun a => x ^ a) = (1 - x ^ j) * (1 - x)⁻¹ := by
    rw [← geom_sum_range_mul_one_sub x j, mul_assoc, mul_inv_cancel₀ hx1'.ne', mul_one]
  have hpos : 0 ≤ A * x ^ j * (1 - x)⁻¹ :=
    mul_nonneg (mul_nonneg hA0 (pow_nonneg hx0 _)) (inv_nonneg.mpr hx1'.le)
  rw [← hsplit]
  calc Finset.sum (range j) f + ∑' a, f (a + j)
      ≤ (A + D) * Finset.sum (range j) (fun a => x ^ a) + (B + D) * x ^ j * (1 - x)⁻¹ :=
        add_le_add h1 h2
    _ = (A + B * x ^ j + D) * (1 - x)⁻¹ - A * x ^ j * (1 - x)⁻¹ := by rw [hS']; ring
    _ ≤ (A + B * x ^ j + D) * (1 - x)⁻¹ := by linarith

theorem rr_arith (l d G h y C L s r q : ℝ) (hld : l = d + 1) (hd2 : 2 ≤ d) (hG0 : 0 ≤ G)
    (hh0 : 0 ≤ h) (hy0 : 0 ≤ y) (hC0 : 0 ≤ C) (hCL : C ≤ 3 + L) (hL0 : 0 ≤ L)
    (hq : q = d / (d - 1)) (hsA : s ≤ (2 * G + 2 * h * y + C + 3) * q)
    (hr : r ≤ s * l / d ^ 2 + C) : r ≤ 20 * (G / l + h * y / d + L + 1) := by
  subst hld
  subst hq
  have hd1 : 0 < d - 1 := by linarith
  have hd0 : 0 < d := by linarith
  have hl0 : 0 < d + 1 := by linarith
  have hdd : 0 < (d - 1) * d := mul_pos hd1 hd0
  have hst : s * (d + 1) / d ^ 2 ≤ (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) := by
    have h1 : s * (d + 1) / d ^ 2 ≤ (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2 := by
      have e : (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2 - s * (d + 1) / d ^ 2
          = ((2 * G + 2 * h * y + C + 3) * (d / (d - 1)) - s) * ((d + 1) / d ^ 2) := by ring
      have : 0 ≤ ((2 * G + 2 * h * y + C + 3) * (d / (d - 1)) - s) * ((d + 1) / d ^ 2) :=
        mul_nonneg (by linarith) (div_nonneg hl0.le (sq_nonneg d))
      linarith
    have h2 : (2 * G + 2 * h * y + C + 3) * (d / (d - 1)) * (d + 1) / d ^ 2
        = (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) := by
      have hd1' : d - 1 ≠ 0 := hd1.ne'
      have hd0' : d ≠ 0 := hd0.ne'
      field_simp
    linarith
  have ht0 : 0 ≤ (d + 1) / ((d - 1) * d) := div_nonneg hl0.le hdd.le
  have htc : (d + 1) / ((d - 1) * d) ≤ 3 / 2 := by
    have key : d + 1 ≤ 3 / 2 * ((d - 1) * d) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2) (by linarith : (0:ℝ) ≤ 3 * d + 1)]
    exact (div_le_iff₀ hdd).mpr key
  have htG : (d + 1) / ((d - 1) * d) ≤ 10 / (d + 1) := by
    have key : (d + 1) * (d + 1) ≤ 10 * ((d - 1) * d) := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ d - 2) (by linarith : (0:ℝ) ≤ 9 * d + 6)]
    exact (div_le_div_iff₀ hdd hl0).mpr key
  have hth : (d + 1) / ((d - 1) * d) ≤ 3 / d := by
    have key : (d + 1) * d ≤ 3 * ((d - 1) * d) := by
      nlinarith [mul_nonneg hd0.le (by linarith : (0:ℝ) ≤ d - 2)]
    exact (div_le_div_iff₀ hdd hd0).mpr key
  have e1 : 2 * G * ((d + 1) / ((d - 1) * d)) ≤ 20 * (G / (d + 1)) := by
    calc 2 * G * ((d + 1) / ((d - 1) * d)) ≤ 2 * G * (10 / (d + 1)) :=
          mul_le_mul_of_nonneg_left htG (by linarith)
      _ = 20 * (G / (d + 1)) := by ring
  have hhy : 0 ≤ h * y := mul_nonneg hh0 hy0
  have e2 : 2 * h * y * ((d + 1) / ((d - 1) * d)) ≤ 20 * (h * y / d) := by
    have hq0 : 0 ≤ h * y / d := div_nonneg hhy hd0.le
    calc 2 * h * y * ((d + 1) / ((d - 1) * d)) = 2 * (h * y) * ((d + 1) / ((d - 1) * d)) := by ring
      _ ≤ 2 * (h * y) * (3 / d) := mul_le_mul_of_nonneg_left hth (by linarith)
      _ = 6 * (h * y / d) := by ring
      _ ≤ 20 * (h * y / d) := by linarith
  have e3 : (C + 3) * ((d + 1) / ((d - 1) * d)) ≤ (C + 3) * (3 / 2) :=
    mul_le_mul_of_nonneg_left htc (by linarith)
  have expand : (2 * G + 2 * h * y + C + 3) * ((d + 1) / ((d - 1) * d)) + C
      = 2 * G * ((d + 1) / ((d - 1) * d)) + 2 * h * y * ((d + 1) / ((d - 1) * d))
        + (C + 3) * ((d + 1) / ((d - 1) * d)) + C := by ring
  linarith

theorem remainder_bound_of_tsum : RrBound := by
  intro ℓ hℓ n _ H G h j cut s r hh hH hG hs hr
  have hL3 : (3:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast hℓ
  have hb : (1:ℝ) < (ℓ:ℝ) := by linarith
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hlog0 : 0 ≤ Real.logb ℓ (2 * h + 1) := Real.logb_nonneg hb (by linarith)
  have hceil := Nat.ceil_lt_add_one (R := ℝ) (a := 1 + Real.logb ℓ (2 * h + 1)) (by linarith)
  have hlog3 : Real.logb ℓ 3 ≤ 1 := by
    rw [← Real.logb_self_eq_one hb]
    exact (Real.logb_le_logb hb (by norm_num) (by linarith)).mpr hL3
  have hlogmul : Real.logb ℓ (2 * h + 1) ≤ Real.logb ℓ 3 + Real.logb ℓ h := by
    rw [← Real.logb_mul (by norm_num) (by linarith)]
    exact (Real.logb_le_logb hb (by linarith) (by nlinarith)).mpr (by linarith)
  have hL0 : 0 ≤ Real.logb ℓ h := Real.logb_nonneg hb hh1
  have hC0 : (0:ℝ) ≤ (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) := Nat.cast_nonneg _
  have hCL : (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) ≤ 3 + Real.logb ℓ h := by linarith
  have hd2 : (2:ℝ) ≤ (ℓ:ℝ) - 1 := by linarith
  have hdpos : (0:ℝ) < (ℓ:ℝ) - 1 := by linarith
  have hx0 : (0:ℝ) ≤ 1 / ((ℓ:ℝ) - 1) := by positivity
  have hx1 : 1 / ((ℓ:ℝ) - 1) < 1 := by rw [div_lt_one hdpos]; linarith
  have hser := tsum_le_two_level (1 / ((ℓ:ℝ) - 1)) (2 * G) (2 * h)
    ((⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) j
    (fun a : ℕ => ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ) +
        (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) + 3) / ((ℓ : ℝ) - 1) ^ a)
    hx0 hx1 (by positivity) (fun a => by positivity)
    (fun a => by
      have h' : ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ)) ≤ 2 * h := by
        exact_mod_cast hH (cut + ((a + 1 : ℕ) : ZMod n))
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hdpos.le a))
    (fun a ha => by
      have h' : ((H (cut + ((a + 1 : ℕ) : ZMod n)) : ℝ)) ≤ 2 * G := by
        exact_mod_cast hG (a + 1) (by omega) (by omega)
      rw [one_div, inv_pow, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hdpos.le a))
  have hsA := hs.trans hser
  have hq : (1 - 1 / ((ℓ:ℝ) - 1))⁻¹ = ((ℓ:ℝ) - 1) / ((ℓ:ℝ) - 1 - 1) := by
    have hd0 : (ℓ:ℝ) - 1 ≠ 0 := by linarith
    have hd1 : (ℓ:ℝ) - 1 - 1 ≠ 0 := by linarith
    field_simp
  have hyd : (h:ℝ) / ((ℓ:ℝ) - 1) ^ (j + 1) =
      (h:ℝ) * (1 / ((ℓ:ℝ) - 1)) ^ j / ((ℓ:ℝ) - 1) := by
    have hd0 : (ℓ:ℝ) - 1 ≠ 0 := by linarith
    rw [pow_succ, one_div_pow]
    field_simp
  rw [hyd]
  have key := rr_arith (ℓ:ℝ) ((ℓ:ℝ) - 1) (G:ℝ) (h:ℝ) ((1 / ((ℓ:ℝ) - 1)) ^ j)
    (⌈1 + Real.logb ℓ (2 * h + 1)⌉₊ : ℝ) (Real.logb ℓ h) s r
    (1 - 1 / ((ℓ:ℝ) - 1))⁻¹ (by ring) hd2 (Nat.cast_nonneg _) (by linarith)
    (pow_nonneg hx0 j) hC0 hCL hL0 hq (by linarith) hr
  exact key

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.SaturationCriterion
section
namespace Formalism.TruncatedSeriesCounting.X

private theorem iter_nzd {A : Type} [CommRing A] (ℓ g : A)
    (h : ∀ a : A, ℓ * a ∈ Ideal.span {g} → a ∈ Ideal.span {g}) :
    ∀ (n : ℕ) (z : A), ℓ ^ n * z ∈ Ideal.span {g} → z ∈ Ideal.span {g} := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ n ih =>
    intro z hz
    apply ih
    apply h
    have e : ℓ * (ℓ ^ n * z) = ℓ ^ (n + 1) * z := by ring
    rw [e]; exact hz

theorem saturation_criterion : SatA := by
  intro A _ _ ℓ f f' hf' hℓf hℓf' x k ⟨b, hb⟩ ⟨a, ha⟩
  have inj : Function.Injective (algebraMap A (FractionRing A)) := IsFractionRing.injective A (FractionRing A)
  have h1 : ℓ ^ k * b = f' * (f * a) := by
    apply inj
    rw [map_mul, map_pow, hb, map_mul (algebraMap A (FractionRing A)) f', ha]
    ring
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f' hℓf' k b (by
    rw [h1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f')))
  have hf'0 : algebraMap A (FractionRing A) f' ≠ 0 := (map_ne_zero_iff _ inj).mpr hf'
  have hx : x = algebraMap A (FractionRing A) c := by
    apply mul_left_cancel₀ hf'0
    rw [← hb, hc, map_mul]
  have h2 : ℓ ^ k * c = f * a := by
    apply inj
    rw [map_mul, map_pow, ← hx, ha]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (iter_nzd ℓ f hℓf k c (by
    rw [h2]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))
  exact ⟨d, by rw [hx, hd]⟩

end Formalism.TruncatedSeriesCounting.X
end

-- bundled from Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.ThmEExp
section
noncomputable section

namespace Formalism.TruncatedSeriesCounting.WachCoordinates

private lemma sigma_exponent_le_real (ℓ : ℕ) (hℓ : 3 ≤ ℓ) (g h j : ℕ) (hj : 1 ≤ j) :
    (sigE ℓ g h j : ℝ) ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) + 9 / 4 * g + 11 / 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hjm : m + 1 - 1 = m := by omega
  unfold sigE
  rw [hjm]
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hq0 : (0 : ℝ) < (ℓ : ℝ) - 1 := by linarith
  have hq2 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hg0 : (0 : ℝ) ≤ g := by positivity
  have hA0 : (0 : ℝ) ≤ (h : ℝ) + 2 * g := by positivity
  have hP1 : (1 : ℝ) ≤ (ℓ : ℝ) ^ m := one_le_pow₀ (by linarith)
  have hPq : ((ℓ : ℝ) - 1) ^ m ≤ (ℓ : ℝ) ^ m := pow_le_pow_left₀ hq0.le (by linarith) m
  have hP0 : (0 : ℝ) < (ℓ : ℝ) ^ m := by linarith
  have hM : (Mpar ℓ g h : ℝ) ≤ ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1 := by
    unfold Mpar
    push_cast
    have hc : (((ℓ - 1 : ℕ)) : ℝ) = (ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    have := Nat.cast_div_le (α := ℝ) (m := h + 2 * g) (n := ℓ - 1)
    rw [hc] at this
    push_cast at this
    linarith
  have hM0 : (0 : ℝ) ≤ (Mpar ℓ g h : ℝ) := by positivity
  have hr : (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 ≤ 3 / 4 := by
    rw [div_le_iff₀ hq2]
    nlinarith
  have hr0 : (0 : ℝ) ≤ (ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2 := by positivity
  have hX0 : (0 : ℝ) ≤ ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 + 1 := by
    positivity
  have hceil := Nat.ceil_lt_add_one hX0
  have e1 : ((3 * g : ℝ) + (Mpar ℓ g h : ℝ) / (ℓ : ℝ) ^ m) * ℓ / ((ℓ : ℝ) - 1) ^ 2 =
      3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) +
        (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
    field_simp
  have t1 : 3 * g * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) ≤ 9 / 4 * g := by nlinarith
  have t2 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
      3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) + 3 / 4 := by
    have hB : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by positivity
    have s1 : (Mpar ℓ g h : ℝ) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤
        (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      gcongr
    have s2 : (((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) + 1) * ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m =
        ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) +
          ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m := by
      field_simp
    have s3 : ((h : ℝ) + 2 * g) * ℓ / (((ℓ : ℝ) - 1) ^ 3 * (ℓ : ℝ) ^ m) ≤
        3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (m + 1 + 1) := by
      rw [div_le_div_iff₀ (by positivity) hB]
      have k1 : (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m := by
        have : (ℓ : ℝ) ≤ 3 / 2 * ((ℓ : ℝ) - 1) := by linarith
        calc (ℓ : ℝ) * ((ℓ : ℝ) - 1) ^ m ≤ 3 / 2 * ((ℓ : ℝ) - 1) * ((ℓ : ℝ) - 1) ^ m :=
              mul_le_mul_of_nonneg_right this (by positivity)
          _ ≤ 3 / 2 * ((ℓ : ℝ) - 1) * (ℓ : ℝ) ^ m :=
              mul_le_mul_of_nonneg_left hPq (by positivity)
      have k2 := mul_le_mul_of_nonneg_left k1 (mul_nonneg hA0 hq2.le)
      have e2 : ((ℓ : ℝ) - 1) ^ (m + 1 + 1) = ((ℓ : ℝ) - 1) ^ m * ((ℓ : ℝ) - 1) ^ 2 := by ring
      rw [e2]
      nlinarith [k2]
    have s4 : ((ℓ : ℝ) / ((ℓ : ℝ) - 1) ^ 2) / (ℓ : ℝ) ^ m ≤ 3 / 4 := by
      rw [div_le_iff₀ hP0]
      nlinarith
    linarith
  rw [e1] at hceil ⊢
  linarith

theorem total_exponent_le_eight_hundred : ExponentBoundOfRankAndKappaBounds := by
  intro ℓ hℓ G g h j ell rr kap hj hG hg hgh hell hrr hkap
  have hσ := sigma_exponent_le_real ℓ hℓ g h j hj
  unfold eE a0E
  have hL : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hq : (2 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
  have hB4 : (4 : ℝ) ≤ ((ℓ : ℝ) - 1) ^ (j + 1) := by
    have := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (ℓ : ℝ) - 1) (by omega : 2 ≤ j + 1)
    nlinarith
  have hB0 : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ (j + 1) := by linarith
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hGg : (G : ℝ) ≤ g := by exact_mod_cast hG
  have hgh' : (g : ℝ) ≤ h := by exact_mod_cast hgh
  have hh1 : (1 : ℝ) ≤ h := by linarith
  have hell1 : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hT : (0 : ℝ) ≤ (h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) := by positivity
  have hΛ : (0 : ℝ) ≤ Real.logb ℓ h := Real.logb_nonneg (by linarith) hh1
  have hlog2 : Real.logb ℓ (2 * h) = Real.logb ℓ 2 + Real.logb ℓ h :=
    Real.logb_mul (by norm_num) (by positivity)
  have hl2 : Real.logb ℓ 2 ≤ 1 := by
    have := Real.logb_le_logb_of_le (by linarith : (1 : ℝ) < ℓ) (by norm_num : (0 : ℝ) < 2)
      (by linarith : (2 : ℝ) ≤ ℓ)
    rwa [Real.logb_self_eq_one (by linarith)] at this
  have hGL : (G : ℝ) / ℓ ≤ g / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hgB : (g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) ≤ g / 4 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hB4
  have h4g : 4 * (g : ℝ) / ((ℓ : ℝ) - 1) ≤ 2 * g := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have eσ : 3 / 2 * ((h : ℝ) + 2 * g) / ((ℓ : ℝ) - 1) ^ (j + 1) =
      3 / 2 * ((h : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) + 3 * ((g : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1)) := by
    ring
  rw [eσ] at hσ
  rw [hlog2] at hkap
  have hge : (g : ℝ) ≤ g * ell := by nlinarith
  have hee : (ell : ℝ) ≤ g * ell := by nlinarith
  have h1e : (1 : ℝ) ≤ g * ell := by nlinarith
  nlinarith

end Formalism.TruncatedSeriesCounting.WachCoordinates
end
end

