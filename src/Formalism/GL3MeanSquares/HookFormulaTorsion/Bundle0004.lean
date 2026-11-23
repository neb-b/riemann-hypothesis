module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0005
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.CardStabilizerVector
public import Formalism.LogVandermondeBounds.LogVandermondeProofs.Bundle0001
public import Formalism.LogVandermondeBounds.Bundle0001

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.DimensionMassJointBound
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

private lemma triangular_numbers_half (k : ℕ) : ∃ A, k * (k - 1) / 2 = A ∧ k * (k + 1) / 2 = A + k ∧ k * k = 2 * A + k := by
  have hY : k * (k + 1) / 2 = k * (k - 1) / 2 + k := by
    have e : k * (k + 1) = k * (k - 1) + k * 2 := by
      cases k with
      | zero => simp
      | succ n => rw [Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  refine ⟨k * (k - 1) / 2, rfl, hY, ?_⟩
  have := half_add_half k
  rw [hY] at this
  linarith

private lemma odd_square_expansion (k s : ℕ) :
    (k + 2 * s + 1) ^ 2 = k * k + 4 * (s * k) + 4 * (s * s) + 2 * k + 4 * s + 1 := by
  ring

private lemma exponent_square_identities (k s A : ℕ) (hA : k * k = 2 * A + k) :
    ((k + 2 * s + 1) ^ 2 - (k + 1) ^ 2 - 2 * s) / 2 = 2 * (s * k) + s + 2 * (s * s) ∧
    ((k + 2 * s + 1) ^ 2 + 3 * k + 1 + 2 * s) / 2 = A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s) := by
  rw [odd_square_expansion, show (k + 1) ^ 2 = k * k + 2 * k + 1 by ring, hA]
  generalize s * k = X
  generalize s * s = Y
  constructor <;> omega

private lemma card_general_linear_group (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) :
    (Fintype.card (GL (Fin n) F) : ℝ) =
      (Fintype.card F : ℝ) ^ (n * n) * ∏ i ∈ range n, (1 - ((Fintype.card F : ℝ)⁻¹) ^ (i + 1)) := by
  rw [cardGeneralLinear F n, ← pow_add, half_add_half]

theorem local_index_formula : LocalColumnIndex := by
  intro F _ _ _ k m hm hme hF
  dsimp only
  have hg3 : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hF
  have hg0 : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_numbers_half k
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have e1 : k + (2 * s + 2) - 1 = k + 2 * s + 1 := by omega
  have e2 : (2 * s + 2) / 2 - 1 = s := by omega
  rw [e1, e2]
  obtain ⟨hb1, hb2⟩ := eulerProductBounds (Fintype.card F : ℝ) hg3 k
  obtain ⟨hc1, hc2⟩ := eulerProductBounds (Fintype.card F : ℝ) hg3 (k + 2 * s + 1)
  refine ⟨⟨_, hb1, hb2, ?_⟩, ⟨_, hc1, hc2, ?_⟩⟩
  · rw [cardGeneralLinear F k, div_eq_iff (pow_ne_zero _ hg0)]
    ring
  · rw [card_general_linear_group F, (exponent_square_identities k s A hA3).1, (exponent_square_identities k s A hA3).2, hA1]
    have hexp : (k + 2 * s + 1) * (k + 2 * s + 1) = (2 * (s * k) + s + 2 * (s * s)) + A +
        (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) := by
      rw [← sq, odd_square_expansion, hA3]
      ring
    rw [hexp, pow_add, pow_add,
      div_eq_iff (mul_ne_zero (pow_ne_zero _ hg0) (pow_ne_zero _ hg0))]
    ring

private lemma prod_two_factor_split (f E : ℕ) (G : Fin 2 → ℝ) (t : Fin 2 → ℕ → ℝ) :
    ∏ i, ∏ ρ ∈ range f, G i ^ E * t i ρ =
      (G 0 * G 1) ^ (E * f) * ∏ i, ∏ ρ ∈ range f, t i ρ := by
  simp only [Fin.prod_univ_two, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [mul_pow, pow_mul, pow_mul]

private lemma prod_half_to_one_bounds (f : ℕ) (t : Fin 2 → ℕ → ℝ) (h : ∀ i ρ, 1 / 2 ≤ t i ρ ∧ t i ρ ≤ 1) :
    ((2 : ℝ) ^ (2 * f))⁻¹ ≤ ∏ i, ∏ ρ ∈ range f, t i ρ ∧ ∏ i, ∏ ρ ∈ range f, t i ρ ≤ 1 := by
  have h0 : ∀ i ρ, 0 ≤ t i ρ := fun i ρ => le_trans (by norm_num) (h i ρ).1
  constructor
  · calc ((2 : ℝ) ^ (2 * f))⁻¹ = ∏ i : Fin 2, ∏ ρ ∈ range f, (1 / 2 : ℝ) := by
          simp only [Finset.prod_const, Finset.card_range, Finset.card_univ, Fintype.card_fin]
          rw [← pow_mul, one_div, inv_pow, mul_comm]
      _ ≤ ∏ i, ∏ ρ ∈ range f, t i ρ :=
          Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun ρ _ => by norm_num)
            (fun i _ => Finset.prod_le_prod₀ (fun ρ _ => by norm_num) (fun ρ _ => (h i ρ).1))
  · exact Finset.prod_le_one₀ (fun i _ => Finset.prod_nonneg fun ρ _ => h0 i ρ)
      (fun i _ => Finset.prod_le_one₀ (fun ρ _ => h0 i ρ) (fun ρ _ => (h i ρ).2))

theorem index_ratio_bound : IndexRatioComparison := by
  intro f k m g₁ g₂ Ipi Isig θ θ' hm hme hg1 hg2 hθ
  dsimp only
  intro hIpi hIsig
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 2 := by
    obtain ⟨u, hu⟩ := hme
    exact ⟨u - 1, by omega⟩
  have e1 : k + (2 * s + 2) - 1 = k + 2 * s + 1 := by omega
  have e2 : (2 * s + 2) / 2 - 1 = s := by omega
  rw [e1, e2] at hIsig
  obtain ⟨A, hA1, hA2, hA3⟩ := triangular_numbers_half k
  rw [(exponent_square_identities k s A hA3).2, prod_two_factor_split] at hIsig
  rw [hA2, prod_two_factor_split] at hIpi
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hIpi hIsig
  obtain ⟨hPl, hPu⟩ := prod_half_to_one_bounds f θ (fun i ρ => ⟨(hθ i ρ).1, (hθ i ρ).2.1⟩)
  obtain ⟨hQl, hQu⟩ := prod_half_to_one_bounds f θ' (fun i ρ => ⟨(hθ i ρ).2.2.1, (hθ i ρ).2.2.2⟩)
  have hX0 : 0 < g₁ * g₂ := by nlinarith
  have hc : (0 : ℝ) < ((2 : ℝ) ^ (2 * f))⁻¹ := by positivity
  have hPpos : 0 < ∏ i, ∏ ρ ∈ range f, θ i ρ := lt_of_lt_of_le hc hPl
  have hN : (g₁ * g₂) ^ ((f : ℝ) * ((2 * s + 2 : ℕ) : ℝ) * (2 * (k : ℝ) + ((2 * s + 2 : ℕ) : ℝ) - 1) / 2) =
      (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) := by
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hratio : Isig / Ipi = (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) *
      ((∏ i, ∏ ρ ∈ range f, θ' i ρ) / ∏ i, ∏ ρ ∈ range f, θ i ρ) := by
    rw [hIsig, hIpi]
    have e : (A + 3 * k + 1 + 2 * (s * k) + 3 * s + 2 * (s * s)) * f =
        (A + k) * f + (2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f := by ring
    rw [e, pow_add, mul_assoc, mul_div_mul_left _ _ (pow_pos hX0 _).ne', mul_div_assoc]
  rw [hN, hratio]
  have hXN : 0 ≤ (g₁ * g₂) ^ ((2 * (s * k) + 2 * (s * s) + 3 * s + 2 * k + 1) * f) :=
    (pow_pos hX0 _).le
  have h22 : (2 : ℝ) ^ (2 * f) * ((2 : ℝ) ^ (2 * f))⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  constructor
  · rw [mul_comm ((2 : ℝ) ^ (2 * f))⁻¹]
    refine mul_le_mul_of_nonneg_left ?_ hXN
    rw [le_div_iff₀ hPpos]
    nlinarith
  · rw [mul_comm ((2 : ℝ) ^ (2 * f))]
    refine mul_le_mul_of_nonneg_left ?_ hXN
    rw [div_le_iff₀ hPpos]
    nlinarith [mul_le_mul_of_nonneg_left hPl (by positivity : (0 : ℝ) ≤ 2 ^ (2 * f))]

private lemma increments_sum_lower_bound (m : ℕ) (b : ℕ → ℝ) (h₀ : ℝ) (hb : ∀ j, j + 1 < m → h₀ ≤ b (j + 1) - b j)
    (a : ℕ) : ∀ d, a + d < m → (d : ℝ) * h₀ ≤ b (a + d) - b a := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have h1 := ih (by omega)
    have h2 := hb (a + d) (by omega)
    rw [← add_assoc]
    push_cast
    linarith

theorem least_noncompact_gap : LeastNoncompactGap := by
  intro k m v b h₀ hk hh hv hb0 hb i j hij hj hsg
  simp only [plusSign, ne_eq, decide_eq_decide] at hsg
  by_cases hi : i < k - 1
  · by_cases hj' : j < k - 1
    · exact absurd ⟨fun _ => Or.inl hj', fun _ => Or.inl hi⟩ hsg
    · have hodd : (j - (k - 1)) % 2 = 1 := by
        by_contra hc
        exact hsg ⟨fun _ => Or.inr (by omega), fun _ => Or.inl hi⟩
      simp only [rowPar, hi, hj', if_true, if_false]
      have hst := increments_sum_lower_bound m b h₀ hb 0 (j - (k - 1)) (by omega)
      simp only [zero_add] at hst
      have h1 : (1 : ℝ) ≤ ((j - (k - 1) : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j - (k - 1))
      have := hv i hi
      nlinarith [mul_le_mul_of_nonneg_right h1 hh]
  · have hj' : ¬ j < k - 1 := by omega
    simp only [rowPar, hi, hj', if_false]
    have hst := increments_sum_lower_bound m b h₀ hb (i - (k - 1)) (j - (k - 1) - (i - (k - 1))) (by omega)
    have e : i - (k - 1) + (j - (k - 1) - (i - (k - 1))) = j - (k - 1) := by omega
    rw [e] at hst
    have h1 : (1 : ℝ) ≤ ((j - (k - 1) - (i - (k - 1)) : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ j - (k - 1) - (i - (k - 1)))
    nlinarith [mul_le_mul_of_nonneg_right h1 hh]

end Formalism.HermitianLattices.GenusMassVolumes
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.FiniteEulerProductLeZeta
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

theorem global_arithmetic_identity : GlobalArithmeticIdentity := by
  intro f M v Lv hM hv hL
  show ((((2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)) ^ f * ((2 * v) ^ f) ^ ((1 : ℝ) / 2 - M) / Lv)⁻¹ =
    (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f / Real.sqrt ((2 * v) ^ f) * Lv)
  have hd : (0 : ℝ) < (2 * v) ^ f := by positivity
  rw [Real.rpow_sub hd, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt ((2 * v) ^ f) := Real.sqrt_pos.2 hd
  have hfac : (0 : ℝ) < ((M - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpi := Real.pi_pos
  have key : ((2 * v) ^ f) ^ M = ((2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)) ^ f *
      (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f := by
    rw [← pow_mul, mul_comm f M, pow_mul, ← mul_pow]
    congr 1
    rw [div_pow]
    field_simp
    ring
  rw [key]
  have hA : (0 : ℝ) < (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) := by positivity
  have hB : (0 : ℝ) < ((M - 1).factorial : ℝ) * (v / Real.pi) ^ M := by positivity
  generalize (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) = A at hA ⊢
  generalize ((M - 1).factorial : ℝ) * (v / Real.pi) ^ M = B at hB ⊢
  have hAf : 0 < A ^ f := pow_pos hA f
  have hBf : 0 < B ^ f := pow_pos hB f
  field_simp

end Formalism.HermitianLattices.GenusMassVolumes
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.HilbertSchmidtHalfBound
section
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

section A
open Finset

end A

section B
open Finset
open scoped ComplexOrder

end B

section C
open Finset MeasureTheory
open scoped ComplexOrder


end C

section D
open Finset
open scoped Nat

end D

section E
open Finset Matrix Unitary

end E

section F
open Finset

def bb (k rS : ℕ) (i : ℕ) : ℕ := if i < rS then i else if i < rS + (k + 1) then rS else i - k
def cc (k rS : ℕ) (j : ℕ) : ℕ := if j < rS then j else if j < rS + (k + 1) then rS else j

lemma inner (k rS j : ℕ) (hj : j < rS + (k + 1) + rS) :
    ((range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j)).card = cc k rS j := by
  have h : (range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j) = range (cc k rS j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    simp only [bb, cc]
    constructor
    · rintro ⟨h1, h2⟩
      split_ifs at h2 ⊢ <;> omega
    · intro h1
      refine ⟨by split_ifs at h1 <;> omega, ?_⟩
      split_ifs at h1 ⊢ <;> omega
  rw [h, card_range]

lemma total (k rS : ℕ) : ∑ j ∈ range (rS + (k + 1) + rS), cc k rS j = rS * (2 * k + 1 + 2 * rS) := by
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ x ∈ range rS, cc k rS x = ∑ x ∈ range rS, x :=
    Finset.sum_congr rfl fun x hx => by simp [cc, mem_range.1 hx]
  have e2 : ∑ x ∈ range (k + 1), cc k rS (rS + x) = ∑ x ∈ range (k + 1), rS :=
    Finset.sum_congr rfl fun x hx => by
      have := mem_range.1 hx
      simp only [cc]
      split_ifs <;> omega
  have e3 : ∑ x ∈ range rS, cc k rS (rS + (k + 1) + x) = ∑ x ∈ range rS, (rS + (k + 1) + x) :=
    Finset.sum_congr rfl fun x _ => by
      simp only [cc]
      split_ifs <;> omega
  rw [e1, e2, e3, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, card_range, card_range,
    smul_eq_mul, smul_eq_mul]
  have hS := Finset.sum_range_id_mul_two rS
  rcases rS with _ | m
  · simp
  · simp only [Nat.add_sub_cancel] at hS
    nlinarith [hS]

lemma countFree (k rS r : ℕ) (hr : r = rS + (k + 1) + rS) :
    (univ.filter (fun ij : Fin r × Fin r => bb k rS ij.1.val < bb k rS ij.2.val)).card =
      rS * (2 * k + 1 + 2 * rS) := by
  subst hr
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h : ∀ j : Fin (rS + (k + 1) + rS),
      ∑ i : Fin (rS + (k + 1) + rS), (if bb k rS i.val < bb k rS j.val then 1 else 0) = cc k rS j.val := by
    intro j
    have h1 := inner k rS j.val j.isLt
    rw [Finset.card_filter] at h1
    rw [Fin.sum_univ_eq_sum_range (fun i => if bb k rS i < bb k rS j.val then 1 else 0), h1]
  rw [Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun j => cc k rS j), total]

end F

end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

namespace Formalism.HermitianLattices.CumulantEstimateDefs

end Formalism.HermitianLattices.CumulantEstimateDefs
end

-- bundled from Formalism.GL3MeanSquares.HookFormulaTorsion.OneAddInvPowLeExpOne
section
namespace Formalism.HermitianLattices.GenusMassVolumes

open Finset
open Formalism.LogVandermondeBounds.StandardLattice

private lemma one_add_inv_pow_le_exp_one (N : ℕ) (hN : 1 ≤ N) :
    (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp 1 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc (1 + 1 / (N : ℝ)) ^ N ≤ (Real.exp (1 / N)) ^ N := by
        gcongr
        linarith [Real.add_one_le_exp (1 / (N : ℝ))]
    _ = Real.exp 1 := by rw [← Real.exp_nat_mul, mul_one_div_cancel hN']

theorem mass_corollary : PowerProductTwoSidedBounds := by
  intro f k T X Γ Dstar dstar dM lo hi hf hk hfk2 hT hX hΓ hD hd hXD hlow hup hdM hlo hhi
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr hf
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hN : (0:ℝ) < f * k := mul_pos hf' hk'
  have hN1 : 1 ≤ f * k := by simpa using Nat.mul_le_mul hf hk
  have hΓ0 : 0 < Γ := by linarith
  have hT0 : 0 < T := by linarith
  set r : ℝ := -(2:ℝ) / ((f:ℝ) * k) with hr
  set Y : ℝ := X * Γ ^ r with hY
  have hYpos : 0 < Y := mul_pos hX (Real.rpow_pos_of_pos hΓ0 r)
  have hrN : r * ((f * k : ℕ) : ℝ) = -2 := by rw [hr, Nat.cast_mul, div_mul_cancel₀ _ hN.ne']
  have hYN : Y ^ (f * k) = Dstar * (Γ⁻¹) ^ 2 / dstar := by
    rw [hY, mul_pow, hXD, ← Real.rpow_natCast (Γ ^ r), ← Real.rpow_mul hΓ0.le, hrN, Real.rpow_neg hΓ0.le,
      Real.rpow_two, inv_pow]
    ring
  have hdY : dstar * Y ^ (f * k) = Dstar * (Γ⁻¹) ^ 2 := by rw [hYN]; field_simp
  have hTk : 1 ≤ T ^ k := one_le_pow₀ (by linarith)
  have hTkpos : 0 < T ^ k := lt_of_lt_of_le one_pos hTk
  have hB : (T ^ k - 1) ^ f ≤ Y ^ (f * k) * Real.exp 1 := by
    calc (T ^ k - 1) ^ f ≤ (T ^ k) ^ f := by gcongr <;> linarith
      _ = T ^ (f * k) := by rw [← pow_mul, mul_comm]
      _ ≤ (Y * (1 + 1 / ((f:ℝ) * k))) ^ (f * k) := by gcongr <;> linarith
      _ = Y ^ (f * k) * (1 + 1 / ((f * k : ℕ) : ℝ)) ^ (f * k) := by rw [mul_pow, Nat.cast_mul]
      _ ≤ Y ^ (f * k) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (one_add_inv_pow_le_exp_one _ hN1) (pow_nonneg hYpos.le _)
  have hq : (f:ℝ) * (1 / T ^ k) ≤ 1 / 2 := by
    have h2k : (2:ℝ) ^ k ≤ T ^ k := by gcongr
    have h2f : (2 * f : ℝ) ≤ 2 ^ k := by exact_mod_cast hfk2
    rw [mul_one_div, div_le_iff₀ hTkpos]
    linarith
  have hle1 : 1 / T ^ k ≤ 1 := (div_le_one hTkpos).2 hTk
  have hBer : 1 + (f:ℝ) * (-(1 / T ^ k)) ≤ (1 + -(1 / T ^ k)) ^ f := one_add_mul_le_pow (by linarith) f
  have hfac : T ^ k - 1 = T ^ k * (1 + -(1 / T ^ k)) := by
    rw [mul_add, mul_one, mul_neg, mul_one_div_cancel hTkpos.ne']
    ring
  have hA : Y ^ (f * k) / 2 ≤ (T ^ k - 1) ^ f := by
    have h1 : Y ^ (f * k) ≤ (T ^ k) ^ f := by
      rw [← pow_mul, mul_comm k f]
      exact pow_le_pow_left₀ hYpos.le hlow _
    have h2 : 1 / 2 ≤ (1 + -(1 / T ^ k)) ^ f := by linarith
    have h3 : 0 ≤ (T ^ k) ^ f := pow_nonneg hTkpos.le _
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    calc Y ^ (f * k) / 2 = Y ^ (f * k) * (1 / 2) := by ring
      _ ≤ (T ^ k) ^ f * (1 / 2) := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ ≤ (T ^ k) ^ f * (1 + -(1 / T ^ k)) ^ f := h4
      _ = (T ^ k - 1) ^ f := by rw [hfac, mul_pow]
  have hΓr : Γ ^ r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΓ (by
    rw [hr]; exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hN.le)
  have hYX : Y ≤ X := mul_le_of_le_one_right hX.le hΓr
  have hinv : 1 / ((f:ℝ) * k) ≤ 1 := (div_le_one hN).2 (by exact_mod_cast hN1)
  have hT2X : T ≤ 2 * X := by nlinarith
  have hlogY : Real.log Y = Real.log X + r * Real.log Γ := by
    rw [hY, Real.log_mul hX.ne' (Real.rpow_pos_of_pos hΓ0 r).ne', Real.log_rpow hΓ0]
  have hr2 : r * Real.log Γ = -(2 * Real.log Γ / ((f:ℝ) * k)) := by rw [hr]; ring
  have hYT : Real.log Y ≤ Real.log T := Real.log_le_log hYpos hlow
  have hT2 : Real.log T ≤ Real.log 2 + Real.log X := by
    rw [← Real.log_mul two_ne_zero hX.ne']
    exact Real.log_le_log hT0 hT2X
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdM, ← hdY]
    calc dstar * Y ^ (f * k) / 2 = dstar * (Y ^ (f * k) / 2) := by ring
      _ ≤ dstar * (T ^ k - 1) ^ f := mul_le_mul_of_nonneg_left hA hd.le
  · rw [hdM, ← hdY]
    calc dstar * (T ^ k - 1) ^ f ≤ dstar * (Y ^ (f * k) * Real.exp 1) := mul_le_mul_of_nonneg_left hB hd.le
      _ = Real.exp 1 * (dstar * Y ^ (f * k)) := by ring
  · linarith
  · linarith

end Formalism.HermitianLattices.GenusMassVolumes
end

