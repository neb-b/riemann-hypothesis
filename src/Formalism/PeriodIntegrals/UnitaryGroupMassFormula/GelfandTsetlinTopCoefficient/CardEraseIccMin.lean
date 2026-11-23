module

public import Mathlib

@[expose] public section

namespace PI.GTNum

open Finset

theorem card_erase_Icc_min (a b c x : ℤ) (hab : a ≤ b) (hc : 0 ≤ c)
    (hx : x ∈ Icc a (min b (a + c))) :
    ((((Icc a (min b (a + c))).erase x).card : ℕ) : ℤ) = min (b - a) c := by
  rw [Finset.card_erase_of_mem hx, Int.card_Icc]
  have h1 : 1 ≤ (min b (a + c) + 1 - a).toNat := by omega
  rw [Nat.cast_sub h1, Int.toNat_of_nonneg (by omega)]
  push_cast
  omega

theorem abs_prod_le_prod {α : Type*} (s : Finset α) (f b : α → ℤ) (h : ∀ x ∈ s, |f x| ≤ b x) :
    |∏ x ∈ s, f x| ≤ ∏ x ∈ s, b x := by
  rw [abs_prod]
  exact Finset.prod_le_prod₀ (fun x _ => abs_nonneg _) h

theorem abs_prod_le_pow {α : Type*} (s : Finset α) (f : α → ℤ) (B : ℤ) (h : ∀ x ∈ s, |f x| ≤ B) :
    |∏ x ∈ s, f x| ≤ B ^ s.card := by
  simpa [Finset.prod_const] using abs_prod_le_prod s f (fun _ => B) h

theorem prod_pow_pow {α : Type*} (s : Finset α) (B : ℤ) (m : ℕ) (e : α → ℕ) :
    ∏ x ∈ s, (B ^ m) ^ e x = B ^ (m * ∑ x ∈ s, e x) := by
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]

end PI.GTNum
