module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdInertClosed
section
noncomputable section

namespace PI.OmVe

theorem prodSplit_closed (x : ℝ) (hx : x ≠ 0) (M : ℕ) : ∀ a, a ≤ M →
    ∏ i : Fin a, (x ^ M - x ^ (i : ℕ)) = x ^ (M * a) * ∏ j ∈ Finset.Icc (M - a + 1) M, (1 - x ^ (-(j : ℤ))) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show a + 1 + m - a + 1 = m + 1 + 1 by omega,
      show a + 1 + m - (a + 1) + 1 = m + 1 by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : m + 1 ≤ a + 1 + m), Finset.prod_insert (by simp),
      mul_add_one, zpow_neg, zpow_natCast]
    have hpow : x ^ (a + 1 + m) = x ^ a * x ^ (m + 1) := by
      rw [← pow_add]
      ring_nf
    rw [pow_add x ((a + 1 + m) * a) (a + 1 + m), hpow]
    have hw : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
    field_simp

theorem prodInert_closed (x : ℝ) (hx : x ≠ 0) (M : ℕ) : ∀ a, a ≤ M →
    ∏ j : Fin a, (x ^ (2 * (M - j) - 1) - (-1) ^ (M - j) * x ^ (M - j - 1)) =
      x ^ (2 * M * a - a ^ 2) * ∏ j ∈ Finset.Icc (M - a + 1) M, (1 - (-1) ^ j * x ^ (-(j : ℤ))) := by
  intro a
  induction a with
  | zero => intro _; simp
  | succ a ih =>
    intro ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih (by omega), show a + 1 + m - a + 1 = m + 1 + 1 by omega,
      show a + 1 + m - (a + 1) + 1 = m + 1 by omega,
      ← Finset.insert_Icc_add_one_left_eq_Icc (by omega : m + 1 ≤ a + 1 + m), Finset.prod_insert (by simp),
      zpow_neg, zpow_natCast, show a + 1 + m - a = m + 1 by omega,
      show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show m + 1 - 1 = m by omega]
    have h1 : 2 * (a + 1 + m) * a - a ^ 2 = a ^ 2 + 2 * a + 2 * a * m := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    have h2 : 2 * (a + 1 + m) * (a + 1) - (a + 1) ^ 2 = a ^ 2 + 2 * a + 2 * a * m + (2 * m + 1) := by
      rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
      ring
    rw [h1, h2, pow_add]
    have hw : x ^ (m + 1) ≠ 0 := pow_ne_zero _ hx
    field_simp
    ring

end PI.OmVe
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.QuadRoot
section
noncomputable section

open Polynomial IsLocalRing

namespace PI.OmVf

theorem quad_root {R : Type*} [CommRing R] [HenselianLocalRing R] (A B K : R) (hA : A ∈ maximalIdeal R)
    (hB : IsUnit B) : ∃ s : R, A * s ^ 2 + B * s + K = 0 := by
  obtain ⟨u, hu⟩ := hB.exists_right_inv
  have haK : A * u * u * K ∈ maximalIdeal R := by
    have h1 : A * u * u * K = A * (u * u * K) := by ring
    rw [h1]; exact Ideal.mul_mem_right _ _ hA
  obtain ⟨w, hwr, hwm⟩ := HenselianLocalRing.is_henselian
    (X ^ 2 + X + Polynomial.C (A * u * u * K)) (by monicity!) 0
    (by simpa using haK) (by simp)
  have hw : w ^ 2 + w + A * u * u * K = 0 := by simpa using hwr
  have hwm' : w ∈ maximalIdeal R := by simpa using hwm
  have hunit : IsUnit (1 + w) := by
    by_contra hn
    have h1 : 1 + w ∈ maximalIdeal R := (mem_maximalIdeal _).mpr hn
    have h2 : (1 : R) ∈ maximalIdeal R := by
      have e : (1 : R) = (1 + w) - w := by ring
      rw [e]; exact Ideal.sub_mem _ h1 hwm'
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h2)
  obtain ⟨v, hv⟩ := hunit.exists_right_inv
  refine ⟨-(u * K * v), ?_⟩
  linear_combination K * v ^ 2 * hw - K * (2 - v + ((1 + w) * v - 1)) * hv - K * v * hu

end PI.OmVf
end
end

