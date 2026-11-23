module

public import Formalism.PeriodIntegrals.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteExtensionTopology.AddPreservesExpCongruence
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.FinExtTop

open PI.FinExtTop Topology Filter

section

variable {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']

def fracB (ϖ : O') (i : ℕ) : Submodule O' (FractionRing O') :=
  Submodule.span O' {algebraMap O' (FractionRing O') (ϖ ^ i)}

theorem mem_fracB {ϖ : O'} {i : ℕ} {x : FractionRing O'} :
    x ∈ fracB ϖ i ↔ ∃ c : O', x = algebraMap O' (FractionRing O') (c * ϖ ^ i) := by
  simp only [fracB, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩

theorem algebraMap_mem_fracB {ϖ : O'} {i : ℕ} {x : O'} :
    algebraMap O' (FractionRing O') x ∈ fracB ϖ i ↔ ϖ ^ i ∣ x := by
  rw [mem_fracB]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [mul_comm]; exact IsFractionRing.injective O' (FractionRing O') hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [mul_comm]⟩

theorem fracB_anti (ϖ : O') {i j : ℕ} (h : i ≤ j) : fracB ϖ j ≤ fracB ϖ i := by
  intro x hx
  rw [mem_fracB] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c * ϖ ^ (j - i), by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]⟩

theorem exists_pow_mul_mem {ϖ : O'} (hϖ : Irreducible ϖ) (a : FractionRing O') :
    ∃ n : ℕ, ∃ c : O', algebraMap O' (FractionRing O') (ϖ ^ n) * a =
      algebraMap O' (FractionRing O') c := by
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O') a
  have hy : (y : O') ≠ 0 := nonZeroDivisors.ne_zero y.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  refine ⟨n, x * ↑u⁻¹, ?_⟩
  have hy' : algebraMap O' (FractionRing O') (y : O') =
      algebraMap O' (FractionRing O') (↑u) * algebraMap O' (FractionRing O') (ϖ ^ n) := by
    rw [hu, map_mul]
  have hu1 : algebraMap O' (FractionRing O') (↑u) * algebraMap O' (FractionRing O') (↑u⁻¹) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hxy' : a * algebraMap O' (FractionRing O') (y : O') = algebraMap O' (FractionRing O') x := hxy
  rw [map_mul, ← hxy']
  linear_combination (-(a * algebraMap O' (FractionRing O') (↑u⁻¹))) * hy' +
    (-(algebraMap O' (FractionRing O') (ϖ ^ n) * a)) * hu1

theorem fracB_basis {ϖ : O'} (hϖ : Irreducible ϖ) : SubmodulesRingBasis (fracB ϖ) := by
  constructor
  · intro i j
    exact ⟨max i j, le_inf (fracB_anti ϖ (le_max_left _ _)) (fracB_anti ϖ (le_max_right _ _))⟩
  · intro a i
    obtain ⟨n, c, hc⟩ := exists_pow_mul_mem hϖ a
    refine ⟨i + n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨d, rfl⟩ := mem_fracB.1 hx
    refine mem_fracB.2 ⟨c * d, ?_⟩
    have e : algebraMap O' (FractionRing O') (d * ϖ ^ (i + n)) =
        algebraMap O' (FractionRing O') (d * ϖ ^ i) * algebraMap O' (FractionRing O') (ϖ ^ n) := by
      rw [← map_mul, pow_add, mul_assoc]
    show a * _ = _
    rw [e, mul_comm (algebraMap O' (FractionRing O') (d * ϖ ^ i)), ← mul_assoc, mul_comm a, hc,
      ← map_mul]
    congr 1
    ring
  · intro i
    refine ⟨i, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_fracB.1 hx
    obtain ⟨d, rfl⟩ := mem_fracB.1 hy
    exact mem_fracB.2 ⟨c * d * ϖ ^ i, by show _ * _ = _; rw [← map_mul]; congr 1; ring⟩

end

end PI.UnitaryGroupMassFormula.FinExtTop
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteExtensionTopology.ExpCongruenceExtendsToSum
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.FinExtTop

open PI.FinExtTop

theorem torsionFree_pi_matrix (O' : Type) [CommRing O'] [IsDomain O'] (X' d : Type) [Fintype d]
    [DecidableEq d] : Module.IsTorsionFree O' (X' → Matrix d d (FractionRing O')) where
  isSMulRegular r hr f g h := by
    have hr0 : algebraMap O' (FractionRing O') r ≠ 0 := by
      intro h0
      exact hr.ne_zero ((IsFractionRing.injective O' (FractionRing O')).eq_iff.1
        (h0.trans (map_zero _).symm))
    have h' : algebraMap O' (FractionRing O') r • f = algebraMap O' (FractionRing O') r • g := by
      simpa only [algebraMap_smul] using h
    exact ((IsUnit.mk0 _ hr0).smul_left_cancel).1 h'

end PI.UnitaryGroupMassFormula.FinExtTop
end
end

