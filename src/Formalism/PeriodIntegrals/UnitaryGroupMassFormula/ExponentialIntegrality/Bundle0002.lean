module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.InvNatMemWf
section
noncomputable section

namespace PI.ExpIntWProof

open PI

def Wf (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | InWf x}
  mul_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : (p : ℂ_[p]) ^ (a + b) * (x * y) = ((p : ℂ_[p]) ^ a * x) * ((p : ℂ_[p]) ^ b * y) := by ring
    rw [this]
    exact Subring.mul_mem _ ha hb
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have : (p : ℂ_[p]) ^ (a + b) * (x + y) =
        (p : ℂ_[p]) ^ b * ((p : ℂ_[p]) ^ a * x) + (p : ℂ_[p]) ^ a * ((p : ℂ_[p]) ^ b * y) := by ring
    rw [this]
    exact Subring.add_mem _ (Subring.mul_mem _ (Subring.pow_mem _ (p_mem p) b) ha)
      (Subring.mul_mem _ (Subring.pow_mem _ (p_mem p) a) hb)
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro x ⟨a, ha⟩
    exact ⟨a, by rw [mul_neg]; exact Subring.neg_mem _ ha⟩

theorem mem_Wf {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} : x ∈ Wf p ↔ InWf x := Iff.rfl

theorem inv_nat_mem_Wf (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : m ≠ 0) :
    ((m : ℂ_[p]))⁻¹ ∈ Wf p := by
  rw [mem_Wf]
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.ne_one
  refine ⟨k, ?_⟩
  have hpk : (p : ℂ_[p]) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  rw [Nat.cast_mul, Nat.cast_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ hpk, one_mul]
  exact inv_natCast_mem_wittIntegers p u hu

theorem coeff_pow_mem {σ : Type} (p : ℕ) [Fact p.Prime] (f : MvPowerSeries σ ℂ_[p])
    (hf : CoefWf f) : ∀ n : ℕ, ∀ α, MvPowerSeries.coeff α (f ^ n) ∈ Wf p := by
  classical
  intro n
  induction n with
  | zero =>
    intro α
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs
    · exact (Wf p).one_mem
    · exact (Wf p).zero_mem
  | succ n ih =>
    intro α
    rw [pow_succ, MvPowerSeries.coeff_mul]
    exact (Wf p).sum_mem fun x _ => (Wf p).mul_mem (ih x.1) (mem_Wf.mpr (hf x.2))

theorem stepI : StepI := by
  intro p _ σ f hf n
  rw [← mem_Wf]
  show (∑ k ∈ Finset.range _, MvPowerSeries.coeff n (f ^ k) / (k.factorial : ℂ_[p])) ∈ Wf p
  refine (Wf p).sum_mem fun k _ => ?_
  rw [div_eq_mul_inv]
  exact (Wf p).mul_mem (coeff_pow_mem p f hf k n) (inv_nat_mem_Wf p _ (Nat.factorial_ne_zero k))

end PI.ExpIntWProof

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialIntegrality.StepIII
section
noncomputable section

namespace PI.ExpIntWProof

open PI

theorem div_pow_mem (h : KeyW) (p : ℕ) [hp : Fact p.Prime] :
    ∀ k : ℕ, ∀ y : ℂ_[p], y ∈ Wp p → ‖y‖ ≤ ((p : ℝ)⁻¹) ^ k → y / (p : ℂ_[p]) ^ k ∈ Wp p := by
  intro k
  induction k with
  | zero => intro y hy _; simpa using hy
  | succ k ih =>
    intro y hy hnorm
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
    have hpinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have hlt : ‖y‖ < 1 :=
      lt_of_le_of_lt hnorm (pow_lt_one₀ hpos.le hpinv (Nat.succ_ne_zero k))
    have h1 : y / (p : ℂ_[p]) ∈ PI.Wp p := h p y hy hlt
    have h2 : ‖y / (p : ℂ_[p])‖ ≤ ((p : ℝ)⁻¹) ^ k := by
      rw [norm_div, norm_p, div_le_iff₀ hpos, ← pow_succ]
      exact hnorm
    have h3 := ih _ h1 h2
    rwa [div_div, ← pow_succ'] at h3

theorem stepIII_of_key (h : KeyW) : StepIII := by
  intro p hp x hx hnorm
  obtain ⟨k, hk⟩ := hx
  have hp0 : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hn : ‖(p : ℂ_[p]) ^ k * x‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [norm_mul, norm_pow, norm_p]
    exact mul_le_of_le_one_right (by positivity) hnorm
  have h3 := div_pow_mem h p k _ hk hn
  rwa [mul_div_cancel_left₀ _ (pow_ne_zero k hp0)] at h3

theorem expIntW_of_key (h1 : StepI) (h : KeyW) : ExpIntW :=
  expIntW_of_steps h1 (stepIII_of_key h)

end PI.ExpIntWProof

end
end

