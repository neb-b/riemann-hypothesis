module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GuLine

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffPowMemS
section
noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem wq_const {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    PowerSeries.constantCoeff wq = 1 := by
  simp only [IsWq] at h
  have h1 := congrArg PowerSeries.constantCoeff h
  simpa using h1

theorem coeff_mul_memS {S : Subring ℂ_[p]} {f g : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (hg : ∀ i ≤ m, PowerSeries.coeff i g ∈ S) :
    PowerSeries.coeff m (f * g) ∈ S := by
  rw [PowerSeries.coeff_mul]
  refine S.sum_mem fun x hx => S.mul_mem (hf _ ?_) (hg _ ?_)
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega
  · have := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
    omega

theorem coeff_pow_memS {S : Subring ℂ_[p]} {f : PowerSeries ℂ_[p]} {m : ℕ}
    (hf : ∀ i ≤ m, PowerSeries.coeff i f ∈ S) (k : ℕ) : ∀ i ≤ m, PowerSeries.coeff i (f ^ k) ∈ S := by
  induction k with
  | zero =>
    intro i _
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  | succ k ih =>
    intro i hi
    rw [pow_succ]
    exact coeff_mul_memS (fun j hj => ih j (hj.trans hi)) (fun j hj => hf j (hj.trans hi))

theorem coeff_termS (a : ℂ_[p]) (k n : ℕ) (f : PowerSeries ℂ_[p]) :
    PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X ^ k * f) =
      if k ≤ n then a * PowerSeries.coeff (n - k) f else 0 := by
  rw [mul_assoc, ← Algebra.smul_def, PowerSeries.coeff_smul, PowerSeries.coeff_X_pow_mul']
  split_ifs <;> simp

theorem wq_mem {S : Subring ℂ_[p]} {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]}
    (h1 : W.a₁ ∈ S) (h2 : W.a₂ ∈ S) (h3 : W.a₃ ∈ S) (h4 : W.a₄ ∈ S) (h6 : W.a₆ ∈ S) (h : IsWq W wq) :
    ∀ n, PowerSeries.coeff n wq ∈ S := by
  have t1 : ∀ (a : ℂ_[p]) (f : PowerSeries ℂ_[p]) (n : ℕ),
      PowerSeries.coeff n (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a * PowerSeries.X * f) =
        if 1 ≤ n then a * PowerSeries.coeff (n - 1) f else 0 := by
    intro a f n
    rw [← coeff_termS, pow_one]
  simp only [IsWq] at h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hc := congrArg (PowerSeries.coeff n) h
    rw [hc]
    simp only [map_add (f := _), t1, coeff_termS, PowerSeries.coeff_one]
    refine S.add_mem (S.add_mem (S.add_mem (S.add_mem (S.add_mem ?_ ?_) ?_) ?_) ?_) ?_
    · split_ifs
      · exact S.one_mem
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h1 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h2 (ih _ (by omega))
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h3 (coeff_pow_memS (m := n - 3) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h4 (coeff_pow_memS (m := n - 4) (fun i hi => ih i (by omega)) 2 _ le_rfl)
      · exact S.zero_mem
    · split_ifs with hn
      · exact S.mul_mem h6 (coeff_pow_memS (m := n - 6) (fun i hi => ih i (by omega)) 3 _ le_rfl)
      · exact S.zero_mem

theorem G_wser {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    G W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) = 0 := by
  simp only [IsWq] at h
  unfold G wser
  rw [sub_eq_zero]
  conv_rhs => rw [h]
  ring

end PI.AddIntG.Wk
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DvCoeffMulEqZeroOfLtOrder
section
noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem dv_exists_lt_order_pow {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (N : ℕ) : ∃ m : ℕ, (N : ℕ∞) < (a ^ m).order := by
  obtain ⟨k, hk⟩ := ha
  refine ⟨k * (N + 1), ?_⟩
  have h0 : MvPowerSeries.constantCoeff (a ^ k) = 0 := by rw [map_pow]; exact hk
  have := MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (N + 1) h0
  rw [← pow_mul] at this
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) this

theorem dv_coeff_mul_eq_zero_of_lt_order {R : Type*} [CommRing R] {σ : Type*} (f g : MvPowerSeries σ R)
    (e : σ →₀ ℕ) (h : (e.degree : ℕ∞) < f.order) : MvPowerSeries.coeff e (f * g) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le h (le_trans le_self_add MvPowerSeries.le_order_mul)

theorem dv_pderiv_subst_coe {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (P : Polynomial R) (i : σ) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a (P : PowerSeries R)) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) (P : PowerSeries R)) * MvPowerSeries.pderiv (R := R) i a := by
  rw [PowerSeries.derivative_coe, PowerSeries.subst_coe ha, PowerSeries.subst_coe ha,
    Derivation.comp_aeval_eq, smul_eq_mul]

theorem pderiv_subst {R : Type*} [CommRing R] {σ : Type*} {a : MvPowerSeries σ R}
    (ha : PowerSeries.HasSubst a) (f : PowerSeries R) (i : σ) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a f) =
      PowerSeries.subst a (PowerSeries.derivative (R := R) f) * MvPowerSeries.pderiv (R := R) i a := by
  rw [← sub_eq_zero]
  ext e
  rw [map_zero]
  obtain ⟨m, hm⟩ := dv_exists_lt_order_pow ha e.degree
  set g : PowerSeries R := PowerSeries.mk fun n => PowerSeries.coeff (n + m) f
  have hf : f = ((PowerSeries.trunc m f : Polynomial R) : PowerSeries R) + PowerSeries.X ^ m * g := by
    ext n
    rw [map_add (f := _), Polynomial.coeff_coe, PowerSeries.coeff_trunc, PowerSeries.coeff_X_pow_mul']
    by_cases hn : n < m
    · simp [hn, not_le.mpr hn]
    · simp [hn, not_lt.mp hn, g, Nat.sub_add_cancel (not_lt.mp hn)]
  have key : MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a f) -
      PowerSeries.subst a (PowerSeries.derivative (R := R) f) * MvPowerSeries.pderiv (R := R) i a =
      a ^ m * (MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a g) -
        PowerSeries.subst a (PowerSeries.derivative (R := R) g) * MvPowerSeries.pderiv (R := R) i a) := by
    have hc : PowerSeries.subst a ((m : PowerSeries R)) = (m : MvPowerSeries σ R) := by
      rw [← map_natCast (PowerSeries.C (R := R)), PowerSeries.subst_C, map_natCast]
    conv_lhs => rw [hf]
    simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      PowerSeries.derivative_X, mul_one]
    simp only [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha,
      PowerSeries.subst_X ha, hc]
    simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul,
      dv_pderiv_subst_coe ha]
    ring
  rw [key]
  exact dv_coeff_mul_eq_zero_of_lt_order _ _ e hm

theorem derivative_flog (W : WeierstrassCurve ℂ_[p]) (wq : PowerSeries ℂ_[p]) :
    PowerSeries.derivative (R := ℂ_[p]) (flog W wq) = omegaW W wq := by
  ext n
  rw [PowerSeries.coeff_derivative, flog, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n),
    Nat.add_sub_cancel]
  have h : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

end PI.AddIntG.Wk
end
end

