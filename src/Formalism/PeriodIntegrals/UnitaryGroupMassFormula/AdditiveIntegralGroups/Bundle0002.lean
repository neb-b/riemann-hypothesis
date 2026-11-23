module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.CoeffWSeriesVarZero
section
noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem lamA_coeff_wser (wq : PowerSeries ℂ_[p]) (n : ℕ) :
    PowerSeries.coeff n (wser wq) = if 3 ≤ n then PowerSeries.coeff (n - 3) wq else 0 := by
  simp [wser, PowerSeries.coeff_X_pow_mul']

theorem lamA_coeff_lam (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam wq) = PowerSeries.coeff (e 0 + e 1 + 1) (wser wq) := rfl

theorem lamA_single0 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 0 (e 0) ↔ e 1 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem lamA_single1 (e : Fin 2 →₀ ℕ) : e = Finsupp.single 1 (e 1) ↔ e 0 = 0 := by
  constructor
  · intro h; rw [h]; simp
  · intro h; ext j; fin_cases j <;> simp [h]

theorem coeff_wSeriesVar_zero (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 0) = if e 1 = 0 then PowerSeries.coeff (e 0) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single0 e) rfl rfl

theorem coeff_wSeriesVar_one (wq : PowerSeries ℂ_[p]) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (wv wq 1) = if e 0 = 0 then PowerSeries.coeff (e 1) (wser wq) else 0 := by
  rw [wv, Xv, PowerSeries.coeff_subst_single]
  exact if_congr (lamA_single1 e) rfl rfl

theorem lamA_coeff_mul_X (f : MvPowerSeries (Fin 2) ℂ_[p]) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (f * Xv i) =
      if 1 ≤ e i then MvPowerSeries.coeff (e - Finsupp.single i 1) f else 0 := by
  rw [Xv, MvPowerSeries.X_def, MvPowerSeries.coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff]

theorem lam_mul (wq : PowerSeries ℂ_[p]) :
    (Xv 1 - Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) * lam wq = wv wq 1 - wv wq 0 := by
  ext e
  rw [sub_mul, map_sub, map_sub, mul_comm (Xv 1), mul_comm (Xv 0), lamA_coeff_mul_X, lamA_coeff_mul_X,
    coeff_wSeriesVar_zero, coeff_wSeriesVar_one, lamA_coeff_lam, lamA_coeff_lam]
  have a1 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 0 = e 0 := by simp
  have a2 : (e - (Finsupp.single 1 1 : Fin 2 →₀ ℕ)) 1 = e 1 - 1 := by simp
  have a3 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 0 = e 0 - 1 := by simp
  have a4 : (e - (Finsupp.single 0 1 : Fin 2 →₀ ℕ)) 1 = e 1 := by simp
  rw [a1, a2, a3, a4]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0
  · simp [h0, h1]
  · have : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    simp [h0, h1, this]
  · have : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h2 : e 0 - 1 + 0 + 1 = e 0 := by omega
    simp [h0, h1, this, h2]
  · have h3 : 1 ≤ e 0 := Nat.one_le_iff_ne_zero.mpr h0
    have h4 : 1 ≤ e 1 := Nat.one_le_iff_ne_zero.mpr h1
    have h2 : e 0 - 1 + e 1 + 1 = e 0 + (e 1 - 1) + 1 := by omega
    simp [h0, h1, h3, h4, h2]

theorem wv_line1 (wq : PowerSeries ℂ_[p]) : wv wq 1 = lam wq * Xv 1 + nu wq := by
  have h := lam_mul wq
  simp only [nu]
  linear_combination -h

theorem constantCoeff_lam (wq : PowerSeries ℂ_[p]) : MvPowerSeries.constantCoeff (lam wq) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, lamA_coeff_lam, lamA_coeff_wser]
  simp

theorem lamA_wser_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S)
    (n : ℕ) : PowerSeries.coeff n (wser wq) ∈ S := by
  rw [lamA_coeff_wser]; split_ifs
  · exact hS _
  · exact S.zero_mem

theorem lam_mem {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∀ e, MvPowerSeries.coeff e (lam wq) ∈ S := by
  intro e
  rw [lamA_coeff_lam]
  exact lamA_wser_mem hS _

theorem G_wv {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) (i : Fin 2) :
    G W (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) (wv wq i) = 0 := by
  have hs : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) := PowerSeries.HasSubst.X i
  set φ := PowerSeries.substAlgHom (R := ℂ_[p]) hs with hφ
  have hX : (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = φ PowerSeries.X := by
    rw [hφ, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs]
  have hw : wv wq i = φ (wser wq) := by
    rw [hφ, PowerSeries.coe_substAlgHom]; rfl
  rw [hX, hw]
  have : G W (φ PowerSeries.X) (φ (wser wq)) = φ (G W PowerSeries.X (wser wq)) := by
    simp only [G, map_add (f := _), map_sub, map_mul, map_pow, AlgHom.commutes]
  rw [this, G_wser h, map_zero]

end PI.AddIntG.Wk
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.DXEqDerivative
section
noncomputable section

open Classical

namespace PI.AddIntG.Wk

variable {p : ℕ} [Fact p.Prime]

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative (R := ℂ_[p]) f := by
  ext n
  simp only [dX, PowerSeries.coeff_mk, PowerSeries.coeff_derivative]
  ring

theorem omega_mul_Gv {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (h : IsWq W wq) :
    omegaW W wq * Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq) = -1 := by
  have hw1 := wq_const h
  have hder := dX_eq_derivative wq
  have h' : wq = 1 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) * wq + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 * wq +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq ^ 2 + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 4 * wq ^ 2 +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 6 * wq ^ 3 := h
  have hD := congrArg (PowerSeries.derivative (R := ℂ_[p])) h'
  simp only [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    PowerSeries.derivative_X, Derivation.map_one_eq_zero, smul_eq_mul, nsmul_eq_mul] at hD
  have hQ : PowerSeries.constantCoeff
      (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2)) ≠ 0 := by
    have h2 : PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := by
      rw [show (2 : PowerSeries ℂ_[p]) = 1 + 1 by norm_num, map_add (f := _), map_one]
      norm_num
    simp [hw1, h2]
  have key : (-(2 : PowerSeries ℂ_[p]) * wq - (PowerSeries.X : PowerSeries ℂ_[p]) * PowerSeries.derivative (R := ℂ_[p]) wq) *
      (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 + 2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) +
        2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) + 3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) ^ 2 - 1) =
      -(wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2)) := by
    linear_combination (PowerSeries.X : PowerSeries ℂ_[p]) * hD
  calc omegaW W wq * Gv W (PowerSeries.X : PowerSeries ℂ_[p]) (wser wq)
      = ((-(2 : PowerSeries ℂ_[p]) * wq - (PowerSeries.X : PowerSeries ℂ_[p]) * PowerSeries.derivative (R := ℂ_[p]) wq) *
        (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₂ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 + 2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) +
          2 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₄ * (PowerSeries.X : PowerSeries ℂ_[p]) * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) + 3 * algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₆ * ((PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq) ^ 2 - 1)) *
        (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * (PowerSeries.X : PowerSeries ℂ_[p]) + algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * (PowerSeries.X : PowerSeries ℂ_[p]) ^ 3 * wq - 2))⁻¹ := by
        simp only [omegaW, Gv, wser, hder]
        ring
    _ = -1 := by
        rw [key, neg_mul, PowerSeries.mul_inv_cancel _ hQ]

end PI.AddIntG.Wk
end
end

