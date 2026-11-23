module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0002

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem rad_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) : 0 ≤ ρ * (1 / 2 : ℝ) ^ n := by positivity

theorem filt_ball {A C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hA1 : ∀ x : L, ‖x‖ ≤ A * ‖Phi K L x‖) (hA : 0 ≤ A)
    (hC1 : ∀ x y : L, ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖)
    (hAρ : A * ρ < 1) (hCρ : C * ρ ≤ 1 / 2) :
    Filt (L ≃ₐ[K] L) (fun n => ball (K := K) (L := L) (ρ * (1 / 2 : ℝ) ^ n) (rad_nonneg hρ n)) (proj1 (K := K) (L := L)) := by
  refine {
    anti := ?_
    mul := ?_
    smul := ?_
    comp := ?_
    sep := ?_
    inv := ?_
    e_mem := ?_
    e_sum := ?_ }
  · intro n x hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ (n + 1) at hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    refine hx.trans ?_
    rw [pow_succ]
    nlinarith [rad_nonneg hρ n]
  · intro n x y hx hy
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n at hx
    change ‖Phi K L y‖ ≤ ρ * (1 / 2 : ℝ) ^ 0 at hy
    change ‖Phi K L (x * y)‖ ≤ ρ * (1 / 2 : ℝ) ^ (n + 1)
    rw [pow_zero, mul_one] at hy
    calc ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖ := hC1 x y
      _ ≤ C * (ρ * (1 / 2 : ℝ) ^ n) * ρ := by gcongr
      _ = (C * ρ) * (ρ * (1 / 2 : ℝ) ^ n) := by ring
      _ ≤ (1 / 2) * (ρ * (1 / 2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_right hCρ (rad_nonneg hρ n)
      _ = ρ * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  · intro n g x hx
    exact (norm_Phi_map g x).trans hx
  · intro x hx
    have hx' : ∀ k, ‖Phi K L (x k)‖ ≤ ρ * (1 / 2 : ℝ) ^ k := fun k => by
      exact hx k
    have hsum : Summable fun k => Phi K L (x k) :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ρ) hx'
    refine ⟨(Phi K L).symm (∑' k, Phi K L (x k)), fun n => ?_⟩
    change ‖Phi K L ((Phi K L).symm (∑' k, Phi K L (x k)) - ∑ k ∈ range n, x k)‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, map_sum,
      ← hsum.sum_add_tsum_nat_add n, add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (rad_nonneg hρ n) fun k => ?_
    refine (hx' (k + n)).trans ?_
    gcongr ρ * ?_
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left n k)
  · intro x hx
    have hx' : ∀ n, ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n := hx
    have hlim : Filter.Tendsto (fun n : ℕ => ρ * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (ρ * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul ρ
    have h0 : ‖Phi K L x‖ ≤ ρ * 0 := ge_of_tendsto' hlim hx'
    rw [mul_zero] at h0
    have := norm_le_zero_iff.1 h0
    simpa using this
  · intro n x hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n at hx
    change ‖Phi K L ((1 + x)⁻¹ - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    have hr : ρ * (1 / 2 : ℝ) ^ n ≤ ρ := by
      have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hxlt : ‖x‖ < 1 := by
      refine lt_of_le_of_lt ((hA1 x).trans ?_) hAρ
      gcongr
      exact hx.trans hr
    have hne : 1 + x ≠ 0 := by
      intro h0
      have : x = -1 := by linear_combination h0
      rw [this, norm_neg, norm_one] at hxlt
      exact lt_irrefl _ hxlt
    set y : L := (1 + x)⁻¹ - 1 with hy
    have hy1 : y = -x + -(x * y) := by
      rw [hy]; field_simp; ring
    have h1 : ‖Phi K L y‖ ≤ max ‖Phi K L x‖ ‖Phi K L (x * y)‖ := by
      conv_lhs => rw [hy1, map_add (f := _), map_neg, map_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, norm_neg]
    have h2 : ‖Phi K L (x * y)‖ ≤ (1 / 2) * ‖Phi K L y‖ := by
      refine (hC1 x y).trans ?_
      gcongr
      refine le_trans ?_ hCρ
      gcongr
      exact hx.trans hr
    rcases le_max_iff.1 h1 with h3 | h3
    · exact h3.trans hx
    · have : ‖Phi K L y‖ ≤ 0 := by linarith
      exact this.trans (rad_nonneg hρ n)
  · intro n x hx
    classical
    have hbound : ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1)‖ ≤ ‖Phi K L x‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro τ
      show ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1) τ‖ ≤ _
      rw [map_smul, Pi.smul_apply]
      have h : Phi K L (IsGalois.normalBasis K L 1) τ = if 1 = τ then 1 else 0 :=
        Module.Basis.equivFun_self _ _ _
      rw [h, smul_eq_mul]
      split_ifs
      · rw [mul_one]
        exact norm_le_pi_norm _ _
      · rw [mul_zero, norm_zero]
        exact norm_nonneg _
    exact hbound.trans (by change ‖Phi K L x‖ ≤ _; exact hx)
  · intro x
    calc ∑ σ : L ≃ₐ[K] L, σ • proj1 (K := K) (L := L) (σ⁻¹ • x)
        = ∑ σ : L ≃ₐ[K] L, Phi K L x σ • σ (IsGalois.normalBasis K L 1) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          show σ (Phi K L (σ⁻¹ • x) 1 • IsGalois.normalBasis K L 1) = _
          rw [map_smul]
          congr 1
          have h := Phi_map (σ⁻¹) x (1 : L ≃ₐ[K] L)
          simpa [inv_inv] using h
      _ = x := by
        rw [← Phi_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem exists_units_subgroup [IsUltrametricDist L] : ∃ S : Subgroup Lˣ,
    (∀ (σ : L ≃ₐ[K] L) (u v : Lˣ), u ∈ S → (v : L) = σ u → v ∈ S) ∧
    (∀ u ∈ S, ‖(u : L)‖ = 1) ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ u : Lˣ, ‖(u : L) - 1‖ < ε → u ∈ S) ∧
    (∀ u ∈ S, (∀ σ : L ≃ₐ[K] L, σ (u : L) = u) → ∃ v ∈ S, ∏ σ : L ≃ₐ[K] L, σ (v : L) = u) ∧
    ∀ σ₀ : L ≃ₐ[K] L, (∀ σ, σ ∈ Subgroup.zpowers σ₀) → ∀ u ∈ S, ∏ σ : L ≃ₐ[K] L, σ (u : L) = 1 →
      ∃ v ∈ S, σ₀ (v : L) = u * v := by
  obtain ⟨A, B, C, hA, hB, hC, hA1, hB1, hC1⟩ := exists_consts (K := K) (L := L)
  set ρ : ℝ := (2 * (C + A + 1))⁻¹ with hρdef
  have hpos : 0 < 2 * (C + A + 1) := by positivity
  have hρ : 0 < ρ := inv_pos.2 hpos
  have hρ1 : ρ * (2 * (C + A + 1)) = 1 := inv_mul_cancel₀ hpos.ne'
  have hAρ : A * ρ < 1 := by nlinarith [mul_nonneg hC hρ.le, mul_nonneg hA hρ.le]
  have hCρ : C * ρ ≤ 1 / 2 := by nlinarith [mul_nonneg hC hρ.le, mul_nonneg hA hρ.le]
  have F := filt_ball hC hρ.le hA1 hA hC1 hAρ hCρ
  refine ⟨F.V 0, fun σ u v hu hv => ?_, fun u hu => ?_, ⟨ρ / (B + 1), by positivity, fun u hu => ?_⟩,
    fun u hu hfix => F.norm_surj u hu hfix, fun σ₀ hσ₀ u hu hN => F.hilbert90_matrix_subalgebra_norm_one σ₀ hσ₀ u hu hN⟩
  · have : v = act σ u := Units.ext hv
    rw [this]
    exact F.act_mem σ hu
  · have hu' : ‖Phi K L ((u : L) - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ 0 := hu
    rw [pow_zero, mul_one] at hu'
    have hlt : ‖(u : L) - 1‖ < 1 := by
      refine lt_of_le_of_lt ((hA1 _).trans ?_) hAρ
      gcongr
    have h1 : (u : L) = 1 + ((u : L) - 1) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'), norm_one]
    exact max_eq_left hlt.le
  · show ‖Phi K L ((u : L) - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ 0
    rw [pow_zero, mul_one]
    refine (hB1 _).trans ?_
    have h2 : B * ‖(u : L) - 1‖ ≤ (B + 1) * (ρ / (B + 1)) := by
      gcongr
      · linarith
    refine h2.trans (le_of_eq ?_)
    field_simp

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
