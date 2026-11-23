module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModCMPoint
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_sq (d : ℕ) : 4 * omegaK d ^ 2 = 4 * omegaK d - (1 + d) := by
  have hs : (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    push_cast
    ring
  unfold omegaK
  linear_combination hs

theorem omegaK_lin {d : ℕ} (hd : 0 < d) {t n : ℤ} (h : (t : ℂ) * omegaK d + n = 0) :
    t = 0 ∧ n = 0 := by
  have h2 : (t : ℂ) * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) + 2 * n = 0 := by
    rw [omegaK] at h
    linear_combination 2 * h
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h3 : (((t : ℝ) + 2 * n : ℝ) : ℂ) + (((t : ℝ) * Real.sqrt d : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination h2
  have him : (t : ℝ) * Real.sqrt d = 0 := by
    have := congrArg Complex.im h3
    simpa using this
  have hre : (t : ℝ) + 2 * n = 0 := by
    have := congrArg Complex.re h3
    simpa using this
  have ht : (t : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hsq.ne'
  have hn : (n : ℝ) = 0 := by linarith
  exact ⟨by exact_mod_cast ht, by exact_mod_cast hn⟩

theorem cmPoint {d : ℕ} (hd : 0 < d) {L : PeriodPair} (hL : HasCMBy d L) {c : ℂ} {τ : ℍ}
    (h : IsTauOf L c τ) (x y : ℤ) :
    ∃ A B C D : ℤ, ((x : ℂ) + y * omegaK d) * τ = A * τ + B ∧ (x : ℂ) + y * omegaK d = C * τ + D ∧
      4 * (A * D - B * C) = 4 * x ^ 2 + 4 * x * y + y ^ 2 * (1 + d) := by
  obtain ⟨hc, hmem⟩ := h
  have hmul : ∀ w ∈ L.lattice, ((x : ℂ) + y * omegaK d) * w ∈ L.lattice := by
    intro w hw
    have h1 : (x : ℂ) * w ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem hw x
    have h2 : (y : ℂ) * (omegaK d * w) ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem (hL w hw) y
    have e : ((x : ℂ) + y * omegaK d) * w = (x : ℂ) * w + (y : ℂ) * (omegaK d * w) := by ring
    rw [e]
    exact add_mem h1 h2
  have hcτ : c * (τ : ℂ) ∈ L.lattice := (hmem _).2 ⟨1, 0, by push_cast; ring⟩
  have hc1 : c ∈ L.lattice := (hmem _).2 ⟨0, 1, by push_cast; ring⟩
  obtain ⟨A, B, hAB⟩ := (hmem _).1 (hmul _ hcτ)
  obtain ⟨C, D, hCD⟩ := (hmem _).1 (hmul _ hc1)
  have e1 : ((x : ℂ) + y * omegaK d) * τ = A * τ + B := by
    apply mul_left_cancel₀ hc
    linear_combination hAB
  have e2 : (x : ℂ) + y * omegaK d = C * τ + D := by
    apply mul_left_cancel₀ hc
    linear_combination hCD
  refine ⟨A, B, C, D, e1, e2, ?_⟩

  have key : ((x : ℂ) + y * omegaK d - A) * ((x : ℂ) + y * omegaK d - D) = B * C := by
    linear_combination ((x : ℂ) + y * omegaK d - A) * e2 + (C : ℂ) * e1
  have hω := omegaK_sq d
  obtain ⟨ht, hn⟩ := omegaK_lin hd (t := 8 * x * y + 4 * y ^ 2 - 4 * (A + D) * y)
    (n := 4 * x ^ 2 - y ^ 2 * (1 + d) - 4 * (A + D) * x + 4 * (A * D - B * C)) (by
      push_cast
      linear_combination 4 * key - (y : ℂ) ^ 2 * hω)
  by_cases hy : y = 0
  · subst hy
    simp only [Int.cast_zero, zero_mul, add_zero] at e1 e2
    have hτ : 0 < (τ : ℂ).im := τ.im_pos
    have e2' : (x : ℂ) - D = (C : ℂ) * τ := by linear_combination e2
    have e1' : ((x : ℂ) - A) * τ = (B : ℂ) := by linear_combination e1
    have hC : C = 0 := by
      have := congrArg Complex.im e2'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re] at this
      have h0 : (C : ℝ) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 hτ.ne'
    have hA : A = x := by
      have := congrArg Complex.im e1'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
        Complex.sub_re] at this
      have h0 : ((x : ℝ) - A) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · have : (A : ℝ) = x := by linarith
        exact_mod_cast this
      · exact absurd h0 hτ.ne'
    subst hC hA
    have hD : D = A := by
      have : ((A : ℤ) : ℂ) = D := by linear_combination e2'
      exact_mod_cast this.symm
    subst hD
    ring
  · have h4 : 4 * (y * (2 * x + y - (A + D))) = 0 := by linear_combination ht
    have hs : 2 * x + y - (A + D) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left (by norm_num))).resolve_left hy
    linear_combination hn - 4 * x * hs

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEisInt
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

private theorem hasSum_sigma_mul_qParam_pow_modularForm_E {k : ℕ} (hk : 3 ≤ k) (hke : Even k) (C : ℂ)
    (hC : (riemannZeta k)⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ k / ((k - 1).factorial : ℂ) = C)
    (τ : ℍ) :
    HasSum (fun m : ℕ => (if m = 0 then (1 : ℂ) else C * (ArithmeticFunction.sigma (k - 1) m : ℂ)) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (ModularForm.E hk τ) := by
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqe : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ) = q := by
    simp [hqdef, Function.Periodic.qParam]
  have hq : ‖q‖ < 1 := by
    rw [hqdef, Function.Periodic.norm_qParam]
    refine (Real.exp_lt_exp.mpr ?_).trans_eq Real.exp_zero
    have := τ.im_pos
    have := Real.pi_pos
    simp only [UpperHalfPlane.coe_im, div_one]
    nlinarith
  have hσ : ∀ n : ℕ, ‖((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n‖ ≤ (n : ℝ) ^ k * ‖q‖ ^ n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    rw [ArithmeticFunction.sigma_apply]
    push_cast
    calc ∑ d ∈ n.divisors, (d : ℝ) ^ (k - 1) ≤ ∑ d ∈ n.divisors, (n : ℝ) ^ (k - 1) :=
          Finset.sum_le_sum fun d hd => pow_le_pow_left₀ (by positivity)
            (by exact_mod_cast Nat.divisor_le hd) _
      _ = (n.divisors.card : ℝ) * (n : ℝ) ^ (k - 1) := by simp
      _ ≤ (n : ℝ) * (n : ℝ) ^ (k - 1) := by
          gcongr
          exact_mod_cast Nat.card_divisors_le_self n
      _ = (n : ℝ) ^ k := by
          rw [← pow_succ']
          congr 1
          omega
  have hsum : Summable fun n : ℕ => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n :=
    Summable.of_norm_bounded (summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hq)) hσ
  have hsum1 : Summable fun n : ℕ =>
      ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  have hE := EisensteinSeries.q_expansion_riemannZeta hk hke τ
  rw [hE, hC, hqe]
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, if_true, mul_one,
    add_sub_cancel_left, Nat.add_eq_zero, one_ne_zero, and_false, if_false]
  have ht : ∑' n : ℕ+, ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ (n : ℕ) =
      ∑' n : ℕ, ((ArithmeticFunction.sigma (k - 1) (n + 1) : ℕ) : ℂ) * q ^ (n + 1) :=
    tsum_pnat_eq_tsum_succ (f := fun n => ((ArithmeticFunction.sigma (k - 1) n : ℕ) : ℂ) * q ^ n)
  convert hsum1.hasSum.mul_left C using 1 <;>
    first
    | rfl
    | (funext n <;> ring)
    | (congr 1 <;> (rw [← ht]; apply tsum_congr; intro n; simp))

theorem map_eisensteinFourInt : e4Z.map (Int.castRingHom ℂ) = qExpansion 1 E₄ := by
  have hE : E₄ = ModularForm.E (k := 4) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₄) (h := 1)
    (c := fun m => PowerSeries.coeff m (e4Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hC : (riemannZeta ((4 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 4 /
      (((4 - 1).factorial : ℕ) : ℂ) = 240 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
    have hI : Complex.I ^ 4 = 1 := Complex.I_pow_four
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 4) (by norm_num) (by decide) 240 hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e4Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem map_eisensteinSixInt : e6Z.map (Int.castRingHom ℂ) = qExpansion 1 E₆ := by
  have hE : E₆ = ModularForm.E (k := 6) (by norm_num) := rfl
  ext m
  refine ModularFormClass.qExpansion_coeff_unique (f := E₆) (h := 1)
    (c := fun m => PowerSeries.coeff m (e6Z.map (Int.castRingHom ℂ))) one_pos (by simp) ?_ m
  intro τ
  have hb6 : bernoulli 6 = 1 / 42 := by
    have h5 : bernoulli' 5 = 0 := by
      rw [bernoulli'_def]
      norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
        bernoulli'_three, bernoulli'_four, Nat.choose]
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
    norm_num [Finset.sum_range_succ, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
      bernoulli'_three, bernoulli'_four, h5, Nat.choose]
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 6 / 945 := by
    have h6 := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show ((6 : ℕ) : ℂ) = 2 * ((3 : ℕ) : ℂ) by norm_num, h6, hb6]
    norm_num [Nat.factorial]
    ring
  have hC : (riemannZeta ((6 : ℕ) : ℂ))⁻¹ * (-2 * (Real.pi : ℂ) * Complex.I) ^ 6 /
      (((6 - 1).factorial : ℕ) : ℂ) = -504 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [hz6]
    have hI : Complex.I ^ 6 = -1 := by
      rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]
      norm_num
    simp only [Nat.factorial, Nat.succ_eq_add_one]
    field_simp
    ring_nf
    rw [hI]
    ring
  have h := hasSum_sigma_mul_qParam_pow_modularForm_E (k := 6) (by norm_num) (by decide) (-504) hC τ
  rw [hE]
  convert h using 2 with n
  simp only [e6Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

theorem aC_eq : aC = qExpansion 1 AA := by
  have h1 : AnalyticAt ℂ (cuspFunction 1 ⇑E₄) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos (by simp)
  have h2 : AnalyticAt ℂ (cuspFunction 1 (⇑E₄ * ⇑E₄)) 0 := by
    have h3 := ModularFormClass.analyticAt_cuspFunction_zero (E₄.mul E₄) one_pos (by simp)
    rwa [ModularForm.coe_mul] at h3
  have hA : AA = ⇑E₄ * (⇑E₄ * ⇑E₄) := by
    funext τ
    simp only [AA, Pi.mul_apply]
    ring
  rw [hA, qExpansion_mul h1 h2, qExpansion_mul h1 h1, ← map_eisensteinFourInt]
  simp only [aC, aZ, map_pow]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGEis
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def latMap {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) (v : Fin 2 → ℤ) : L.lattice :=
  ⟨c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)), (h.2 _).2 ⟨v 0, v 1, rfl⟩⟩

theorem latMap_bijective {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    Function.Bijective (latMap h) := by
  constructor
  · intro v w hvw
    have h1 : c * ((v 0 : ℂ) * (τ : ℂ) + (v 1 : ℂ)) = c * ((w 0 : ℂ) * (τ : ℂ) + (w 1 : ℂ)) :=
      congrArg Subtype.val hvw
    have h2 := mul_left_cancel₀ h.1 h1
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
      add_zero, Complex.add_re, Complex.mul_re, sub_zero] at him hre
    have hτ : (τ : ℂ).im ≠ 0 := τ.im_ne_zero
    have h0 : (v 0 : ℝ) = w 0 := mul_right_cancel₀ hτ him
    rw [h0] at hre
    have h1' : (v 1 : ℝ) = w 1 := add_left_cancel hre
    funext i
    fin_cases i
    · exact_mod_cast h0
    · exact_mod_cast h1'
  · rintro ⟨x, hx⟩
    obtain ⟨u, v, rfl⟩ := (h.2 x).1 hx
    exact ⟨![u, v], by simp [latMap]⟩

theorem G_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    L.G k = (c ^ k)⁻¹ * (2 * riemannZeta k) * E hk τ := by
  have hE : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := by
    rw [show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
      eisensteinSeriesSIF_apply 0 k τ, smul_eq_mul]
  have H := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h1 : L.G k = ∑' v : Fin 2 → ℤ, (c ^ k)⁻¹ * eisSummand k v τ := by
    rw [PeriodPair.G, ← (Equiv.ofBijective _ (latMap_bijective h)).tsum_eq]
    refine tsum_congr fun v => ?_
    simp [latMap, eisSummand, mul_pow, mul_comm]
  rw [h1, tsum_mul_left, H, hE]
  ring

theorem sixVal : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h5 : bernoulli' 5 = 0 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four]
    norm_num [Nat.choose]
  have h6 : bernoulli' 6 = 1 / 42 := by
    rw [bernoulli'_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
      bernoulli'_two, bernoulli'_three, bernoulli'_four, h5]
    norm_num [Nat.choose]
  have hB : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), h6]
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [Nat.factorial, hB] at h
  rw [h]
  ring

theorem g₂_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₂ = (c ^ 4)⁻¹ * (4 * (Real.pi : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [PeriodPair.g₂, G_eq h (k := 4) (by norm_num) ⟨2, rfl⟩,
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four]
  have hE : E (k := 4) (by norm_num) τ = E₄ τ := rfl
  rw [hE]
  ring

theorem g₃_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.g₃ = (c ^ 6)⁻¹ * (8 * (Real.pi : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [PeriodPair.g₃, G_eq h (k := 6) (by norm_num) ⟨3, rfl⟩,
    show ((6 : ℕ) : ℂ) = 6 by norm_num, sixVal]
  have hE : E (k := 6) (by norm_num) τ = E₆ τ := rfl
  rw [hE]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormNatCastClOfNotDvd
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Polynomial

variable (l : ℕ) [Fact l.Prime]

theorem norm_natCast_Cl (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← PadicComplex.norm_extends' l (n : ℚ_[l])]
  congr 1
  simp

theorem norm_sub_le_max_Cl (a b : ℂ_[l]) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ :=
  by simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_l_Cl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_Cl, Padic.norm_p]

theorem norm_natCast_Cl_of_not_dvd {n : ℕ} (hn : ¬ l ∣ n) : ‖(n : ℂ_[l])‖ = 1 := by
  rw [norm_natCast_Cl, Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hn

theorem muP_norm {ζ : ℂ_[l]} (hζ : ζ ∈ muP l) : ‖ζ‖ = 1 := by
  obtain ⟨n, hn, -, h⟩ := hζ
  have : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this

theorem tch_norm_le {ξ : ℂ_[l]} (hξ : ξ ∈ Tch l) : ‖ξ‖ ≤ 1 := by
  rcases hξ with rfl | h
  · simp
  · exact (muP_norm l h).le

theorem tch_mul {ξ ξ' : ℂ_[l]} (h : ξ ∈ Tch l) (h' : ξ' ∈ Tch l) : ξ * ξ' ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  · rw [zero_mul]; exact Set.mem_insert _ _
  rcases h' with rfl | ⟨m, hm, hlm, hζ'⟩
  · rw [mul_zero]; exact Set.mem_insert _ _
  refine Set.mem_insert_of_mem _ ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · intro hd
    rcases ((Fact.out : l.Prime).dvd_mul).1 hd with h1 | h1
    · exact hln h1
    · exact hlm h1
  · rw [mul_pow, pow_mul, hζ, one_pow, one_mul, mul_comm n m, pow_mul, hζ', one_pow]

theorem tch_inv {ξ : ℂ_[l]} (h : ξ ∈ Tch l) : ξ⁻¹ ∈ Tch l := by
  rcases h with rfl | ⟨n, hn, hln, hζ⟩
  · rw [inv_zero]; exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ ⟨n, hn, hln, by rw [inv_pow, hζ, inv_one]⟩

theorem tch_near (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (f : ℕ) (hf : 0 < f) (r : ℝ) (hr : r < 1)
    (h : ‖x ^ (l ^ f) - x‖ ≤ r) : ∃ ξ ∈ Tch l, ‖x - ξ‖ ≤ r := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hq : 2 ≤ l ^ f := le_trans hl (Nat.le_self_pow hf.ne' l)
  obtain ⟨m, hm⟩ : ∃ m, l ^ f = m + 1 := ⟨l ^ f - 1, by omega⟩
  have hm0 : 0 < m := by omega
  have hlm : ¬ l ∣ m := by
    intro hd
    have h1 : l ∣ m + 1 := hm ▸ dvd_pow_self l hf.ne'
    have h2 : l ∣ 1 := (Nat.dvd_add_right hd).1 h1
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h2)
  by_cases hsmall : ‖x‖ ≤ r
  · exact ⟨0, Set.mem_insert _ _, by simpa using hsmall⟩
  push Not at hsmall
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) h
  have hx1 : ‖x‖ = 1 := by
    have h1 : ‖x‖ ≤ max ‖x ^ (l ^ f)‖ ‖x ^ (l ^ f) - x‖ := by
      calc ‖x‖ = ‖x ^ (l ^ f) - (x ^ (l ^ f) - x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le_max_Cl l _ _
    have h2 : ‖x‖ ≤ ‖x‖ ^ (l ^ f) := by
      rw [← norm_pow]
      rcases le_max_iff.1 h1 with h3 | h3
      · exact h3
      · linarith
    by_contra hne
    have hlt : ‖x‖ < 1 := lt_of_le_of_ne hx hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_lt hr0 hsmall
    have := pow_lt_self_of_lt_one₀ hpos hlt (by omega : 1 < l ^ f)
    linarith
  have hxm : ‖x ^ m - 1‖ ≤ r := by
    have e : x ^ (l ^ f) - x = x * (x ^ m - 1) := by rw [hm]; ring
    rwa [e, norm_mul, hx1, one_mul] at h
  obtain ⟨ζ, hζroot, hζ⟩ := ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.exists_root_near l (X ^ m - C 1)
    (monic_X_pow_sub_C 1 hm0.ne') x
    (by simp only [eval_sub, eval_pow, eval_X, eval_C]; exact lt_of_le_of_lt hxm hr)
  have hζm : ζ ^ m = 1 := by
    have : ζ ^ m - 1 = 0 := by simpa using hζroot
    exact sub_eq_zero.1 this
  have hmu : ζ ∈ muP l := ⟨m, hm0, hlm, hζm⟩
  refine ⟨ζ, Set.mem_insert_of_mem _ hmu, ?_⟩
  have hζ1 : ‖ζ‖ = 1 := muP_norm l hmu
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have e1 : x - ζ = ζ * (x * ζ⁻¹ - 1) := by
    rw [mul_sub, mul_one, mul_comm x ζ⁻¹, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  have e2 : x ^ m - 1 = (∑ i ∈ Finset.range m, (x * ζ⁻¹) ^ i) * (x * ζ⁻¹ - 1) := by
    rw [geom_sum_mul, mul_pow, inv_pow, hζm, inv_one, mul_one]
  have hy : ‖x * ζ⁻¹ - 1‖ = ‖x - ζ‖ := by rw [e1, norm_mul, hζ1, one_mul]
  rw [e2, norm_mul, ReciprocityTheory.ChartRestriction.PadicPolynomialApproximation.norm_geom_sum_eq_one l (hy ▸ hζ)
    (norm_natCast_Cl_of_not_dvd l hlm), one_mul, hy] at hxm
  exact hxm

end ReciprocityTheory.ChartRestriction.L1
end
end

