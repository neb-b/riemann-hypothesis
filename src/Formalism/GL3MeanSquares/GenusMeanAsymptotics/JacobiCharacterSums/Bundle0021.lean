module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0002
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0014
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0016
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0005

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTBAsm
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet


set_option maxHeartbeats 400000 in
theorem psi_relative_far_range : PsiRelBOf := by
  intro hE hS hZS cA hcA
  obtain ⟨κ, hκ, hκ', hZ⟩ := hZS
  obtain ⟨C, hC, hEx⟩ := hE κ hκ hκ'
  obtain ⟨cz, Az, Cz, hcz, hZ⟩ := hZ C 12 (by norm_num)
  obtain ⟨C₀, B, hC₀, hB, hnum⟩ := num_main cA κ C hcA hκ hC
  obtain ⟨c₁, hc₁, heta⟩ := etaOf_lower 1 one_pos
  refine ⟨min cz (cA ^ 2), 22 * |Az| + B / c₁, max Cz C₀, lt_min hcz (by positivity), ?_⟩
  intro M _ h8 y hy hr1 hr2
  have hM8 : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hM8r : (8 : ℝ) ≤ M := by exact_mod_cast hM8
  have hM3 : 3 ≤ M := by omega
  have hM0 : (0 : ℝ) < M := by linarith
  have hy0 : 0 < y := by linarith
  have hT8 : (8 : ℝ) ≤ (M : ℝ) ^ (12 : ℝ) := by
    calc (8 : ℝ) ≤ (M : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hM8r
      _ ≤ (M : ℝ) ^ (12 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hδ0 : 0 < ((M : ℝ) ^ 5)⁻¹ := by positivity
  have hδ : ((M : ℝ) ^ 5)⁻¹ ≤ 1 / 2 := by
    rw [one_div]
    apply inv_anti₀ (by norm_num)
    calc (2 : ℝ) ≤ (M : ℝ) ^ 1 := by rw [pow_one]; linarith
      _ ≤ (M : ℝ) ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  choose Z m K h1 h2 h3 h4 h5 h6 using fun χ => hEx M χ ((M : ℝ) ^ (12 : ℝ)) hM3 (by linarith)
  have hl : 1 ≤ Real.log M := one_le_log_of_three_le (by linarith)
  have hll : 1 ≤ Real.log (Real.log M + 2) := one_le_log_of_three_le (by linarith)
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hrz : Cz * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : Cz ≤ max Cz C₀ := le_max_left _ _
    gcongr
  have hrn : C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y := by
    refine le_trans ?_ hr1
    have : C₀ ≤ max Cz C₀ := le_max_right _ _
    gcongr
  have hZS := hZ M Z m h8 h1 h3 h4 h5 y hy hrz
  have hN := hnum M y hM8r hy hrn hr2
  generalize hTdef : (M : ℝ) ^ (12 : ℝ) = T at *
  generalize hδdef : ((M : ℝ) ^ 5)⁻¹ = δ at *
  generalize htdef : y ^ (-(κ / 2)) = t at *
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = C * (((M : ℝ) * T) ^ C * t
      + Real.log (2 * y) * Real.log ((M : ℝ) * T) ^ 2 / T) := ⟨_, rfl⟩
  rw [← hEdef] at hN
  have hT0 : 0 < T := by linarith
  have ht0 : 0 ≤ t := by rw [← htdef]; positivity
  have hlg : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have hre : ∀ χ, ∀ ρ ∈ Z χ, 1 / 2 ≤ ρ.re ∧ ρ.re < 1 := by
    intro χ ρ hρ
    obtain ⟨hz, hlo, -⟩ := h1 χ ρ hρ
    refine ⟨by linarith, ?_⟩
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hz.1 (not_lt.1 hcon) hz.2
  have hEu : ∀ u : ℝ, y ≤ u → u ≤ 2 * y →
      C * (((M : ℝ) * T) ^ C * u ^ (-(κ / 2)) + Real.log u * Real.log ((M : ℝ) * T) ^ 2 / T) ≤ E := by
    intro u hu1 hu2
    rw [hEdef]
    have a1 : u ^ (-(κ / 2)) ≤ t := by
      rw [← htdef]; exact Real.rpow_le_rpow_of_nonpos hy0 hu1 (by linarith)
    have a2 : Real.log u ≤ Real.log (2 * y) := Real.log_le_log (by linarith) hu2
    gcongr
  have hsharp : ∀ χ : DirichletCharacter ℂ M,
      ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0) + ∑ ρ ∈ Z χ, (m χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤
      4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) := by
    intro χ
    refine hS M χ (Z χ) (m χ) (K χ) E y δ (hre χ) hy hδ0 hδ ?_
    intro u hu
    have hu1 : y ≤ u := by
      rcases hu with rfl | rfl
      · exact le_rfl
      · nlinarith
    have hu2 : u ≤ 2 * y := by
      rcases hu with rfl | rfl
      · linarith
      · nlinarith
    exact (h6 χ u (by linarith)).trans (hEu u hu1 hu2)
  obtain ⟨W, hW⟩ : ∃ W : DirichletCharacter ℂ M → ℝ, W = fun χ =>
      ∑ ρ ∈ Z χ, ((m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ)) * y ^ (ρ.re - 1) := ⟨_, rfl⟩
  have hW0 : ∀ χ, 0 ≤ W χ := by
    intro χ
    rw [hW]
    apply Finset.sum_nonneg
    intro ρ hρ
    have : ((excW (eOf M) χ ρ : ℕ) : ℝ) ≤ (m χ ρ : ℝ) := by
      exact_mod_cast (excW_le_one (eOf M) χ ρ).trans (h3 χ ρ hρ)
    have h0 : (0 : ℝ) ≤ (m χ ρ : ℝ) - (excW (eOf M) χ ρ : ℝ) := by linarith
    positivity
  have hmW : ∀ χ, ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1) ≤ W χ + excI (eOf M) χ := by
    intro χ
    have := sum_excW_le (eOf M) χ (Z χ) y (by linarith) (fun ρ hρ => (hre χ ρ hρ).2)
    have e : ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        = W χ + ∑ ρ ∈ Z χ, (excW (eOf M) χ ρ : ℝ) * y ^ (ρ.re - 1) := by
      rw [hW, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    linarith
  have hper : ∀ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * W χ
        + excI (eOf M) χ * (20 * δ * y + 2 * y * t) := by
    intro χ
    have a := one_char hM3 (eOf M) (fun p hp => eOf_exc M p hp) χ (Z χ) (m χ) y κ T _ (by linarith)
      hT0.le (h2 χ) (fun ρ hρ => (hre χ ρ hρ).1) (h3 χ) (hsharp χ)
    rw [htdef] at a
    have a' : ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
        4 * y * E / δ + 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        + 4 * (δ * y + 1) * Real.log (2 * y) + 2 * y * W χ + excI (eOf M) χ * (2 * y * t) := by
      rw [hW]; exact a
    have b : 20 * δ * y * ∑ ρ ∈ Z χ, (m χ ρ : ℝ) * y ^ (ρ.re - 1)
        ≤ 20 * δ * y * (W χ + excI (eOf M) χ) := mul_le_mul_of_nonneg_left (hmW χ) (by positivity)
    have c : 20 * δ * y * W χ ≤ 20 * y * W χ := by
      have : 0 ≤ y * W χ := mul_nonneg hy0.le (hW0 χ)
      nlinarith
    linarith
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y)) + 22 * y * ∑ χ, W χ
        + (20 * δ * y + 2 * y * t) := by
    refine (Finset.sum_le_sum (fun χ _ => hper χ)).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    have q0 : 0 ≤ 4 * y * E / δ + 4 * (δ * y + 1) * Real.log (2 * y) := by positivity
    have q1 : 0 ≤ 20 * δ * y + 2 * y * t := by positivity
    have r1 := mul_le_mul_of_nonneg_right (card_char_le M) q0
    have r2 := mul_le_mul_of_nonneg_right (sum_excI_le (eOf M)) q1
    linarith
  have hη0 : 0 < etaOf M := etaOf_pos M (by omega)
  have hex := inv_le_exp hcA (lt_min hcz (by positivity : 0 < cA ^ 2)) (min_le_right _ _) hM8r hy hr2
  have hηM : (M : ℝ)⁻¹ ≤ etaOf M / c₁ := by
    have := heta M hM3
    rw [Real.rpow_neg_one] at this
    rw [le_div_iff₀ hc₁]; linarith
  have hMi : 0 < (M : ℝ)⁻¹ := by positivity
  have hWs : ∑ χ, W χ ≤ |Az| * etaOf M * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
    rw [hW]
    refine hZS.trans ?_
    have e1 : Real.exp (-(cz * Real.log y / Real.log M))
        ≤ Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) := by
      apply Real.exp_le_exp.2
      apply neg_le_neg
      have : min cz (cA ^ 2) ≤ cz := min_le_left _ _
      gcongr
    have e2 : Az ≤ |Az| := le_abs_self _
    gcongr
  have hfin : B * y * ((M : ℝ)⁻¹ * (M : ℝ)⁻¹)
      ≤ B * y * (etaOf M / c₁ * Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M))) := by
    gcongr
  generalize Real.exp (-(min cz (cA ^ 2) * Real.log y / Real.log M)) = ex at *
  have f1 : 22 * y * ∑ χ, W χ ≤ 22 * y * (|Az| * etaOf M * ex) :=
    mul_le_mul_of_nonneg_left hWs (by positivity)
  have f2 : (22 * |Az| + B / c₁) * y * etaOf M * ex
      = 22 * y * (|Az| * etaOf M * ex) + B * y * (etaOf M / c₁ * ex) := by ring
  rw [f2]
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHDom
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation

lemma dhDom_hasSum {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (k : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    HasSum (fun n ↦ term (logMul^[k] (↗ψ * ↗Λ)) s n)
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD ψ) s) := by
  have habs : abscissaOfAbsConv (↗ψ * ↗Λ) < s.re := by
    refine lt_of_le_of_lt (abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) ?_) ?_
    · intro y hy
      exact LSeriesSummable_twist_vonMangoldt ψ hy
    · exact_mod_cast hs
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : negLD ψ =ᶠ[nhds s] LSeries (↗ψ * ↗Λ) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hU : LFunction ψ =ᶠ[nhds z] LSeries (↗ψ) := by
      filter_upwards [hopen.mem_nhds hz'] with w hw
      exact DirichletCharacter.LFunction_eq_LSeries ψ hw
    simp only [negLD]
    rw [Filter.EventuallyEq.deriv_eq hU, DirichletCharacter.LFunction_eq_LSeries ψ hz',
      LSeries_twist_vonMangoldt_eq ψ hz', neg_div]
  have hit : iteratedDeriv k (negLD ψ) s = iteratedDeriv k (LSeries (↗ψ * ↗Λ)) s := by
    simp only [← iteratedDerivWithin_univ]
    refine Filter.EventuallyEq.iteratedDerivWithin_eq ?_ hev.eq_of_nhds
    simpa [nhdsWithin_univ] using hev
  rw [hit, LSeries_iteratedDeriv k habs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  exact (LSeriesSummable_of_abscissaOfAbsConv_lt_re
    (by simpa using habs)).LSeriesHasSum

private theorem logMul_iterate_apply_eq_log_pow_mul (f : ℕ → ℂ) (k n : ℕ) :
    logMul^[k] f n = Complex.log n ^ k * f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', logMul, ih]
    ring

lemma dhDom_term_le {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h1 : χ₁ ^ 2 = 1)
    (k : ℕ) (σ γ : ℝ) (n : ℕ) :
    ‖term (logMul^[k] (↗χ * ↗Λ)) ((σ : ℂ) + γ * I) n
      + term (logMul^[k] (↗(χ * χ₁) * ↗Λ)) ((σ : ℂ) + γ * I) n‖ ≤
    (term (logMul^[k] (↗(1 : DirichletCharacter ℂ q) * ↗Λ)) (σ : ℂ) n).re
      + (term (logMul^[k] (↗χ₁ * ↗Λ)) (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set A : ℝ := Real.log n ^ k * Λ n with hA
  have hA0 : 0 ≤ A :=
    mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k) ArithmeticFunction.vonMangoldt_nonneg
  have e1 : ∀ c : ℂ, Complex.log n ^ k * (c * ((Λ n : ℝ) : ℂ)) = (A : ℂ) * c := by
    intro c
    rw [hA, ← Complex.natCast_log]
    push_cast
    ring
  have hN : ‖(n : ℂ) ^ ((σ : ℂ) + γ * I)‖ = (n : ℝ) ^ σ := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have hR : (n : ℂ) ^ (σ : ℂ) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_cpow hnpos.le]
  have hp : 0 < (n : ℝ) ^ σ := Real.rpow_pos_of_pos hnpos σ
  have hre : ∀ c : ℝ, ((A : ℂ) * (c : ℂ) / (((n : ℝ) ^ σ : ℝ) : ℂ)).re = A * c / (n : ℝ) ^ σ := by
    intro c
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [term_of_ne_zero hn, logMul_iterate_apply_eq_log_pow_mul, Pi.mul_apply, MulChar.coeToFun_mul, e1, hR]
  by_cases hu : IsUnit (n : ZMod q)
  · obtain ⟨u, hu'⟩ := hu
    rw [← hu', MulChar.one_apply_coe]
    have hχ : ‖χ u‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
    have h1u : χ₁ u * χ₁ u = 1 := by
      rw [← pow_two, ← MulChar.pow_apply_coe, h1, MulChar.one_apply_coe]
    rcases mul_self_eq_one_iff.mp h1u with h | h
    · rw [h]
      have := hre 1
      push_cast at this
      rw [this]
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * 1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = ((2 * A : ℝ) : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) := by
        push_cast
        ring
      rw [e2, norm_div, norm_mul, hχ, hN, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      apply le_of_eq
      ring
    · rw [h]
      have := hre 1
      have h' := hre (-1)
      push_cast at this h'
      rw [this, h']
      have e2 : (A : ℂ) * χ u / (n : ℂ) ^ ((σ : ℂ) + γ * I) + (A : ℂ) * (χ u * -1) /
          (n : ℂ) ^ ((σ : ℂ) + γ * I) = 0 := by
        ring
      rw [e2, norm_zero]
      apply le_of_eq
      ring
  · simp [MulChar.map_nonunit _ hu]

theorem deuring_heilbronn_dominant : DHDom := by
  intro M _ χ₁ χ γ σ k h1 hσ
  have hs : 1 < ((σ : ℂ) + γ * I).re := by simpa using hσ
  have hs0 : 1 < (σ : ℂ).re := by simpa using hσ
  have hA := dhDom_hasSum χ k hs
  have hB := dhDom_hasSum (χ * χ₁) k hs
  have hC := dhDom_hasSum (1 : DirichletCharacter ℂ M) k hs0
  have hD := dhDom_hasSum χ₁ k hs0
  have hbound := HasSum.norm_le_of_bounded (hA.add hB) (Complex.hasSum_re (hC.add hD))
    (fun n ↦ by
      rw [Complex.add_re]
      exact dhDom_term_le χ₁ χ h1 k σ γ n)
  have e1 : ‖iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
      + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ =
      ‖(-1 : ℂ) ^ k * iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
        + (-1 : ℂ) ^ k * iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I)‖ := by
    rw [← mul_add, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [e1, mul_add]
  exact hbound

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHIneqB
section
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem dhReBound (A P S : ℂ) (E : ℝ) (h : ‖A - P + S‖ ≤ E) : S.re ≤ P.re - A.re + E := by
  have h1 : (A - P + S).re ≤ ‖A - P + S‖ := by
    first
      | exact Complex.re_le_norm _
      | exact Complex.re_le_abs _
  simp only [Complex.add_re, Complex.sub_re] at h1
  linarith

theorem logMulAbsAddTwoLeTwoMulLog (M : ℕ) (T t : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (ht : |t| ≤ T) :
    Real.log ((M : ℝ) * (|t| + 2)) ≤ 2 * Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hta := abs_nonneg t
  have hpos : 0 < (M : ℝ) * (|t| + 2) := by positivity
  have h1 : (M : ℝ) * (|t| + 2) ≤ (M : ℝ) * (T + 2) := by nlinarith
  have h2 : (M : ℝ) * (T + 2) ≤ ((M : ℝ) * T) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ) - 3) (by linarith : (0 : ℝ) ≤ T - 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (M : ℝ)) (by linarith : (0 : ℝ) ≤ T - 2)]
  calc Real.log ((M : ℝ) * (|t| + 2)) ≤ Real.log (((M : ℝ) * T) ^ 2) :=
        Real.log_le_log hpos (h1.trans h2)
    _ = 2 * Real.log ((M : ℝ) * T) := by rw [Real.log_pow]; norm_num

theorem dhLogOne (M : ℕ) (T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log ((M : ℝ) * T) := by
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : (6 : ℝ) ≤ M * T := by nlinarith
  have he := Real.exp_one_lt_d9
  have h1 : Real.exp 1 ≤ (M : ℝ) * T := by linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) h1

theorem dhPair (η γ β₁ : ℝ) (hη : 0 < η) (hβ1 : β₁ < 1) (k : ℕ) (s : ℂ)
    (hs : s = ((1 + η : ℝ) : ℂ) + γ * I) :
    (1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)).re ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
  have hδ : 0 < 1 - β₁ := by linarith
  have hare : (s - 1).re = η := by rw [hs]; simp
  have hbre : (s - β₁).re = η + (1 - β₁) := by rw [hs]; simp; ring
  have hna : η ≤ ‖s - 1‖ := hare ▸ Complex.re_le_norm (s - 1)
  have hnb : η ≤ ‖s - β₁‖ := le_trans (by linarith) (hbre ▸ Complex.re_le_norm (s - β₁))
  have ha0 : s - 1 ≠ 0 := fun h => by rw [h, norm_zero] at hna; linarith
  have hb0 : s - β₁ ≠ 0 := fun h => by rw [h, norm_zero] at hnb; linarith
  have hba : (s - β₁) - (s - 1) = ((1 - β₁ : ℝ) : ℂ) := by push_cast; ring
  have hid : 1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1) =
      ((s - β₁) - (s - 1)) * (∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)) /
        ((s - 1) ^ (k + 1) * (s - β₁) ^ (k + 1)) := by
    rw [mul_comm ((s - β₁) - (s - 1)), geom_sum₂_mul]
    field_simp
  have hsum : ‖∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ ≤
      ((k + 1 : ℕ) : ℝ) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2)) := by
    calc _ ≤ ∑ i ∈ Finset.range (k + 1), ‖(s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (k + 1), ‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [norm_mul, norm_pow, norm_pow, le_div_iff₀ (by positivity)]
          have e1 : η ^ (k + 2) = η ^ (i + 1) * η ^ (k + 1 - i) := by rw [← pow_add]; congr 1; omega
          have e2 : ‖s - 1‖ ^ (k + 1) = ‖s - 1‖ ^ (k + 1 - 1 - i) * ‖s - 1‖ ^ (i + 1) := by
            rw [← pow_add]; congr 1; omega
          have e3 : ‖s - β₁‖ ^ (k + 1) = ‖s - β₁‖ ^ i * ‖s - β₁‖ ^ (k + 1 - i) := by
            rw [← pow_add]; congr 1; omega
          rw [e1, e2, e3]
          have p1 : η ^ (i + 1) ≤ ‖s - 1‖ ^ (i + 1) := pow_le_pow_left₀ hη.le hna _
          have p2 : η ^ (k + 1 - i) ≤ ‖s - β₁‖ ^ (k + 1 - i) := pow_le_pow_left₀ hη.le hnb _
          have p12 := mul_le_mul p1 p2 (by positivity) (by positivity)
          calc ‖s - β₁‖ ^ i * ‖s - 1‖ ^ (k + 1 - 1 - i) * (η ^ (i + 1) * η ^ (k + 1 - i))
              ≤ ‖s - β₁‖ ^ i * ‖s - 1‖ ^ (k + 1 - 1 - i) * (‖s - 1‖ ^ (i + 1) * ‖s - β₁‖ ^ (k + 1 - i)) :=
                mul_le_mul_of_nonneg_left p12 (by positivity)
            _ = _ := by ring
      _ = ((k + 1 : ℕ) : ℝ) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfinal : ‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ ≤ ((k : ℝ) + 1) * (1 - β₁) / η ^ (k + 2) := by
    rw [hid, norm_div, norm_mul, hba, Complex.norm_real, Real.norm_of_nonneg hδ.le, norm_mul, norm_pow, norm_pow]
    have hpos : 0 < ‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) := by
      have := norm_pos_iff.mpr ha0
      have := norm_pos_iff.mpr hb0
      positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have h3 := mul_le_mul_of_nonneg_left hsum hδ.le
    push_cast at h3
    calc (1 - β₁) * ‖∑ i ∈ Finset.range (k + 1), (s - β₁) ^ i * (s - 1) ^ (k + 1 - 1 - i)‖ * η ^ (k + 2)
        ≤ (1 - β₁) * (((k : ℝ) + 1) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1) / η ^ (k + 2))) * η ^ (k + 2) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ((k : ℝ) + 1) * (1 - β₁) * (‖s - 1‖ ^ (k + 1) * ‖s - β₁‖ ^ (k + 1)) := by
          field_simp
  have hre : (1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)).re ≤
      ‖1 / (s - 1) ^ (k + 1) - 1 / (s - β₁) ^ (k + 1)‖ := Complex.re_le_norm _
  exact hre.trans hfinal

theorem dhAssemble {β : Type*} [AddCommGroup β] (F1 F2 F3 F4 : Multiset ℂ) (b2 b3 b4 : ℂ)
    (c3 c4 : Prop) [Decidable c3] [Decidable c4] (h2 : b2 ∈ F2) (h3 : c3 → b3 ∈ F3) (h4 : c4 → b4 ∈ F4)
    (g : ℂ → β) :
    ((F1 + F2.erase b2 + (if c3 then F3.erase b3 else F3) + (if c4 then F4.erase b4 else F4)).map g).sum
      = (F1.map g).sum + (F2.map g).sum + (F3.map g).sum + (F4.map g).sum - g b2
        - (if c3 then g b3 else 0) - (if c4 then g b4 else 0) := by
  classical
  have e : ∀ (F : Multiset ℂ) (b : ℂ), b ∈ F → ((F.erase b).map g).sum = (F.map g).sum - g b := by
    intro F b hb
    rw [← Multiset.sum_map_erase hb]
    abel
  simp only [Multiset.map_add (f := _), Multiset.sum_add, e _ _ h2]
  by_cases hc3 : c3 <;> by_cases hc4 : c4
  · simp only [if_pos hc3, if_pos hc4, e _ _ (h3 hc3), e _ _ (h4 hc4)]
    abel
  · simp only [if_pos hc3, if_neg hc4, e _ _ (h3 hc3)]
    abel
  · simp only [if_neg hc3, if_pos hc4, e _ _ (h4 hc4)]
    abel
  · simp only [if_neg hc3, if_neg hc4]
    abel

theorem dhFam_re (Z : Finset ℂ) (m : ℂ → ℕ) (s x : ℂ) (η : ℝ) (hZ : ∀ ρ ∈ Z, ρ.re < 1)
    (hs : s.re = 1 + η) (hx : x ∈ dhFam Z m s) : η ≤ x.re := by
  unfold dhFam at hx
  rw [Multiset.mem_bind] at hx
  obtain ⟨ρ, hρ, hx⟩ := hx
  rw [Multiset.eq_of_mem_replicate hx, Complex.sub_re, hs]
  linarith [hZ ρ hρ]

theorem dhMemIte (F : Multiset ℂ) (c : Prop) [Decidable c] (b x : ℂ) (h : x ∈ (if c then F.erase b else F)) :
    x ∈ F := by
  split_ifs at h
  · exact Multiset.mem_of_mem_erase h
  · exact h

theorem dhFamPow (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (k : ℕ) :
    ((dhFam Z m s).map (fun x => 1 / x ^ (k + 1))).sum = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
  unfold dhFam
  rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun ρ _ => ?_
  simp [Multiset.map_replicate, Multiset.sum_replicate, div_eq_mul_inv]

theorem dhFinalArith (S1 S2 S3 S4 P1 P3 P4 A1 A2 A3 A4 E0 Eγ g2 I3 I4 X F G Hc H e8 : ℝ)
    (t1 : S1 + S2 + S3 + S4 ≤ P1 - A1 + E0 + (0 - A2 + E0) + (P3 - A3 + Eγ) + (P4 - A4 + Eγ))
    (hA : 0 ≤ A1 + A2 + A3 + A4) (hp : P1 - g2 ≤ X) (hs : P3 + P4 - I3 - I4 ≤ X + e8)
    (h0 : E0 ≤ F) (hγ : Eγ ≤ F) (t3 : F ≤ 2 * G) (t2 : e8 ≤ H) (nn : 0 ≤ Hc) :
    S1 + S2 + S3 + S4 - g2 - I3 - I4 ≤ 2 * X + (8 * G + 8 * Hc + H) := by
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TuranPowerSumBound
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem turan_power_sum_bound : DHTuran2 := by
  refine ⟨1600, 1, by norm_num, le_rfl, fun n m z hn hz hz1 => ?_⟩
  obtain ⟨k, h1, h2, h3⟩ := T2.turan2Main n m z hn hz hz1
  exact ⟨k, h1, by simpa using h2, by simpa using h3⟩

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

