module

public import Formalism.HermitianCurvature.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0004
public import Formalism.LatticeRigidity.StatementC
public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0003

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AntidiagMulDiagonal
section
namespace Formalism.FourierDecayAlt.P.K

open Matrix Finset Real Formalism.FourierDecayAlt.K

variable {K : Type} [Field K] {n : ℕ}

theorem jointTheoremA : JointTheoremA := by
  intro C₀ hC₀
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.coarseBound
  refine ⟨2 * C₀, C, ?_⟩
  intro Kx Θ f r e σ hKx hf hΘ hr he hσ hrec
  have hΘ1 : 1 ≤ Θ := by linarith
  have hΘpos : 0 < Θ := by linarith
  have ha0 : 0 ≤ C₀ / Θ := div_nonneg (by linarith) hΘpos.le
  have hq : C₀ / Θ ≤ 1 / 2 := by
    rw [div_le_iff₀ hΘpos]
    linarith
  have ha : (C₀ / Θ) ^ f ≤ 1 / 2 := by
    calc (C₀ / Θ) ^ f ≤ (C₀ / Θ) ^ 1 := pow_le_pow_of_le_one ha0 (by linarith) hf
      _ ≤ 1 / 2 := by rw [pow_one]; exact hq
  have hrp : Θ ^ (-(Kx - 5 / 2)) ≤ Θ⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hΘ1 (by linarith)
  have hε0 : 0 ≤ C₀ * Θ ^ (-(Kx - 5 / 2)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hΘpos.le _)
  have hεa : (C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f ≤ (C₀ / Θ) ^ f := by
    apply pow_le_pow_left₀ hε0
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hrp (by linarith)
  exact hC r ((C₀ / Θ) ^ f) ((C₀ * Θ ^ (-(Kx - 5 / 2))) ^ f) e σ (pow_nonneg ha0 _) ha
    (pow_nonneg hε0 _) hεa hr he hσ hrec

end Formalism.FourierDecayAlt.P.K

theorem Formalism.FourierDecayAlt.P.joint_theorem_A' : Formalism.FourierDecayAlt.K.JointTheoremA := Formalism.FourierDecayAlt.P.K.jointTheoremA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
section
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials

open Finset Polynomial Formalism.FourierDecayAlt.F7

lemma chebPt_eq (α β : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    Formalism.SA.C.chebPt α β n j = (α + β) / 2 + (β - α) / 2 * Chebyshev.node n j := by
  simp only [Formalism.SA.C.chebPt, Chebyshev.node, mul_comm Real.pi]

lemma lagCo_affine {d : ℕ} (c h : ℝ) (x : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    lagCo (fun i => c + h * x i) j = (h⁻¹) ^ d * lagCo x j := by
  unfold lagCo
  have : ∀ i ∈ univ.erase j, ((c + h * x j) - (c + h * x i))⁻¹ = h⁻¹ * (x j - x i)⁻¹ := by
    intro i _
    rw [← mul_inv]; congr 1; ring
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ j)]
  simp

noncomputable def nd (n : ℕ) (j : Fin (n + 1)) : ℝ := Chebyshev.node n j

lemma nd_injective (n : ℕ) : Function.Injective (nd n) := by
  intro i j hij
  have := (Chebyshev.strictAntiOn_node n).injOn
    (Finset.mem_coe.mpr (Finset.mem_range.mpr i.isLt)) (Finset.mem_coe.mpr (Finset.mem_range.mpr j.isLt)) hij
  exact Fin.ext this

lemma U_mul_sin_node (m : ℕ) (j : ℕ) :
    (Chebyshev.U ℝ (m:ℤ)).eval (Chebyshev.node (m + 1) j) * Real.sin (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = 0 := by
  unfold Chebyshev.node
  rw [Chebyshev.U_real_cos]
  have : (((m:ℤ):ℝ) + 1) * (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = j * Real.pi := by
    push_cast; field_simp
  rw [this]
  exact Real.sin_nat_mul_pi j

lemma nodal_eq (m : ℕ) :
    (X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ) = C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1)) := by
  have h2 : ((2:ℝ) ^ m) ≠ 0 := by positivity
  have hmon : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (R := ℝ) (1:ℝ) (n := 2) (by norm_num)
    simpa using this
  have hdX : (X ^ 2 - 1 : ℝ[X]).degree = 2 := by
    have := degree_X_pow_sub_C (R := ℝ) (n := 2) (by norm_num) (1:ℝ)
    simpa using this
  have hdL : ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, hdX, Chebyshev.degree_U_natCast]
    norm_cast; ring_nf
  have hdR : (C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1))).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_C_mul h2, Lagrange.degree_nodal, card_univ, Fintype.card_fin]
  apply Polynomial.eq_of_degree_le_of_eval_index_eq univ (v := nd (m + 1))
    ((nd_injective (m + 1)).injOn)
  · rw [hdL, card_univ, Fintype.card_fin]
  · exact hdL.trans hdR.symm
  · rw [leadingCoeff_mul, hmon.leadingCoeff, Chebyshev.leadingCoeff_U_natCast, leadingCoeff_mul,
        leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff]; ring
  · intro i _
    rw [eval_mul, eval_mul, Lagrange.eval_nodal_at_node (mem_univ i), mul_zero]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    have h := U_mul_sin_node m i
    have hs : (nd (m + 1) i) ^ 2 - 1 = - Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ)) ^ 2 := by
      have := Real.sin_sq_add_cos_sq ((i:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ))
      unfold nd Chebyshev.node
      linarith
    rw [hs]
    unfold nd
    linear_combination (- Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ))) * h

lemma deriv_eq (m : ℕ) :
    derivative ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)) =
      ((m:ℝ[X]) + 1) * Chebyshev.T ℝ ((m:ℤ) + 1) + X * Chebyshev.U ℝ (m:ℤ) := by
  have h := Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℝ) (m:ℤ)
  rw [derivative_mul]
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, map_ofNat]
  push_cast at h
  linear_combination -h

lemma node_mul_U (m : ℕ) (j : Fin (m + 2)) :
    nd (m + 1) j * (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) =
      if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (-1) ^ (j:ℕ) * ((m:ℝ) + 1) else 0 := by
  by_cases h0 : (j:ℕ) = 0
  · have : nd (m + 1) j = 1 := by unfold nd; rw [h0]; exact Chebyshev.node_eq_one
    rw [this, if_pos (Or.inl h0), h0, Chebyshev.U_eval_one]; simp
  by_cases h1 : (j:ℕ) = m + 1
  · have : nd (m + 1) j = -1 := by unfold nd; rw [h1]; exact Chebyshev.node_eq_neg_one (by omega)
    rw [this, if_pos (Or.inr h1), h1, Chebyshev.U_eval_neg_one, Int.cast_negOnePow]
    push_cast
    rw [zpow_natCast, pow_succ]; ring
  · rw [if_neg (by tauto)]
    have h := U_mul_sin_node m j
    have hpos : 0 < Real.sin ((j:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ)) := by
      have hj : (0:ℝ) < (j:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hjm : ((j:ℕ):ℝ) < ((m + 1 : ℕ) : ℝ) := by
        have := j.isLt
        exact_mod_cast (by omega : (j:ℕ) < m + 1)
      have hm : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := Real.pi_pos; positivity
      · rw [div_lt_iff₀ hm, mul_comm]
        exact mul_lt_mul_of_pos_left hjm Real.pi_pos
    have : (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hpos.ne'
    rw [this, mul_zero]

lemma prod_node (m : ℕ) (j : Fin (m + 2)) :
    (2:ℝ) ^ m * ∏ i ∈ univ.erase j, (nd (m + 1) j - nd (m + 1) i) =
      (-1) ^ (j:ℕ) * ((m:ℝ) + 1) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 2 else 1) := by
  have h1 := congrArg (fun p => eval (nd (m + 1) j) (derivative p)) (nodal_eq m)
  simp only [deriv_eq, derivative_C_mul, eval_mul, eval_C, eval_add, eval_X, eval_natCast, eval_one,
    Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ j), Lagrange.eval_nodal] at h1
  rw [← h1, node_mul_U]
  have hT : (Chebyshev.T ℝ ((m:ℤ) + 1)).eval (nd (m + 1) j) = (-1) ^ (j:ℕ) := by
    have := Chebyshev.eval_T_real_node (n := m + 1) (i := j) (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt))
    push_cast at this
    exact this
  rw [hT]
  split_ifs <;> ring

lemma lagCo_nd (m : ℕ) (j : Fin (m + 2)) :
    lagCo (nd (m + 1)) j =
      (-1) ^ (j:ℕ) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 1 / 2 else 1) * ((2:ℝ) ^ m / ((m:ℝ) + 1)) := by
  have h := prod_node m j
  unfold lagCo
  rw [prod_inv_distrib]
  have h2 : (2:ℝ) ^ m ≠ 0 := by positivity
  have hm : (m:ℝ) + 1 ≠ 0 := by positivity
  have hs : ((-1:ℝ) ^ (j:ℕ)) * ((-1:ℝ) ^ (j:ℕ)) = 1 := by
    rw [← mul_pow]; simp
  have hs0 : ((-1:ℝ) ^ (j:ℕ)) ≠ 0 := by positivity
  have hP : ∏ i ∈ univ.erase j, (nd (m + 1) j - nd (m + 1) i) =
      (-1) ^ (j:ℕ) * ((m:ℝ) + 1) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 2 else 1) / (2:ℝ) ^ m := by
    rw [← h]; field_simp
  rw [hP]
  split_ifs
  · field_simp; linear_combination -hs
  · field_simp; linear_combination -hs

theorem coValue : Formalism.FourierDecayAlt.F7.ChebCoValue := by
  intro α β n hαβ hn j
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd : 0 < β - α := by linarith
  have e : Formalism.SA.C.chebPt α β (m + 1) = fun i => (α + β) / 2 + (β - α) / 2 * nd (m + 1) i := by
    funext i; exact chebPt_eq α β (m + 1) i
  rw [e, lagCo_affine, lagCo_nd]
  have : ((β - α) / 2)⁻¹ = 2 / (β - α) := by rw [inv_div]
  rw [this, Nat.add_sub_cancel]
  push_cast
  ring

lemma sum_half (m : ℕ) :
    ∑ j : Fin (m + 2), (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = (m:ℝ) + 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have : ∀ i : Fin m, (if ((i.castSucc.succ : Fin (m + 2)) : ℕ) = 0 ∨
      ((i.castSucc.succ : Fin (m + 2)) : ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = 1 := by
    intro i
    rw [if_neg]
    have := i.isLt
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  rw [sum_congr rfl (fun i _ => this i)]
  simp
  ring

theorem sharp : Formalism.FourierDecayAlt.F7.ChebSharp := by
  intro α β n hαβ hn
  have hd : 0 < β - α := by linarith
  constructor
  · intro i j hij
    rw [chebPt_eq, chebPt_eq] at hij
    have h2 : Chebyshev.node n i = Chebyshev.node n j := by
      have : (β - α) / 2 * Chebyshev.node n i = (β - α) / 2 * Chebyshev.node n j := by linarith
      exact mul_left_cancel₀ (by positivity) this
    exact nd_injective n h2
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hv : ∀ j : Fin (m + 2), |lagCo (Formalism.SA.C.chebPt α β (m + 1)) j| =
        (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) *
          (((2 : ℝ) ^ m / ((m:ℝ) + 1)) * (2 / (β - α)) ^ (m + 1)) := by
      intro j
      rw [coValue α β (m + 1) hαβ hn j, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, Nat.add_sub_cancel]
      have h1 : |(if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1)| =
          (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) := by
        apply abs_of_nonneg; split_ifs <;> norm_num
      rw [h1, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      push_cast; ring
    rw [sum_congr rfl (fun j _ => hv j), ← sum_mul, sum_half]
    have hm : (m:ℝ) + 1 ≠ 0 := by positivity
    rw [show (4:ℝ) / (β - α) = 2 * (2 / (β - α)) by ring, mul_pow, pow_succ (2:ℝ) m]
    field_simp

lemma sum_lagCo_mul_pow {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (k : ℕ)
    (hk : k ≤ d) : ∑ j, lagCo y j * y j ^ k = if k = d then 1 else 0 := by
  have hlt : ((X : ℝ[X]) ^ k).degree < (univ : Finset (Fin (d + 1))).card := by
    rw [degree_X_pow, card_univ, Fintype.card_fin]; exact_mod_cast Nat.lt_succ_of_le hk
  have h := Lagrange.coeff_eq_sum (s := univ) (v := y) hy.injOn hlt
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, coeff_X_pow, eval_pow, eval_X] at h
  have e : (if k = d then (1:ℝ) else 0) = if d = k then 1 else 0 := by
    by_cases hkd : k = d
    · subst hkd; simp
    · rw [if_neg hkd, if_neg (Ne.symm hkd)]
  rw [e, h]
  refine sum_congr rfl fun i _ => ?_
  unfold lagCo
  rw [prod_inv_distrib, div_eq_mul_inv, mul_comm]

lemma lead_complex {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ} (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) (a : Fin (d + 1) → V) :
    a (Fin.last d) = ∑ j, ((lagCo y j : ℝ) : ℂ) • ∑ k : Fin (d + 1), ((y j : ℂ) ^ (k : ℕ)) • a k := by
  simp_rw [smul_sum, smul_smul]
  rw [sum_comm]
  simp_rw [← sum_smul]
  have : ∀ k : Fin (d + 1), (∑ j, ((lagCo y j : ℝ) : ℂ) * (y j : ℂ) ^ (k:ℕ)) =
      if k = Fin.last d then 1 else 0 := by
    intro k
    have h := sum_lagCo_mul_pow y hy k (Nat.lt_succ_iff.mp k.isLt)
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    push_cast at h'
    rw [h']
    by_cases hk : k = Fin.last d
    · subst hk; simp
    · have hk' : ¬ ((k:ℕ) = d) := fun h0 => hk (Fin.ext (by simpa using h0))
      rw [if_neg hk, if_neg hk']; simp
  simp_rw [this]
  simp

end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials

namespace Formalism.FourierDecayAlt.P

theorem chebyshev_bound_sharp : Formalism.FourierDecayAlt.F7.ChebSharp := ChebyshevExtremalPolynomials.sharp

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FderivDecomp
section
open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

def wZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - I * fderiv ℝ f ζ I)

def wZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I)

def Hh (TT : ℝ) : Set ℂ := {w | TT < Complex.normSq (Complex.exp w)}

theorem normSq_exp (w : ℂ) : Complex.normSq (Complex.exp w) = Real.exp w.re ^ 2 := by

  first
    | rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    | simp [Complex.normSq_eq_norm_sq, Complex.norm_exp]

theorem isOpen_Hh (TT : ℝ) : IsOpen (Hh TT) := isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)

theorem convex_Hh (TT : ℝ) : Convex ℝ (Hh TT) := by

  intro w1 h1 w2 h2 a b ha hb hab
  simp only [Hh, Set.mem_setOf_eq, normSq_exp] at h1 h2 ⊢
  have hre : (a • w1 + b • w2).re = a * w1.re + b * w2.re := by simp
  rw [hre]
  rcases le_total w1.re w2.re with h | h
  · calc TT < Real.exp w1.re ^ 2 := h1
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w1.re = b * (w2.re - w1.re) := by
          rw [show a = 1 - b by linarith]; ring
        have : w1.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
        gcongr
  · calc TT < Real.exp w2.re ^ 2 := h2
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w2.re = a * (w1.re - w2.re) := by
          rw [show b = 1 - a by linarith]; ring
        have : w2.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg ha (sub_nonneg.2 h)]
        gcongr

def bet (α : ℂ → ℂ) (w : ℂ) : ℂ := α (Complex.exp w) * Complex.exp w

def omL : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

theorem omL_apply (c v : ℂ) : omL c v = 2 * (c * v).im := by

  simp [omL]

def om (α : ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ := omL (bet α w)

theorem om_apply (α : ℂ → ℂ) (w v : ℂ) : om α w v = 2 * (bet α w * v).im := omL_apply _ _

theorem bet_periodic (α : ℂ → ℂ) (w : ℂ) (k : ℤ) : bet α (w + (k : ℂ) * (2 * Real.pi * I)) = bet α w := by

  simp only [bet, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothDecayOfWeighted
section
open MeasureTheory Module
open scoped Nat

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC.Fou

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def au (j : ℕ) : ℝ := j ! * j ! * 4 ^ j

theorem au_nonneg (j : ℕ) : 0 ≤ au j := by
  unfold au
  positivity

theorem contDiff_u (n : ℕ∞) : ContDiff ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) :=
  (contDiff_const.add (contDiff_norm_sq ℝ)).inv (fun y => by positivity)

theorem norm_iteratedFDeriv_w_le (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * au i * au (n - i)) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
  refine (norm_iteratedFDeriv_mul_le (N := (n : ℕ∞)) (contDiff_u n) (contDiff_u n) x le_rfl).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := norm_iteratedFDeriv_u_le (V := V) i x
  have h2 := norm_iteratedFDeriv_u_le (V := V) (n - i) x
  have hq : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x‖ *
        ‖iteratedFDeriv ℝ (n - i) (fun y : V => (1 + ‖y‖ ^ 2)⁻¹) x‖
      ≤ (n.choose i : ℝ) * (au i * (1 + ‖x‖ ^ 2)⁻¹) * (au (n - i) * (1 + ‖x‖ ^ 2)⁻¹) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (au_nonneg i) hq))
    _ = (n.choose i : ℝ) * au i * au (n - i) * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring

theorem inv_sq_le (x : V) : (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ ≤ 4 * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have ht0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have hA : (0 : ℝ) < (1 + ‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) := by positivity
  have hB : (0 : ℝ) < (1 + ‖x‖) ^ 4 := by positivity
  have hr : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg h1.le]
    norm_cast
  have h2 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖x‖)]
  have h3 : ((1 + ‖x‖) ^ 2) ^ 2 ≤ (2 * (1 + ‖x‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [hr, ← mul_inv, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ hA hB]
  nlinarith [h3]

theorem decay_of_weight {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ ∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hEb 0 (Nat.zero_le _) 0)
  have hDw : D = fun x => ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) • E x := by
    funext x
    rw [hDE x, smul_smul]
    have hq : (1 + ‖x‖ ^ 2) ≠ 0 := by positivity
    field_simp
    simp
  have hwc : ContDiff ℝ m (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) :=
    (contDiff_u m).mul (contDiff_u m)
  refine ⟨hDw ▸ hwc.smul hE, ?_⟩
  set Kw : ℕ → ℝ := fun i => ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * au l * au (i - l) with hKw
  have hKw0 : ∀ i, 0 ≤ Kw i := fun i =>
    Finset.sum_nonneg fun l _ => mul_nonneg (mul_nonneg (by positivity) (au_nonneg _)) (au_nonneg _)
  set Cn : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Kw i * B with hCn
  have hCn0 : ∀ n, 0 ≤ Cn n := fun n =>
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (by positivity) (hKw0 i)) hB
  refine ⟨4 * ∑ n ∈ Finset.range (m + 1), Cn n, fun j hj x => ?_⟩
  have hq0 : 0 ≤ (1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹ := by positivity
  have hstep : ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by
    rw [hDw]
    refine (norm_iteratedFDeriv_smul_le (N := (j : ℕ∞)) (hwc.of_le (by exact_mod_cast hj))
      (hE.of_le (by exact_mod_cast hj)) x le_rfl).trans ?_
    rw [hCn, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : V => (1 + ‖y‖ ^ 2)⁻¹ * (1 + ‖y‖ ^ 2)⁻¹) x‖ *
          ‖iteratedFDeriv ℝ (j - i) E x‖
        ≤ (j.choose i : ℝ) * (Kw i * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹)) * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_w_le i x) (Nat.cast_nonneg _))
            (hEb (j - i) (by omega) x) (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hKw0 i) hq0))
      _ = (j.choose i : ℝ) * Kw i * B * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := by ring
  have hsum : Cn j ≤ ∑ n ∈ Finset.range (m + 1), Cn n :=
    Finset.single_le_sum (fun n _ => hCn0 n) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  calc ‖iteratedFDeriv ℝ j D x‖ ≤ Cn j * ((1 + ‖x‖ ^ 2)⁻¹ * (1 + ‖x‖ ^ 2)⁻¹) := hstep
    _ ≤ (∑ n ∈ Finset.range (m + 1), Cn n) * (4 * (1 + ‖x‖) ^ (-(4 : ℝ))) :=
        mul_le_mul hsum (inv_sq_le x) hq0 (Finset.sum_nonneg fun n _ => hCn0 n)
    _ = 4 * (∑ n ∈ Finset.range (m + 1), Cn n) * (1 + ‖x‖) ^ (-(4 : ℝ)) := by ring

theorem smooth_decay_of_weighted [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (hV : finrank ℝ V ≤ 3)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {D E : V → W} {m : ℕ}
    (hE : ContDiff ℝ m E) (B : ℝ) (hEb : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j E x‖ ≤ B)
    (hDE : ∀ x, E x = ((1 + ‖x‖ ^ 2) ^ 2 : ℝ) • D x) :
    ContDiff ℝ m D ∧ (∃ C, ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j D x‖ ≤ C * (1 + ‖x‖) ^ (-(4 : ℝ))) ∧
      ∀ j, 1 ≤ j → j ≤ m → Integrable (iteratedFDeriv ℝ j D) ∧ ∫ x, iteratedFDeriv ℝ j D x = 0 := by
  obtain ⟨hD, C, hC⟩ := decay_of_weight hE B hEb hDE
  refine ⟨hD, ⟨C, hC⟩, fun j hj1 hjm => integral_iteratedFDeriv_eq_zero hD C (fun i hi x => ?_) j hj1 hjm⟩
  refine (hC i hi x).trans ?_
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0)
    exact nonneg_of_mul_nonneg_left h (by positivity)
  gcongr
  · linarith [norm_nonneg x]
  · have : (finrank ℝ V : ℝ) ≤ 3 := by exact_mod_cast hV
    linarith

end Formalism.FourierDecayAlt.P5.HerC.Fou
end
end

