module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpNormProductLeOne
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
namespace GlobalTheory.EisM

theorem locineq_log_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    T * ‖∑ i, z i‖ ^ 2 ≤ - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
  have hs : ∀ i j, HasSum (fun n : ℕ => (z i * conj (z j) * T) ^ n / n)
      (-Complex.log (1 - z i * conj (z j) * T)) := fun i j =>
    Complex.hasSum_taylorSeries_neg_log (h i j)
  have H := hasSum_sum (s := Finset.univ) (fun i _ => hasSum_sum (s := Finset.univ) (fun j _ => hs i j))
  have H2 := ((Complex.hasSum_iff _ _).mp H).1
  have hterm : ∀ n : ℕ, (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ)).re
      = T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n := by
    intro n
    have e : (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ))
        = (((T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n : ℝ)) : ℂ) := by
      have e1 : ∀ i j, (z i * conj (z j) * T) ^ n / (n : ℂ)
          = z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n) := by
        intro i j; rw [map_pow]; ring
      simp_rw [e1]
      have e2 : ∑ i, ∑ j, z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n)
          = (∑ i, z i ^ n) * conj (∑ j, z j ^ n) * ((T : ℂ) ^ n / n) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_mul]
      rw [e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [e, Complex.ofReal_re]
  have hre : (∑ i, ∑ j, -Complex.log (1 - z i * conj (z j) * T)).re
      = - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
    simp [Complex.re_sum, Complex.log_re]
  rw [hre] at H2
  simp_rw [hterm] at H2
  have := le_hasSum H2 1 (fun n _ => by positivity)
  simpa using this

theorem locineq_exp_prod {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    Real.exp (‖∑ i, z i‖ ^ 2 * T) * ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖ ≤ 1 := by
  have hpos : ∀ i j, 0 < ‖1 - z i * conj (z j) * T‖ := by
    intro i j
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun e => ?_)
    have := h i j
    rw [← e, norm_one] at this
    exact lt_irrefl _ this
  have hP : ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖
      = Real.exp (∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos i j)).symm
  rw [hP, ← Real.exp_add, Real.exp_le_one_iff]
  have := locineq_log_sum z T hT h
  linarith

theorem locineq : ∀ (x y : ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 →
    Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖(1 - x * T) * (1 - y * T)‖ ^ 2 *
      ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)) ≤ 1 := by
  intro x y T hT0 hT1 hx hy
  have hxT : ‖x‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg x) (norm_nonneg x))]
  have hyT : ‖y‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg y) (norm_nonneg y))]
  have hxy : ‖x‖ * ‖y‖ * T < 1 := by
    nlinarith [mul_nonneg (sq_nonneg (‖x‖ - ‖y‖)) hT0]
  let z : Fin 3 → ℂ := ![1, x, y]
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_of_nonneg hT0]
  have h : ∀ i j, ‖z i * conj (z j) * T‖ < 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [z, hnT, Complex.norm_conj, abs_of_nonneg hT0] <;> nlinarith
  have key := locineq_exp_prod z T hT0 h
  have c1 : ‖1 - conj x * T‖ = ‖1 - x * T‖ := by
    rw [← Complex.norm_conj (1 - x * T)]; simp
  have c2 : ‖1 - conj y * T‖ = ‖1 - y * T‖ := by
    rw [← Complex.norm_conj (1 - y * T)]; simp
  have c3 : ‖1 - y * conj x * T‖ = ‖1 - x * conj y * T‖ := by
    rw [← Complex.norm_conj (1 - x * conj y * T)]; simp; ring_nf
  have d0 : ‖1 - (T : ℂ)‖ = 1 - T := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dx : ‖1 - x * conj x * T‖ = 1 - ‖x‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dy : ‖1 - y * conj y * T‖ = 1 - ‖y‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  simp only [z, Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, mul_one] at key
  rw [c1, c2, c3, d0, dx, dy] at key
  rw [norm_mul]
  calc _ = Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖1 - x * T‖ * ‖1 - y * T‖ *
        (‖1 - x * T‖ * (1 - ‖x‖ ^ 2 * T) * ‖1 - x * conj y * T‖) *
        (‖1 - y * T‖ * ‖1 - x * conj y * T‖ * (1 - ‖y‖ ^ 2 * T))) := by ring
    _ ≤ 1 := key

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteSlTwoSmulMemFundamentalDomain
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem finite_smul_mem_fd : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  intro τ
  have hP : {p : Fin 2 → ℤ | ¬ (2 * τ.im < Complex.normSq ((p 0 : ℂ) * τ + p 1))}.Finite :=
    Filter.eventually_cofinite.1
      ((ModularGroup.tendsto_normSq_coprime_pair τ).eventually_gt_atTop (2 * τ.im))
  have hrow : ∀ p : Fin 2 → ℤ, {γ : SL(2, ℤ) | γ 1 = p ∧ |(γ • τ).re| ≤ 1 / 2}.Finite := by
    intro p
    by_cases hp : IsCoprime (p 0) (p 1)
    · have h := Filter.eventually_cofinite.1
        ((ModularGroup.tendsto_abs_re_smul τ hp).eventually_gt_atTop (1 / 2 : ℝ))
      refine (h.image Subtype.val).subset ?_
      rintro γ ⟨h1, h2⟩
      exact ⟨⟨γ, h1⟩, not_lt.2 h2, rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro γ ⟨h1, -⟩
      exact hp (h1 ▸ ModularGroup.bottom_row_coprime γ)
  refine (hP.biUnion fun p _ => hrow p).subset ?_
  intro γ hγ
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  have hpos := (γ • τ).im_pos
  have hhalf : (1 : ℝ) / 2 ≤ (γ • τ).im := by nlinarith
  rw [ModularGroup.im_smul_eq_div_normSq, le_div_iff₀ (Complex.normSq_pos.2 (denom_ne_zero _ _))] at hhalf
  rw [Set.mem_iUnion₂]
  refine ⟨γ 1, ?_, rfl, hγ.2⟩
  simp only [Set.mem_setOf_eq, not_lt]
  simp [UpperHalfPlane.denom] at hhalf ⊢
  linarith

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FirstDiff
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.TermDiff

lemma rpow_neg_sub_le {x y p : ℝ} (hx : 1/2 ≤ x) (hxy : x ≤ y) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    |x ^ (-p) - y ^ (-p)| ≤ 8 * (y - x) / y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  set r := x / y with hr
  have hr0 : 0 < r := div_pos hx0 hy0
  have hr1 : r ≤ 1 := (div_le_one hy0).2 hxy
  have hyr : y ^ (-p) = x ^ (-p) * r ^ p := by
    rw [hr, Real.div_rpow hx0.le hy0.le, Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
    have : 0 < x ^ p := Real.rpow_pos_of_pos hx0 p
    have : 0 < y ^ p := Real.rpow_pos_of_pos hy0 p
    field_simp
  have hrp1 : r ^ p ≤ 1 := Real.rpow_le_one hr0.le hr1 hp0
  have hrp2 : r ^ (2:ℝ) ≤ r ^ p := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hp2
  have hr2 : r ^ (2:ℝ) = r ^ 2 := Real.rpow_two r
  have hxp : x ^ (-p) ≤ 4 := by
    rw [Real.rpow_neg hx0.le, ← Real.inv_rpow hx0.le]
    have h1 : x⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hx0 (by norm_num)]; linarith
    calc x⁻¹ ^ p ≤ (2:ℝ) ^ p := Real.rpow_le_rpow (inv_nonneg.2 hx0.le) h1 hp0
      _ ≤ (2:ℝ) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 4 := by norm_num
  have hxp0 : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx0.le _
  rw [hyr]
  have e : x ^ (-p) - x ^ (-p) * r ^ p = x ^ (-p) * (1 - r ^ p) := by ring
  rw [e, abs_of_nonneg (mul_nonneg hxp0 (by linarith))]
  have h1r : 1 - r ^ p ≤ 2 * (1 - r) := by
    have : 1 - r^2 ≤ 2 * (1 - r) := by nlinarith [mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hr1)]
    rw [hr2] at hrp2
    linarith
  have h1r' : 1 - r = (y - x) / y := by rw [hr]; field_simp
  calc x ^ (-p) * (1 - r ^ p) ≤ 4 * (2 * (1 - r)) :=
        mul_le_mul hxp h1r (by linarith) (by norm_num)
    _ = 8 * (y - x) / y := by rw [h1r']; ring

lemma norm_pow_sub_pow_le (z w : ℂ) (n : ℕ) (M : ℝ) (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖w ^ (n+1) - z ^ (n+1)‖ ≤ (n+1) * M ^ n * ‖w - z‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  have hM : 0 ≤ M := (norm_nonneg z).trans hz
  calc ‖∑ i ∈ Finset.range (n+1), w ^ i * z ^ (n + 1 - 1 - i)‖
      ≤ ∑ i ∈ Finset.range (n+1), ‖w ^ i * z ^ (n + 1 - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), M ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖w‖ ^ i * ‖z‖ ^ (n + 1 - 1 - i) ≤ M ^ i * M ^ (n + 1 - 1 - i) := by gcongr
          _ = M ^ n := by rw [← pow_add]; congr 1; omega
    _ = (n+1) * M ^ n := by simp

lemma inv_pow_sub_le (j : ℕ) (z w : ℂ) (hz : 0 < ‖z‖) (hwz : ‖w - z‖ ≤ ‖z‖ / 2) :
    ‖(z ^ j)⁻¹ - (w ^ j)⁻¹‖ ≤ j * 4 ^ j * ‖w - z‖ / ‖z‖ ^ (j + 1) := by
  have hW1 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
    have := norm_sub_le w (w - z); simpa using this
  have hW2 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
    have := norm_add_le z (w - z); simpa using this
  have hWl : ‖z‖ / 2 ≤ ‖w‖ := by linarith
  have hW0 : 0 < ‖w‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz
  have hw0 : w ≠ 0 := norm_pos_iff.1 hW0
  cases j with
  | zero => simp
  | succ n =>
    rw [inv_sub_inv (pow_ne_zero _ hz0) (pow_ne_zero _ hw0), norm_div, norm_mul, norm_pow, norm_pow]
    have hM : ‖w‖ ≤ 2 * ‖z‖ := by linarith
    have hnum := norm_pow_sub_pow_le z w n (2 * ‖z‖) (by linarith) hM
    have hden : ‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1) ≤ ‖z‖ ^ (n+1) * ‖w‖ ^ (n+1) := by gcongr
    have hdpos : 0 < ‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1) := by positivity
    calc ‖w ^ (n+1) - z ^ (n+1)‖ / (‖z‖ ^ (n+1) * ‖w‖ ^ (n+1))
        ≤ ((n+1) * (2 * ‖z‖) ^ n * ‖w - z‖) / (‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1)) :=
          div_le_div₀ (by positivity) hnum hdpos hden
      _ = (n+1) * 2 ^ (2 * n + 1) * ‖w - z‖ / ‖z‖ ^ (n + 2) := by
          rw [div_pow, mul_pow]; field_simp; ring
      _ ≤ ((n+1 : ℕ) : ℝ) * 4 ^ (n+1) * ‖w - z‖ / ‖z‖ ^ (n + 1 + 1) := by
          push_cast
          gcongr
          calc (2:ℝ) ^ (2 * n + 1) ≤ 2 ^ (2 * n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 4 ^ (n+1) := by rw [show 2 * n + 2 = 2 * (n+1) by ring, pow_mul]; norm_num

theorem first_diff : ∀ j : ℕ, ∃ C : ℝ, ∀ (s : ℝ) (z a : ℂ), 0 ≤ s → s ≤ 1 → 1 ≤ ‖z‖ → 2 * ‖a‖ ≤ ‖z‖ → ‖trm j s z - trm j s (z + a)‖ ≤ C * ‖a‖ / ‖z‖ ^ (j + 1) := by
  intro j
  refine ⟨j * 4 ^ j + 8 * 2 ^ j, ?_⟩
  intro s z a hs0 hs1 hz ha
  have hZ : 0 < ‖z‖ := by linarith
  have hwz : (z + a) - z = a := by ring
  have hA : ‖(z + a) - z‖ ≤ ‖z‖ / 2 := by rw [hwz]; linarith
  have hW1 : ‖z‖ ≤ ‖z + a‖ + ‖a‖ := by
    have := norm_sub_le (z + a) a; simpa using this
  have hW2 : ‖z + a‖ ≤ ‖z‖ + ‖a‖ := norm_add_le z a
  have hWl : ‖z‖ / 2 ≤ ‖z + a‖ := by linarith
  have hW0 : 0 < ‖z + a‖ := by linarith
  have hv : ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
  have hdv : ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)‖ ≤ 8 * ‖a‖ / ‖z‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, neg_mul]
    rcases le_total ‖z‖ ‖z + a‖ with h | h
    · refine (rpow_neg_sub_le (by linarith) h (by linarith) (by linarith)).trans ?_
      rw [div_le_div_iff₀ hW0 hZ]
      nlinarith
    · rw [abs_sub_comm]
      refine (rpow_neg_sub_le (by linarith) h (by linarith) (by linarith)).trans ?_
      gcongr
      linarith
  have hu' : ‖((z + a) ^ j)⁻¹‖ ≤ 2 ^ j / ‖z‖ ^ j := by
    rw [norm_inv, norm_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 1 * ‖z‖ ^ j = 2 ^ j * (‖z‖ / 2) ^ j := by rw [div_pow]; field_simp
      _ ≤ 2 ^ j * ‖z + a‖ ^ j := by gcongr
  have hdu := inv_pow_sub_le j z (z + a) hZ hA
  rw [hwz] at hdu
  unfold trm
  have e : (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((z + a) ^ j)⁻¹ * ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)
      = ((z ^ j)⁻¹ - ((z + a) ^ j)⁻¹) * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)
        + ((z + a) ^ j)⁻¹ * (((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)) := by ring
  rw [e]
  calc _ ≤ ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹‖ * ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ)‖
        + ‖((z + a) ^ j)⁻¹‖ * ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)‖ :=
          norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (j * 4 ^ j * ‖a‖ / ‖z‖ ^ (j + 1)) * 1 + (2 ^ j / ‖z‖ ^ j) * (8 * ‖a‖ / ‖z‖) := by
          gcongr
    _ = (j * 4 ^ j + 8 * 2 ^ j) * ‖a‖ / ‖z‖ ^ (j + 1) := by
          field_simp; ring

end GlobalTheory.EisM.TermDiff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1CharElementary
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem qs_coef_of_mfc {k M : ℕ} [NeZero M] {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 M) (k : ℤ)] (f : F) : qs (coef f) = ⇑f := by
  funext τ
  have h := ModularForm.hasSum_qExpansion f one_pos (by simp) τ
  rw [qs, ← h.tsum_eq]
  congr 1
  funext n
  rw [coef, Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem polyB_of_isBigO {a : ℕ → ℂ} {k : ℕ}
    (h : (fun n => a n) =O[atTop] fun n : ℕ => (n : ℝ) ^ k) : PolyB a := by
  obtain ⟨c, hc⟩ := h.bound
  rw [eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  have hS : 0 ≤ ∑ n ∈ Finset.range N, ‖a n‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨|c| + ∑ n ∈ Finset.range N, ‖a n‖, k, fun n => ?_⟩
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ k := one_le_pow₀ (by linarith)
  by_cases hn : N ≤ n
  · have h2 := hN n hn
    rw [Real.norm_of_nonneg (by positivity)] at h2
    calc ‖a n‖ ≤ c * (n : ℝ) ^ k := h2
      _ ≤ |c| * ((n : ℝ) + 1) ^ k :=
          mul_le_mul (le_abs_self c) (pow_le_pow_left₀ hn0 (by linarith) k) (by positivity) (abs_nonneg c)
      _ ≤ (|c| + ∑ n ∈ Finset.range N, ‖a n‖) * ((n : ℝ) + 1) ^ k :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have h2 : ‖a n‖ ≤ ∑ n ∈ Finset.range N, ‖a n‖ :=
      Finset.single_le_sum (f := fun n => ‖a n‖) (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
    calc ‖a n‖ ≤ |c| + ∑ n ∈ Finset.range N, ‖a n‖ := by linarith [abs_nonneg c]
      _ ≤ (|c| + ∑ n ∈ Finset.range N, ‖a n‖) * ((n : ℝ) + 1) ^ k :=
          le_mul_of_one_le_right (by positivity) h1

theorem inv_of_hasChar {k M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) (hf : HasChar k χ f) :
    Inv k M (ch χ) f := by
  intro γ hγ τ
  have hmem : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hγ
  have h := congrFun (hf γ hmem) τ
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul] at h
  have hd : denom (γ : GL (Fin 2) ℝ) τ = ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
    simp [denom]
  have hne : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ τ
  rw [← hd, ch]
  rw [zpow_neg, zpow_natCast] at h
  have hk : denom (γ : GL (Fin 2) ℝ) τ ^ k ≠ 0 := pow_ne_zero _ hne
  field_simp at h
  rw [h]
  ring

theorem mf_of_mfc {k M : ℕ} [NeZero M] {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F (Gamma1 M) (k : ℤ)] (χ : DirichletCharacter ℂ M) (f : F) (hf : HasChar k χ f) :
    qs (coef f) = ⇑f ∧ MF k M (ch χ) (coef f) := by
  have hq := qs_coef_of_mfc (k := k) f
  refine ⟨hq, ?_, ?_⟩
  · have h := ModularFormClass.qExpansion_isBigO (Int.natCast_nonneg k) f
    simp only [strictWidthInfty_Gamma1, zpow_natCast] at h
    exact polyB_of_isBigO h
  · rw [hq]; exact inv_of_hasChar χ f hf

theorem gamma1_char_elementary : ∀ (k M : ℕ) (χ : DirichletCharacter ℂ M), 0 < M →
    (∀ f : ModularForm (Gamma1 M) (k : ℤ), HasChar k χ f → qs (coef f) = ⇑f ∧ MF k M (ch χ) (coef f)) ∧
    ∀ f : CuspForm (Gamma1 M) (k : ℤ), HasChar k χ f → qs (coef f) = ⇑f ∧ CF k M (ch χ) (coef f) := by
  intro k M χ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  refine ⟨fun f hf => mf_of_mfc χ f hf, fun f hf => ?_⟩
  obtain ⟨hq, hmf⟩ := mf_of_mfc χ f hf
  refine ⟨hq, hmf, ?_⟩
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f f
  refine ⟨C, fun τ => ?_⟩
  have h := hC τ
  rw [hq]
  simp only [petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real,
    zpow_natCast, norm_pow, Real.norm_of_nonneg τ.im_pos.le] at h
  calc ‖f τ‖ ^ 2 * τ.im ^ k = ‖f τ‖ * ‖f τ‖ * τ.im ^ k := by ring
    _ ≤ C := h

end GlobalTheory.EisM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Geofix
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix

namespace GlobalTheory.GeoFix

theorem geofix : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (k : ℕ) (o : Ω), IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T n), g o = o) → ∃ (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' ∧ Cong (p := p) k o x := by
  intro p _ Ω _ _ hc T n ψ h k o ho hfix

  let F : Subfield Ω :=
    { carrier := {y | ∃ (N : Ω) (D : O0 p), InR ψ N ∧ D ≠ 0 ∧ y * ψ D = N}
      zero_mem' := ⟨0, 1, inR_zero ψ, one_ne_zero, by simp⟩
      one_mem' := ⟨ψ 1, 1, inR_psi ψ 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro a b ⟨N, D, hN, hD, ha⟩ ⟨N', D', hN', hD', hb⟩
        exact ⟨N * ψ D' + N' * ψ D, D * D', inR_add (inR_mul hN (inR_psi ψ D')) (inR_mul hN' (inR_psi ψ D)),
          mul_ne_zero hD hD', by rw [map_mul, ← ha, ← hb]; ring⟩
      mul_mem' := by
        rintro a b ⟨N, D, hN, hD, ha⟩ ⟨N', D', hN', hD', hb⟩
        exact ⟨N * N', D * D', inR_mul hN hN', mul_ne_zero hD hD', by rw [map_mul, ← ha, ← hb]; ring⟩
      neg_mem' := by
        rintro a ⟨N, D, hN, hD, ha⟩
        exact ⟨-N, D, inR_neg hN, hD, by rw [neg_mul, ha]⟩
      inv_mem' := by
        rintro a ⟨N, D, hN, hD, ha⟩
        by_cases ha0 : a = 0
        · rw [ha0, inv_zero]
          exact ⟨0, 1, inR_zero ψ, one_ne_zero, by simp⟩
        · have hψD : ψ D ≠ 0 := fun h0 => hD (h.inj (by rw [h0, map_zero]))
          have hN0 : N ≠ 0 := by rw [← ha]; exact mul_ne_zero ha0 hψD
          obtain ⟨N', D', hN', hD', hNN⟩ := _root_.GlobalTheory.GeoFix.exists_inR_mul_eq_psi p Ω hc T n ψ h N hN hN0
          refine ⟨ψ D * N', D', inR_mul (inR_psi ψ D) hN', hD', ?_⟩
          rw [← hNN, ← ha]
          field_simp }
  have hF1 : ∀ c : O0 p, algebraMap (O0 p) Ω c ∈ F := by
    intro c
    have hmem : algebraMap (O0 p) Ω c ∈ ψ.range := by
      rw [h.rng]; exact Subalgebra.algebraMap_mem _ c
    obtain ⟨c', hc'⟩ := hmem
    exact ⟨ψ c', 1, inR_psi ψ c', one_ne_zero, by rw [map_one, mul_one, hc']⟩
  have hF2 : ∀ x : Ω, IsAlgZp p x → x ∈ F := by
    intro x hx
    obtain ⟨D, hD, hxD⟩ := exists_inR_of_isAlgZp hc h hx
    exact ⟨x * ψ D, D, hxD, hD, rfl⟩
  have hF3 : T.qq n ∈ F := ⟨ψ (qO p), 1, inR_psi ψ _, one_ne_zero, by rw [map_one, mul_one, h.par]⟩
  obtain ⟨N, D, hN, hD, hoD⟩ := GlobalTheory.T.mem_subfield_of_fixed_by_geometric_tower_galois p Ω hc T n F hF1 hF2 hF3 o hfix

  obtain ⟨_, hdvr, hirr⟩ := completed_laurent_isDVR p
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hD hirr
  have hN1 : InR ψ (N * ψ (↑u⁻¹ : O0 p)) := inR_mul hN (inR_psi ψ _)
  have hpo : (p : Ω) ^ v * o = N * ψ (↑u⁻¹ : O0 p) := by
    rw [← hoD, hu, map_mul, map_pow, map_natCast]
    have : ψ (↑u : O0 p) * ψ (↑u⁻¹ : O0 p) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    linear_combination (-(↑p ^ v * o)) * this
  obtain ⟨d, e, b, he, hNe⟩ := hN1
  obtain ⟨a, z, hz, hza⟩ := GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow p Ω T n ψ h d e b (fun t => (he t).1) (v + k)
  have hsum : ∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t)) = (p : Ω) ^ v * (o - (p : Ω) ^ k * z) := by
    rw [← hNe] at hza
    rw [pow_add] at hza
    linear_combination -hpo - hza
  have hpi : IsInt (p := p) ((p : Ω) ^ k) := by
    rw [IsInt, ← map_natCast (algebraMap (O0 p) Ω), ← map_pow]; exact isIntegral_algebraMap
  have ho' : IsInt (p := p) (o - (p : Ω) ^ k * z) := IsIntegral.sub ho (IsIntegral.mul hpi hz)
  obtain ⟨c, x', hEv⟩ := GlobalTheory.T.integral_of_expansionSum_eq_primePow_mul_isEval p Ω hc T n ψ h d e a he v _ ho' hsum
  exact ⟨c, _, x', hEv, z, hz, by ring⟩

end GlobalTheory.GeoFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpUpperTriangularStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ), ent g 1 0 = 0 → ∀ (f : T.K) (r : ℚ), (T.exp (T.sl g f)).coeff (r * ent g 0 0 / ent g 1 1) = eOm ε (r * ent g 0 1 / ent g 1 1) * (T.exp f).coeff r := by
  first | exact @GlobalTheory.FN.exp_sl_coeff_upper | exact GlobalTheory.FN.exp_sl_coeff_upper | (intros; apply GlobalTheory.FN.exp_sl_coeff_upper <;> assumption)
end

