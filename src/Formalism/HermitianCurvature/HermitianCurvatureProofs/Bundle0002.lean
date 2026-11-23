module

public import Formalism.HermitianCurvature.StatementG
public import Formalism.HermitianCurvature.Bundle0001

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdditiveCharacterPsi
section
open Matrix MeasureTheory

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace Formalism.FourierDecayAlt.P.G2

open Formalism.FourierDecayAlt.G

theorem symm_castSucc {n : ℕ} (i : Fin n) :
    finSumFinEquiv.symm (i.castSucc : Fin (n + 1)) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd (n := 1) i

theorem symm_last (n : ℕ) : finSumFinEquiv.symm (Fin.last n : Fin (n + 1)) = Sum.inr (0 : Fin 1) :=
  finSumFinEquiv_symm_apply_natAdd (m := n) (0 : Fin 1)

theorem blk_cc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i j : Fin n) :
    blk A b a e i.castSucc j.castSucc = A i j := by
  simp [blk, symm_castSucc]

theorem blk_cl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (i : Fin n) :
    blk A b a e i.castSucc (Fin.last n) = b i := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_lc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) (j : Fin n) :
    blk A b a e (Fin.last n) j.castSucc = a j := by
  simp [blk, symm_castSucc, symm_last]

theorem blk_ll {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b a : Fin n → ℂ) (e : ℂ) :
    blk A b a e (Fin.last n) (Fin.last n) = e := by
  simp [blk, symm_last]

theorem blk_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ) (b a b' a' : Fin n → ℂ) (e e' : ℂ) :
    blk A b a e * blk A' b' a' e' =
      blk (A * A' + Matrix.vecMulVec b a') (A *ᵥ b' + e' • b) (a ᵥ* A' + e • a') (a ⬝ᵥ b' + e * e') := by
  unfold blk
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  congr 2
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  · ext i j; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  · ext i j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j; simp [Matrix.mul_apply, dotProduct]

theorem det_blk_col_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) (e : ℂ) :
    (blk A 0 a e).det = A.det * e := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have h : (Matrix.of fun i (_ : Fin 1) => (0 : Fin n → ℂ) i) = (0 : Matrix (Fin n) (Fin 1) ℂ) := by
    ext i j; simp
  rw [h, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem det_blk_row_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b : Fin n → ℂ) (e : ℂ) :
    (blk A b 0 e).det = A.det * e := by
  unfold blk
  rw [Matrix.det_reindex_self]
  have h : (Matrix.of fun (_ : Fin 1) j => (0 : Fin n → ℂ) j) = (0 : Matrix (Fin 1) (Fin n) ℂ) := by
    ext i j; simp
  rw [h, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem det_upper {d : ℕ} (v : UT d → ℂ) : (upper v).det = 1 := by
  have h : (upper v).BlockTriangular id := by
    intro i j hij
    have hij' : j < i := hij
    simp [upper, strictUpper, Matrix.one_apply, hij'.ne', not_lt.2 hij'.le]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [upper, strictUpper]

theorem wMat_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (wMat n * A) i j = A i.rev j := by
  simp [wMat, Matrix.mul_apply]

theorem wMat_mulVec_apply {n : ℕ} (B : Fin n → ℂ) (i : Fin n) : (wMat n *ᵥ B) i = B i.rev := by
  simp [wMat, Matrix.mulVec, dotProduct]

theorem det_wMat_succ (n : ℕ) : (wMat (n + 1)).det = (-1) ^ n * (wMat n).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Finset.sum_eq_single (Fin.last n)]
  · have h : (wMat (n + 1)).submatrix Fin.succ (Fin.last n).succAbove = wMat n := by
      ext i j
      simp [wMat, Fin.rev_succ]
    rw [h]
    simp [wMat]
  · intro j _ hj
    simp [wMat, hj]
  · simp

theorem det_wMat_ne_zero (n : ℕ) : (wMat n).det ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [det_wMat_succ]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ih

end Formalism.FourierDecayAlt.P.G2

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

theorem additive_character_psi : Formalism.FourierDecayAlt.G.PsiChar := by
  intro β x y
  refine ⟨?_, ?_, ?_⟩
  · simp [psi, mul_add, Complex.exp_add]
  · simp only [psi]; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  · simp [psi]

theorem det_weyl_matrix : Formalism.FourierDecayAlt.G.DetMatch :=
  fun n => ⟨det_wMat_succ n, det_wMat_ne_zero n⟩

theorem det_orbit : Formalism.FourierDecayAlt.G.DetOrbit := by
  refine ⟨fun n t c p => ?_, fun d z v => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_mul, lowRow, ptBlock, det_blk_col_zero, det_blk_col_zero,
      det_blk_row_zero, det_upper, Matrix.det_smul]
    simp; ring
  · rw [Matrix.det_mul, det_upper, ptLong, Matrix.det_smul]
    simp; ring

theorem matrix_entries : Formalism.FourierDecayAlt.G.EntriesM := by
  intro n t c p
  obtain ⟨a, v, b⟩ := p
  simp only [lowRow, ptBlock, Mcoord, blk_mul, Xof, rhoOf, upper]
  congr 1
  · simp [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, smul_add]
  · ext i; simp [Matrix.mulVec_smul, Matrix.smul_mulVec]
  · simp [Matrix.vecMul_smul, Matrix.mul_add, Matrix.vecMul_add, smul_add, Matrix.smul_vecMul,
      ← Matrix.vecMul_vecMul]
  · simp [Matrix.mulVec_smul, Matrix.vecMul_smul, Matrix.dotProduct_mulVec, add_comm]

theorem shape_of_matrix : Formalism.FourierDecayAlt.G.ShapeM := by
  intro m t σ X B ρ hX
  refine ⟨fun i j hij => ?_, fun i j hij => ?_, fun k => ?_, ?_, ?_⟩
  · obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc :=
      ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc :=
      ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have hlt : j' < i'.rev := by
      rw [Fin.lt_def, Fin.val_rev]
      simp only [Fin.val_castSucc] at hij
      omega
    rw [Mcoord, blk_cc, wMat_mul_apply]
    simp [Matrix.one_apply, hlt.ne', hX _ _ hlt.le]
  · obtain ⟨i', rfl⟩ : ∃ i' : Fin (m + 1), i = i'.castSucc :=
      ⟨⟨i, by omega⟩, Fin.ext rfl⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 1), j = j'.castSucc :=
      ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have heq : i'.rev = j' := by
      apply Fin.ext
      rw [Fin.val_rev]
      simp only [Fin.val_castSucc] at hij
      omega
    rw [Mcoord, blk_cc, wMat_mul_apply, heq]
    simp [hX _ _ le_rfl]
  · rw [Mcoord, xOf]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, blk_cl, blk_cl, wMat_mulVec_apply, Fin.rev_rev]
    · rw [Fin.succ_castSucc, blk_cc, blk_cc, wMat_mul_apply, Fin.rev_rev]
      have hne : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
      simp [Matrix.one_apply, hne]
  · have h0 : (0 : Fin (m + 1 + 1)) = (0 : Fin (m + 1)).castSucc := rfl
    rw [Mcoord, h0, blk_lc]
  · rw [Mcoord, blk_ll]

theorem phase_formula : Formalism.FourierDecayAlt.G.PhaseFormula := by
  intro m t ht p
  obtain ⟨a, v, b⟩ := p
  have h1 : subSum (lowRow a) = a (Fin.last m) := by
    rw [subSum, Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add, Fin.succ_last, lowRow, blk_lc]
    intro i _
    have hne : i.succ ≠ i.castSucc := (Fin.castSucc_lt_succ).ne'
    rw [Fin.succ_castSucc, lowRow, blk_cc, Matrix.one_apply_ne hne]
  have h2 : rhoOf t a v 0 = t * a (Fin.last m) := by
    simp only [rhoOf, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, wMat_mul_apply]
    congr 1
    rw [Finset.sum_eq_single (Fin.last m)]
    · simp [upper, strictUpper]
    · intro i _ hi
      have hne : i.rev ≠ 0 := by
        intro h
        apply hi
        rw [← Fin.rev_rev i, h, Fin.rev_zero]
      have hnl : ¬ i.rev < 0 := by simp
      simp [upper, strictUpper, Matrix.one_apply_ne hne]
    · simp
  have h3 : ∀ k : Fin (m + 1), xOf (Xof t v) (t • b) k = t * blk (upper v) b 0 1 k.castSucc k.succ := by
    intro k
    rw [xOf]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · rw [Fin.succ_last, blk_cl, blk_cl]; simp
    · rw [Fin.succ_castSucc, blk_cc, blk_cc]
      have hne : k'.castSucc ≠ k'.succ := (Fin.castSucc_lt_succ).ne
      simp [Xof, upper, Matrix.one_apply_ne hne]
  show subSum (lowRow a) + superSum (blk (upper v) b 0 1) =
    (rhoOf t a v 0 + ∑ k, xOf (Xof t v) (t • b) k) / t
  rw [h1, h2, superSum, Finset.sum_congr rfl (fun k _ => h3 k), ← Finset.mul_sum]
  field_simp

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.Cauchy
section
namespace Formalism.FourierDecayAlt.P.Cauchy

open Complex Metric Set

theorem iteratedDeriv_ofReal {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {f : ℝ → ℝ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hfF : ∀ x : ℝ, F x = f x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧
      ∀ x : ℝ, iteratedDeriv p F x = (iteratedDeriv p f x : ℝ) := by
  induction p with
  | zero => simpa using ⟨hF, hfF⟩
  | succ p ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨?_, fun x => ?_⟩
    · rw [iteratedDeriv_succ]
      exact hd.deriv hU
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ) :=
        (hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt
      have h1 : HasDerivAt (fun y : ℝ => (iteratedDeriv p F y).re)
          (deriv (iteratedDeriv p F) x).re x := h0.real_of_complex
      have h2 : (fun y : ℝ => (iteratedDeriv p F y).re) = iteratedDeriv p f := by
        funext y; rw [he y]; simp
      rw [h2] at h1
      have h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y)
          (deriv (iteratedDeriv p F) x) x := h0.comp_ofReal
      have h4 : (fun y : ℝ => iteratedDeriv p F y) = fun y : ℝ => ((iteratedDeriv p f y : ℝ) : ℂ) := by
        funext y; rw [he y]
      rw [h4] at h3
      have h5 := h3.unique h1.ofReal_comp
      rw [h1.deriv]
      exact h5

theorem rpow_le_exp_one {σ : ℝ} (hσ : 4 ≤ σ) : (1 - 2 * (1 / (4 * σ))) ^ (-σ) ≤ Real.exp 1 := by
  have hσ0 : 0 < σ := by linarith
  have hx : 0 < 1 - 2 * (1 / (4 * σ)) := by
    have : 1 / (4 * σ) ≤ 1 / 16 := by
      apply one_div_le_one_div_of_le <;> linarith
    linarith
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  have h1 := Real.one_sub_inv_le_log_of_pos hx
  have h2 : (1 - 2 * (1 / (4 * σ)))⁻¹ = 2 * σ / (2 * σ - 1) := by
    have h21 : 1 - 2 * (1 / (4 * σ)) = (2 * σ - 1) / (2 * σ) := by
      field_simp
      ring
    rw [h21, inv_div]
  rw [h2] at h1
  have h3 : 1 - 2 * σ / (2 * σ - 1) = -(1 / (2 * σ - 1)) := by
    have : 2 * σ - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h3] at h1
  have h4 : 1 / (2 * σ - 1) ≤ 1 / σ := by
    apply one_div_le_one_div_of_le <;> linarith
  have h5 : -(1 / σ) ≤ Real.log (1 - 2 * (1 / (4 * σ))) := by linarith
  have h6 : σ * -(1 / σ) ≤ σ * Real.log (1 - 2 * (1 / (4 * σ))) :=
    mul_le_mul_of_nonneg_left h5 hσ0.le
  have h7 : σ * -(1 / σ) = -1 := by field_simp
  nlinarith

theorem base_bound {ε : ℝ} (hε : 0 < ε) (u : ℝ) {ρ : ℝ} (hρ : ρ ≤ 1 / 16) {w : ℂ}
    (hw : ‖w - u‖ ≤ ρ) :
    (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ (1 + (ε : ℂ) * Complex.exp (-w)).re := by
  set a : ℝ := ε * Real.exp (-u) with ha
  have ha0 : 0 < a := by positivity
  have h1 : 1 + (ε : ℂ) * Complex.exp (-w) = ((1 + a : ℝ) : ℂ) + (a : ℂ) * (Complex.exp (-(w - u)) - 1) := by
    have : Complex.exp (-w) = Complex.exp (-(u : ℂ)) * Complex.exp (-(w - u)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this, ha]
    push_cast
    ring
  have h2 : ‖Complex.exp (-(w - u)) - 1‖ ≤ 2 * ρ := by
    have h := Complex.norm_exp_sub_one_le (x := -(w - u)) (by rw [norm_neg]; linarith)
    rw [norm_neg] at h
    linarith
  have h3 : -(2 * ρ) ≤ (Complex.exp (-(w - u)) - 1).re := by
    have := Complex.abs_re_le_norm (Complex.exp (-(w - u)) - 1)
    have := neg_abs_le (Complex.exp (-(w - u)) - 1).re
    linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hw
  have h4 : a * -(2 * ρ) ≤ a * (Complex.exp (-(w - u)) - 1).re :=
    mul_le_mul_of_nonneg_left h3 ha0.le
  rw [h1, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  nlinarith

end Formalism.FourierDecayAlt.P.Cauchy

namespace Formalism.FourierDecayAlt.P

open Complex Metric Set Formalism.FourierDecayAlt.P.Cauchy

theorem cauchy_theta_identity : Formalism.FourierDecayAlt.E.CauchyTheta := by
  intro σ ε hσ hε p u
  have hσ0 : 0 < σ := by linarith
  set ρ : ℝ := 1 / (4 * σ) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ : ρ ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le <;> linarith
  set F : ℂ → ℂ := fun w => (1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ) with hF
  set f : ℝ → ℝ := fun v => (1 + ε * Real.exp (-v)) ^ (-σ) with hf
  set U : Set ℂ := {w | 0 < (1 + (ε : ℂ) * Complex.exp (-w)).re} with hUdef
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    fun_prop
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.cpow_const (by fun_prop)
    exact Or.inl hw
  have hpos : ∀ x : ℝ, 0 < 1 + ε * Real.exp (-x) := fun x => by positivity
  have hcast : ∀ x : ℝ, 1 + (ε : ℂ) * Complex.exp (-(x : ℂ)) = ((1 + ε * Real.exp (-x) : ℝ) : ℂ) := by
    intro x; push_cast; ring
  have hmem : ∀ x : ℝ, (x : ℂ) ∈ U := by
    intro x
    show 0 < (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))).re
    rw [hcast, Complex.ofReal_re]
    exact hpos x
  have hfF : ∀ x : ℝ, F x = f x := by
    intro x
    show (1 + (ε : ℂ) * Complex.exp (-(x : ℂ))) ^ ((-σ : ℝ) : ℂ) = _
    rw [hcast, ← Complex.ofReal_cpow (hpos x).le]
  have key := (iteratedDeriv_ofReal hU hFd hmem hfF p).2 u
  have hA : 0 < 1 + ε * Real.exp (-u) := hpos u
  have h12 : 0 < 1 - 2 * ρ := by linarith
  have hsub : closedBall (u : ℂ) ρ ⊆ U := by
    intro w hw
    have := base_bound hε u hρ (w := w) (by simpa [dist_eq_norm] using hw)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    exact lt_of_lt_of_le h0 this
  have hC : ∀ w ∈ sphere (u : ℂ) ρ, ‖F w‖ ≤ Real.exp 1 * (1 + ε * Real.exp (-u)) ^ (-σ) := by
    intro w hw
    have hb := base_bound hε u hρ (w := w) (by
      have : ‖w - u‖ = ρ := by simpa [dist_eq_norm] using hw
      exact this.le)
    have h0 : 0 < (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) := by positivity
    have hn : (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ ‖1 + (ε : ℂ) * Complex.exp (-w)‖ :=
      hb.trans (Complex.re_le_norm _)
    show ‖(1 + (ε : ℂ) * Complex.exp (-w)) ^ ((-σ : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_cpow_real]
    calc ‖1 + (ε : ℂ) * Complex.exp (-w)‖ ^ (-σ)
        ≤ ((1 + ε * Real.exp (-u)) * (1 - 2 * ρ)) ^ (-σ) :=
          Real.rpow_le_rpow_of_nonpos h0 hn (by linarith)
      _ = (1 + ε * Real.exp (-u)) ^ (-σ) * (1 - 2 * ρ) ^ (-σ) :=
          Real.mul_rpow hA.le h12.le
      _ ≤ (1 + ε * Real.exp (-u)) ^ (-σ) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (rpow_le_exp_one hσ) (by positivity)
      _ = _ := mul_comm _ _
  have hcau := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le p hρ0
    (hFd.diffContOnCl_ball hsub) hC
  rw [key, Complex.norm_real, Real.norm_eq_abs] at hcau
  refine hcau.trans (le_of_eq ?_)
  rw [hρdef, one_div, inv_pow, div_inv_eq_mul]
  ring

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DualIdealInclusion
section
namespace Formalism.FourierDecayAlt.P.Dual

open NumberField FractionalIdeal

theorem alg {E : Type} [Field E] [NumberField E] (dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hdd : dd ≠ 0) (ν g : ℤ) (hg : g ≠ 0) :
    spanSingleton _ (g : E) * (dd⁻¹ * (dd ^ ν * spanSingleton _ ((g : E) ^ 2))⁻¹) =
      dd ^ (-(ν + 1)) * spanSingleton _ ((g : E)⁻¹) := by
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  rw [mul_inv (dd ^ ν), spanSingleton_inv]
  have h1 : spanSingleton (nonZeroDivisors (𝓞 E)) (g : E) * spanSingleton _ (((g : E) ^ 2)⁻¹) =
      spanSingleton _ ((g : E)⁻¹) := by
    rw [spanSingleton_mul_spanSingleton]; congr 1; field_simp
  rw [show dd ^ (-(ν + 1)) = dd⁻¹ * (dd ^ ν)⁻¹ by
    rw [neg_add, zpow_add₀ hdd, _root_.zpow_neg, zpow_neg_one, mul_comm]]
  rw [← h1]; ring

theorem dual_third_group_integral : Formalism.FourierDecayAlt.L.DualLatticeInclusion := by
  intro E _ _ dd h1 ν g hg La hLa x hx
  have hdd : dd ≠ 0 := by
    intro h0; rw [h0, _root_.inv_zero] at h1; exact dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) h1
  have hgE : (g : E) ≠ 0 := by exact_mod_cast hg
  have hJ : dd ^ ν * spanSingleton (nonZeroDivisors (𝓞 E)) ((g : E) ^ 2) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hdd) (by simp [spanSingleton_eq_zero_iff, hgE])
  have hy : x * (g : E)⁻¹ ∈ dual ℤ ℚ (dd ^ ν * spanSingleton _ ((g : E) ^ 2)) := by
    rw [mem_dual hJ]
    intro a ha
    have := hx a (hLa a ha)
    rw [Algebra.traceForm_apply]
    convert this using 2
    field_simp
  rw [dual_eq_mul_inv ℤ ℚ, h1] at hy
  rw [← alg dd hdd ν g hg]
  have := mul_mem_mul (mem_spanSingleton_self (nonZeroDivisors (𝓞 E)) (g : E)) hy
  convert this using 1
  field_simp

end Formalism.FourierDecayAlt.P.Dual

theorem Formalism.FourierDecayAlt.P.dual_third_group_holds : Formalism.FourierDecayAlt.L.DualLatticeInclusion := Formalism.FourierDecayAlt.P.Dual.dual_third_group_integral
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.MiddleThirdEstimate
section
namespace Formalism.FourierDecayAlt.P.E2

open Formalism.FourierDecayAlt.E Real Polynomial MeasureTheory

theorem bdd_add' {Λ : Type} {f g : Λ → ℂ} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨a, ha⟩ := hf; obtain ⟨b, hb⟩ := hg
  exact ⟨a + b, fun x => (norm_add_le _ _).trans (add_le_add (ha x) (hb x))⟩

theorem bdd_smul' {Λ : Type} {f : Λ → ℂ} (c : ℂ) (hf : Bdd f) : Bdd (c • f) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨‖c‖ * a, fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (ha x) (norm_nonneg _)⟩

theorem bdd_zero' {Λ : Type} : Bdd (0 : Λ → ℂ) := ⟨0, fun x => by simp⟩

theorem bdd_sum' {Λ ι : Type} (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    Bdd (∑ i ∈ T, f i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using bdd_zero'
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact bdd_add' (hf a) ih

theorem lim_sum' {Λ ι : Type} (LIM : (Λ → ℂ) → ℂ)
    (h1 : ∀ f g, Bdd f → Bdd g → LIM (f + g) = LIM f + LIM g)
    (h2 : ∀ (c : ℂ) f, Bdd f → LIM (c • f) = c * LIM f)
    (T : Finset ι) (f : ι → Λ → ℂ) (hf : ∀ i, Bdd (f i)) :
    LIM (∑ i ∈ T, f i) = ∑ i ∈ T, LIM (f i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := h2 0 0 bdd_zero'
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1 _ _ (hf a) (bdd_sum' s f hf), ih]

theorem mpd : MeanPosDef := by
  intro Λ _ H _ _ LIM h1 h2 h3 h4 u B hu S c
  have hB : ∀ a b : Λ, Bdd (fun x => inner ℂ (u (x + a)) (u (x + b))) := fun a b =>
    ⟨B * B, fun x => (norm_inner_le_norm _ _).trans
      (mul_le_mul (hu _) (hu _) (norm_nonneg _) ((norm_nonneg _).trans (hu (x+a))))⟩
  have hB0 : ∀ b : Λ, Bdd (fun x => inner ℂ (u x) (u (x + b))) := fun b => by simpa using hB 0 b
  have e1 : ∀ σ σ' : Λ, LIM (fun x => inner ℂ (u x) (u (x + (σ - σ'))))
      = LIM (fun x => inner ℂ (u (x + σ')) (u (x + σ))) := by
    intro σ σ'
    rw [← h4 _ σ' (hB0 (σ - σ'))]
    congr 1; funext x; congr 2; abel
  have e2 : (∑ σ ∈ S, ∑ σ' ∈ S,
        LIM (fun x => inner ℂ (u x) (u (x + (σ - σ')))) * c σ * starRingEnd ℂ (c σ'))
      = LIM (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) := by
    rw [lim_sum' LIM h1 h2 S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [lim_sum' LIM h1 h2 S _ (fun σ' => bdd_smul' _ (hB σ' σ))]
    refine Finset.sum_congr rfl fun σ' _ => ?_
    rw [h2 _ _ (hB σ' σ), e1]; ring
  rw [e2]
  apply h3
  · exact bdd_sum' S _ (fun σ => bdd_sum' S _ (fun σ' => bdd_smul' _ (hB σ' σ)))
  · intro x
    have key : (∑ σ ∈ S, ∑ σ' ∈ S,
          (c σ * starRingEnd ℂ (c σ')) • (fun x => inner ℂ (u (x + σ')) (u (x + σ)))) x
        = inner ℂ (∑ σ ∈ S, c σ • u (x + σ)) (∑ σ ∈ S, c σ • u (x + σ)) := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [key]
    exact ⟨inner_self_nonneg (𝕜 := ℂ), inner_self_im (𝕜 := ℂ) _⟩

end Formalism.FourierDecayAlt.P.E2

theorem Formalism.FourierDecayAlt.P.mean_matrix_posDef : Formalism.FourierDecayAlt.E.MeanPosDef := Formalism.FourierDecayAlt.P.E2.mpd
end

