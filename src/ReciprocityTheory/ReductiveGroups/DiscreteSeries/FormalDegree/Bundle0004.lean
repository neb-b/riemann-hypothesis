module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HasDerivAtMexpCommAddBracket
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section Banach

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

theorem hasDerivAt_exp_comm_add_bracket (A V X : R) (h : Commute A V) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • (V + (X * A - A * X))))
      (NormedSpace.exp A * V + (X * NormedSpace.exp A - NormedSpace.exp A * X)) 0 := by
  letI : NormedAlgebra ℚ R := NormedAlgebra.restrictScalars ℚ ℝ R
  have hdiff : DifferentiableAt ℝ NormedSpace.exp A :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) A).differentiableAt
  have hchain : ∀ B : R, HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • B))
      (fderiv ℝ NormedSpace.exp A B) 0 := by
    intro B
    have hl : HasDerivAt (fun s : ℝ => A + s • B) B 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const B).const_add A
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hV : fderiv ℝ NormedSpace.exp A V = NormedSpace.exp A * V := by
    have h2 : HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • V)) (NormedSpace.exp A * V) 0 := by
      have h3 : (fun s : ℝ => NormedSpace.exp (A + s • V)) =
          fun s => NormedSpace.exp A * NormedSpace.exp (s • V) := by
        funext s
        exact NormedSpace.exp_add_of_commute (h.smul_right s)
      rw [h3]
      have h4 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) V (0 : ℝ)).const_mul (NormedSpace.exp A)
      simpa using h4
    exact (hchain V).unique h2
  have hinv : ∀ s : ℝ, NormedSpace.exp (s • X) * NormedSpace.exp (s • (-X)) = 1 ∧
      NormedSpace.exp (s • (-X)) * NormedSpace.exp (s • X) = 1 := by
    intro s
    constructor
    · rw [smul_neg, ← NormedSpace.exp_add_of_commute ((Commute.refl (s • X)).neg_right),
        add_neg_cancel, NormedSpace.exp_zero]
    · rw [smul_neg, ← NormedSpace.exp_add_of_commute ((Commute.refl (s • X)).neg_left),
        neg_add_cancel, NormedSpace.exp_zero]
  have hFG : (fun s : ℝ => NormedSpace.exp (NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X)))) =
      fun s => NormedSpace.exp (s • X) * NormedSpace.exp A * NormedSpace.exp (s • (-X)) := by
    funext s
    exact NormedSpace.exp_units_conj
      ⟨NormedSpace.exp (s • X), NormedSpace.exp (s • (-X)), (hinv s).1, (hinv s).2⟩ A
  have hd1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  have hd2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at hd1 hd2
  have hc : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X)))
      (X * A - A * X) 0 := by
    have := (hd1.mul_const A).mul hd2
    refine this.congr_deriv ?_
    simp [sub_eq_add_neg]
  have hF : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * NormedSpace.exp A * NormedSpace.exp (s • (-X)))
      (X * NormedSpace.exp A - NormedSpace.exp A * X) 0 := by
    have := (hd1.mul_const (NormedSpace.exp A)).mul hd2
    refine this.congr_deriv ?_
    simp [sub_eq_add_neg]
  have hG : HasDerivAt (fun s : ℝ => NormedSpace.exp (NormedSpace.exp (s • X) * A * NormedSpace.exp (s • (-X))))
      (fderiv ℝ NormedSpace.exp A (X * A - A * X)) 0 :=
    hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  rw [hFG] at hG
  have hB : fderiv ℝ NormedSpace.exp A (X * A - A * X) = X * NormedSpace.exp A - NormedSpace.exp A * X :=
    hG.unique hF
  have key := hchain (V + (X * A - A * X))
  rw [map_add (f := _), hV, hB] at key
  exact key

end Banach

section Operator

open scoped Matrix.Norms.Operator in
set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_mexp_comm_add_bracket (A V X : Matrix (Fin n) (Fin n) ℂ) (h : Commute A V) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (A + s • (V + (X * A - A * X))))
      (NormedSpace.exp A * V + (X * NormedSpace.exp A - NormedSpace.exp A * X)) 0 := by
  exact hasDerivAt_exp_comm_add_bracket A V X h

end Operator

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def shcAd {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
    Matrix.of (fun i j => ((shc (pev y i - pev y j) : ℝ) : ℂ) *
      ((((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ * W *
        ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)) i j) *
    (((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ

private theorem hasDerivAt_exp_conj_diag (U U' : Matrix (Fin n) (Fin n) ℂ) (h1 : U * U' = 1) (h2 : U' * U = 1)
    (x : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp
        ((2 : ℂ) • (U * diagonal (fun i => (x i : ℂ)) * U') + (s : ℂ) • W))
      (NormedSpace.exp (U * diagonal (fun i => (x i : ℂ)) * U') *
        (U * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * (U' * W * U) i j) * U') *
        NormedSpace.exp (U * diagonal (fun i => (x i : ℂ)) * U')) 0 := by
  classical
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (x i : ℂ)) with hD
  set W' := U' * W * U with hW'
  set A : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (2 * x i : ℂ)) with hA
  set V : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => if x i = x j then W' i j else 0) with hV
  set Xm : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun i j => if x i = x j then 0 else W' i j / (2 * (x j : ℂ) - 2 * x i)) with hXm
  have hcomm : Commute A V := by
    show A * V = V * A
    ext i j
    simp only [hA, hV, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    by_cases h : x i = x j
    · simp only [h, if_true]
      ring
    · simp only [h, if_false, mul_zero, zero_mul]
  have hsplit : V + (Xm * A - A * Xm) = W' := by
    ext i j
    simp only [hA, hV, hXm, Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.of_apply]
    split_ifs with h
    · simp
    · have h' : (2 * (x j : ℂ) - 2 * x i) ≠ 0 := by
        intro h0
        apply h
        have : ((x i : ℝ) : ℂ) = x j := by linear_combination -h0 / 2
        exact_mod_cast this
      calc _ = W' i j / (2 * (x j : ℂ) - 2 * x i) * (2 * x j - 2 * x i) := by ring
        _ = W' i j := div_mul_cancel₀ _ h'
  have hder := hasDerivAt_mexp_comm_add_bracket A V Xm hcomm
  rw [hsplit] at hder
  have hexpA : NormedSpace.exp A = diagonal (fun i => Complex.exp (2 * x i)) := by
    rw [hA, Matrix.exp_diagonal]
    rw [Pi.exp_def]
    congr 1
    funext i
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  have hexpD : NormedSpace.exp D = diagonal (fun i => Complex.exp (x i)) := by
    rw [hD, Matrix.exp_diagonal]
    rw [Pi.exp_def]
    congr 1
    funext i
    exact (congrFun Complex.exp_eq_exp_ℂ _).symm
  have hval : NormedSpace.exp A * V + (Xm * NormedSpace.exp A - NormedSpace.exp A * Xm) =
      NormedSpace.exp D * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * W' i j) *
        NormedSpace.exp D := by
    rw [hexpA, hexpD]
    ext i j
    simp only [hV, hXm, Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.of_apply]
    by_cases h : x i = x j
    · simp only [h, if_true, sub_self, shc, if_true, Complex.ofReal_one, mul_zero, zero_mul,
        sub_zero, add_zero, one_mul]
      rw [show (2 * (x j : ℂ)) = x j + x j by ring, Complex.exp_add]
      ring
    · simp only [h, if_false, mul_zero, zero_add]
      have hne : x i - x j ≠ 0 := sub_ne_zero.mpr h
      have hreal : (Real.exp (2 * x j) - Real.exp (2 * x i)) / (2 * x j - 2 * x i) =
          Real.exp (x i) * Real.exp (x j) * (Real.sinh (x i - x j) / (x i - x j)) := by
        have h3 : (2 * x j - 2 * x i) ≠ 0 := by
          intro h0
          apply hne
          linarith
        have ei := Real.exp_pos (x i)
        have ej := Real.exp_pos (x j)
        rw [Real.sinh_eq, Real.exp_neg, Real.exp_sub, two_mul, two_mul, Real.exp_add, Real.exp_add]
        field_simp
        ring
      unfold shc
      rw [if_neg hne]
      have hC := congrArg (fun r : ℝ => (r : ℂ)) hreal
      push_cast at hC
      push_cast
      calc _ = W' i j * ((Complex.exp (2 * (x j : ℂ)) - Complex.exp (2 * (x i : ℂ))) /
            (2 * (x j : ℂ) - 2 * x i)) := by ring
        _ = _ := by
          rw [hC]
          ring
  rw [hval] at hder

  have hunit : IsUnit U := ⟨⟨U, U', h1, h2⟩, rfl⟩
  have hconjExp : ∀ M : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp (U * M * U') = U * NormedSpace.exp M * U' :=
    fun M => Matrix.exp_units_conj ⟨U, U', h1, h2⟩ M
  have hfun : (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • (U * D * U') + (s : ℂ) • W)) =
      fun s : ℝ => U * NormedSpace.exp (A + s • W') * U' := by
    funext s
    rw [← hconjExp]
    congr 1
    have hA2 : A = (2 : ℂ) • D := by
      rw [hA, hD]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [hA2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, ← Complex.coe_smul,
      Matrix.mul_smul, Matrix.smul_mul, hW']
    congr 1
    rw [show U * (U' * W * U) * U' = (U * U') * W * (U * U') by simp only [Matrix.mul_assoc], h1,
      Matrix.one_mul, Matrix.mul_one]
  have hD2 : U * D * U' = U * diagonal (fun i => (x i : ℂ)) * U' := rfl
  rw [← hD2, hfun]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun M => U * M * U'
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul] }
  have hL := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hder
  have hL' : HasDerivAt (fun s : ℝ => U * NormedSpace.exp (A + s • W') * U')
      (U * (NormedSpace.exp D * Matrix.of (fun i j => ((shc (x i - x j) : ℝ) : ℂ) * W' i j) *
        NormedSpace.exp D) * U') 0 := hL
  refine hL'.congr_deriv ?_
  rw [hconjExp D]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U' U, h2, Matrix.one_mul, ← Matrix.mul_assoc U' U, h2, Matrix.one_mul]

private theorem pmat_spectral {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    pmat y = ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun i => (pev y i : ℂ)) *
      (((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
  have h := (pmat_isHermitian y).spectral_theorem
  conv_lhs => rw [h]
  first
  | rfl
  | simp [Function.comp_def, Matrix.star_eq_conjTranspose, pev]

theorem hasDerivAt_exp_two {ε : Fin n → Bool} (y : PCoord ε → ℂ) (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((2 : ℂ) • pmat y + (s : ℂ) • W))
      (NormedSpace.exp (pmat y) * shcAd y W * NormedSpace.exp (pmat y)) 0 := by
  set U : Matrix (Fin n) (Fin n) ℂ :=
    ((pmat_isHermitian y).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU1 : U * Uᴴ = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff.mp (pmat_isHermitian y).eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h0
  have hU2 : Uᴴ * U = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp (pmat_isHermitian y).eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h0
  have key := hasDerivAt_exp_conj_diag U Uᴴ hU1 hU2 (pev y) W
  rw [← pmat_spectral y] at key
  exact key

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasicA
section
noncomputable section

open Finset Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pmat_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
  refine continuous_matrix fun a b => ?_
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · simp only [pmat, dif_pos h1]; exact continuous_apply _
  · by_cases h2 : a < b ∧ ε b ≠ ε a
    · simp only [pmat, dif_neg h1, dif_pos h2]; exact (continuous_apply _).star
    · simp only [pmat, dif_neg h1, dif_neg h2]; exact continuous_const

theorem pb_trace_pow_herm {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (j : ℕ) :
    (A ^ j).trace = ∑ a, ((hA.eigenvalues a : ℝ) : ℂ) ^ j := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  first
    | (rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
        Matrix.diagonal_pow, Matrix.trace_diagonal]
       simp)
    | simp [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Matrix.diagonal_pow, Matrix.trace_diagonal]

theorem psum_continuous (ε : Fin n → Bool) (j : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, pev z a ^ j) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, pev z a ^ j) = fun z => ((pmat z) ^ j).trace.re := by
    funext z
    rw [pb_trace_pow_herm (pmat_isHermitian z) j, Complex.re_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
      try rfl
  rw [h]
  exact Complex.continuous_re.comp (((pmat_continuous ε).pow j).matrix_trace)

theorem negpsum_continuous (ε : Fin n → Bool) (j : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ b, (-pev z b) ^ j) := by
  have h : (fun z : PCoord ε → ℂ => ∑ b, (-pev z b) ^ j) = fun z => (-1) ^ j * ∑ b, pev z b ^ j := by
    funext z
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => neg_pow _ _
  rw [h]
  exact continuous_const.mul (psum_continuous ε j)

theorem pairpow_continuous (ε : Fin n → Bool) (k : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, (pev z a - pev z b) ^ k) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, ∑ b, (pev z a - pev z b) ^ k) =
      fun z => ∑ i ∈ range (k + 1),
        (∑ a, pev z a ^ i) * (∑ b, (-pev z b) ^ (k - i)) * (k.choose i : ℝ) := by
    funext z
    simp_rw [sub_eq_add_neg, add_pow, Finset.sum_mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
  rw [h]
  exact continuous_finsetSum _ fun i _ =>
    ((psum_continuous ε i).mul (negpsum_continuous ε (k - i))).mul continuous_const

theorem pairpoly_continuous (ε : Fin n → Bool) (P : Polynomial ℝ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, P.eval (pev z a - pev z b)) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, ∑ b, P.eval (pev z a - pev z b)) =
      fun z => ∑ i ∈ range (P.natDegree + 1), P.coeff i * ∑ a, ∑ b, (pev z a - pev z b) ^ i := by
    funext z
    simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
  rw [h]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (pairpow_continuous ε i)

theorem pb_abs_pev_le {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a : Fin n) :
    |pev z a| ≤ Real.sqrt (∑ b, pev z b ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun b => pev z b ^ 2)
    (fun b _ => sq_nonneg _) (Finset.mem_univ a))

theorem pairfun_continuous (ε : Fin n → Bool) (h : ℝ → ℝ) (hc : Continuous h) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, h (pev z a - pev z b)) := by
  have hS : Continuous (fun z : PCoord ε → ℂ => Real.sqrt (∑ b, pev z b ^ 2)) :=
    (psum_continuous ε 2).sqrt
  rw [Metric.continuous_iff]
  intro z0 e he
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuous_iff.1 hS z0 1 one_pos
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt (∑ b, pev z0 b ^ 2) + 1 := ⟨_, rfl⟩
  have hbd : ∀ z, dist z z0 < δ1 → ∀ a b, pev z a - pev z b ∈ Set.Icc (-(2 * R)) (2 * R) := by
    intro z hz a b
    have hSz : Real.sqrt (∑ b, pev z b ^ 2) ≤ R := by
      have h1z := h1 z hz
      rw [Real.dist_eq] at h1z
      linarith [(abs_lt.1 h1z).2]
    have ha := abs_le.1 ((pb_abs_pev_le z a).trans hSz)
    have hb := abs_le.1 ((pb_abs_pev_le z b).trans hSz)
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = e / (3 * ((n : ℝ) * n + 1)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-(2 * R)) (2 * R) h hc.continuousOn η hηpos
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuous_iff.1 (pairpoly_continuous ε p) z0 (e / 3) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun z hz => ?_⟩
  have hz1 : dist z z0 < δ1 := hz.trans_le (min_le_left _ _)
  have hz2 : dist z z0 < δ2 := hz.trans_le (min_le_right _ _)
  have happrox : ∀ w, dist w z0 < δ1 →
      |∑ a, ∑ b, h (pev w a - pev w b) - ∑ a, ∑ b, p.eval (pev w a - pev w b)| ≤ n * n * η := by
    intro w hw
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hrow : ∀ a, |∑ b, h (pev w a - pev w b) - ∑ b, p.eval (pev w a - pev w b)| ≤ n * η := by
      intro a
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ b, |h (pev w a - pev w b) - p.eval (pev w a - pev w b)| ≤ ∑ _b : Fin n, η :=
            Finset.sum_le_sum fun b _ => by
              rw [abs_sub_comm]; exact (hp _ (hbd w hw a b)).le
        _ = n * η := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ∑ a, |∑ b, h (pev w a - pev w b) - ∑ b, p.eval (pev w a - pev w b)| ≤ ∑ _a : Fin n, (n * η) :=
          Finset.sum_le_sum fun a _ => hrow a
      _ = n * n * η := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hA := abs_le.1 (happrox z hz1)
  have hB := abs_le.1 (happrox z0 (by simpa using hδ1))
  have hC := h2 z hz2
  rw [Real.dist_eq] at hC
  have hsmall : (n : ℝ) * n * η < e / 3 := by
    have hq : (n : ℝ) * n / (n * n + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    have heq : (n : ℝ) * n * η = e / 3 * ((n * n) / (n * n + 1)) := by
      rw [hη]
      first | (field_simp; ring) | field_simp | ring
    rw [heq]
    exact mul_lt_of_lt_one_right (by positivity) hq
  rw [Real.dist_eq]
  have hC' := abs_lt.1 hC
  exact abs_sub_lt_iff.2 ⟨by linarith [hA.1, hA.2, hB.1, hB.2, hC'.1, hC'.2],
    by linarith [hA.1, hA.2, hB.1, hB.2, hC'.1, hC'.2]⟩

theorem pb_shc_eq_update : shc = Function.update (fun u : ℝ => Real.sinh u / u) 0 1 := by
  funext u
  rw [Function.update_apply]
  rfl

theorem pb_shc_continuous : Continuous shc := by
  rw [pb_shc_eq_update, continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    rw [continuousAt_update_same]
    have hd := Real.hasDerivAt_sinh 0
    rw [hasDerivAt_iff_tendsto_slope, Real.cosh_zero] at hd
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    rw [slope_def_field]
    simp
  · rw [continuousAt_update_of_ne hu]
    exact (Real.continuous_sinh.continuousAt).div continuousAt_id hu

theorem pb_shc_pos (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with hu
  · exact one_pos
  · rcases lt_or_gt_of_ne hu with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h
    · exact div_pos (Real.sinh_pos_iff.2 h) h

theorem pb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  by_cases hu : u = 0
  · simp [shc, hu]
  · simp [shc, hu, Real.sinh_neg, neg_div_neg_eq]

theorem pb_sum_pairs_half {f : Fin n → Fin n → ℝ} (hsym : ∀ a b, f a b = f b a) (hd : ∀ a, f a a = 0) :
    ∑ a, ∑ b ∈ univ.filter (fun b => a < b), f a b = (∑ a, ∑ b, f a b) / 2 := by
  have hpt : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, not_lt.2 h.le]
    · simp [hd]
    · simp [h, not_lt.2 h.le]
  have hswap : ∑ a, ∑ b, (if b < a then f a b else 0) = ∑ a, ∑ b, (if a < b then f a b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsym]
  have htot : ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b, (if a < b then f a b else 0) := by
    conv_lhs => enter [2, a, 2, b]; rw [hpt a b]
    simp only [Finset.sum_add_distrib]
    rw [hswap]
    ring
  have hf : ∀ a, ∑ b ∈ univ.filter (fun b => a < b), f a b = ∑ b, (if a < b then f a b else 0) :=
    fun a => Finset.sum_filter _ _
  simp_rw [hf]
  rw [htot]
  ring

theorem pb_jac_eq_exp {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    Jac z = Real.exp ((∑ a, ∑ b, Real.log (shc (pev z a - pev z b))) / 2) := by
  have hsym : ∀ a b, Real.log (shc (pev z a - pev z b)) = Real.log (shc (pev z b - pev z a)) := by
    intro a b
    rw [← neg_sub (pev z a) (pev z b), pb_shc_neg]
  have hd : ∀ a, Real.log (shc (pev z a - pev z a)) = 0 := by
    intro a
    simp [shc]
  have hh := pb_sum_pairs_half (f := fun a b => Real.log (shc (pev z a - pev z b))) hsym hd
  try simp only at hh
  rw [← hh, Real.exp_sum]
  unfold Jac
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Real.exp_log (pb_shc_pos _)]

theorem pb_jac_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => Jac z) := by
  have h : (fun z : PCoord ε → ℂ => Jac z) =
      fun z => Real.exp ((∑ a, ∑ b, Real.log (shc (pev z a - pev z b))) / 2) := funext pb_jac_eq_exp
  rw [h]
  exact Real.continuous_exp.comp ((pairfun_continuous ε _
    (pb_shc_continuous.log fun u => (pb_shc_pos u).ne')).div_const 2)

end ReciprocityTheory.ChartRestriction.DS
end
end

