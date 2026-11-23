module

public import Mathlib
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0049
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0136
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsGradedMatrixEigenBound
section
open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

noncomputable section

namespace GlobalTheory.CompanionTheory.UGeo.SpecGrad

variable {n : ℕ}

theorem aeval_intertwine {R : Type*} [Ring R] [Algebra ℝ R] {X A B : R} (h : X * A = B * X)
    (p : Polynomial ℝ) : X * Polynomial.aeval A p = Polynomial.aeval B p * X := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), mul_add, add_mul, hp, hq]
  | monomial k a =>
    have hk : X * A ^ k = B ^ k * X := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_succ]
    simp only [Polynomial.aeval_monomial]
    rw [← mul_assoc, ← Algebra.commutes, mul_assoc, hk, mul_assoc]

def cj (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  U * diagonal (fun i => (d i : ℂ)) * Uᴴ

variable {U : Matrix (Fin n) (Fin n) ℂ}

theorem cj_mul (h1 : Uᴴ * U = 1) (d e : Fin n → ℝ) : cj U d * cj U e = cj U (fun i => d i * e i) := by
  have hd : diagonal (fun i => (d i : ℂ)) * diagonal (fun i => (e i : ℂ))
      = diagonal (fun i => ((d i * e i : ℝ) : ℂ)) := by
    rw [diagonal_mul_diagonal]; simp
  simp only [cj]
  calc _ = U * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (e i : ℂ)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one, Matrix.mul_assoc U, hd]

theorem cj_conj (d : Fin n → ℝ) : (cj U d)ᴴ = cj U d := by
  have h : (diagonal fun i => (d i : ℂ))ᴴ = diagonal fun i => (d i : ℂ) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp
  rw [cj, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h, Matrix.mul_assoc]

theorem cj_one (h2 : U * Uᴴ = 1) : cj U (fun _ => 1) = 1 := by
  simp [cj, h2]

theorem cj_add (d e : Fin n → ℝ) : cj U (fun i => d i + e i) = cj U d + cj U e := by
  rw [cj, cj, cj, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  congr 3; funext i; push_cast; rfl

theorem cj_smul (c : ℝ) (d : Fin n → ℝ) : cj U (fun i => c * d i) = (c : ℂ) • cj U d := by
  have h : (diagonal fun i => ((c * d i : ℝ) : ℂ)) = (c : ℂ) • diagonal fun i => (d i : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij]
  rw [cj, cj, h, Matrix.mul_smul, Matrix.smul_mul]

theorem cj_neg (d : Fin n → ℝ) : cj U (fun i => - d i) = - cj U d := by
  have := cj_smul (U := U) (-1) d
  simpa using this

theorem algebraMap_eq (a : ℝ) : algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) a = (a : ℂ) • 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

theorem cj_aeval (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1) (d : Fin n → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (cj U d) p = cj U (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), Polynomial.eval_add, hp, hq, cj_add]
  | monomial k a =>
    have hk : cj U d ^ k = cj U (fun i => d i ^ k) := by
      induction k with
      | zero => simp only [pow_zero]; exact (cj_one h2).symm
      | succ k ih => rw [pow_succ, ih, cj_mul h1]; simp only [pow_succ]
    rw [Polynomial.aeval_monomial, hk, algebraMap_eq, smul_mul_assoc, one_mul, ← cj_smul]
    simp only [Polynomial.eval_monomial]

theorem cj_eq_zero (h1 : Uᴴ * U = 1) {d : Fin n → ℝ} (h : cj U d = 0) (i : Fin n) : d i = 0 := by
  have e : diagonal (fun i => (d i : ℂ)) = Uᴴ * cj U d * U := by
    simp only [cj]
    calc _ = (Uᴴ * U) * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by rw [h1]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h] at e
  have := congrFun (congrFun e i) i
  simpa using this

theorem nsq_eq_dot (v : Fin n → ℂ) : ((nsq v : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast; rfl

theorem nsq_eq_of_gram {M N : Matrix (Fin n) (Fin n) ℂ} (h : Mᴴ * M = Nᴴ * N) (y : Fin n → ℂ) :
    nsq (M *ᵥ y) = nsq (N *ᵥ y) := by
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((nsq (M *ᵥ y) : ℝ) : ℂ) = star y ⬝ᵥ ((Mᴴ * M) *ᵥ y) := by
    intro M
    rw [nsq_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  exact Complex.ofReal_injective (by rw [key, key, h])

theorem nsq_cj (h1 : Uᴴ * U = 1) (d : Fin n → ℝ) (y : Fin n → ℂ) :
    nsq (cj U d *ᵥ y) = ∑ i, d i ^ 2 * ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by
  have hU : ∀ w : Fin n → ℂ, nsq (U *ᵥ w) = nsq w := fun w => by
    have := nsq_eq_of_gram (M := U) (N := 1) (by simp [h1]) w
    simpa using this
  have e : cj U d *ᵥ y = U *ᵥ (diagonal (fun i => (d i : ℂ)) *ᵥ (Uᴴ *ᵥ y)) := by
    simp only [cj, mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hU]
  simp only [nsq, mulVec_diagonal, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem core {J G H : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hHG : H * G = 1) (hGH : G * H = 1)
    (hJc : Jᴴ = J) (hHJ : H = J * Gᴴ * J) (hT : (Hᴴ * H).IsHermitian) (f : ℝ → ℝ) (α β : ℝ)
    (hf : ∀ l : ℝ, 0 < l → (f l = -1 ∨ f l = 0 ∨ f l = 1) ∧ f l⁻¹ = - f l)
    (hα : ∀ i, f (hT.eigenvalues i) = -1 → α ≤ hT.eigenvalues i)
    (hβ : ∀ i, f (hT.eigenvalues i) = 0 → β⁻¹ ≤ hT.eigenvalues i)
    (hne : ∃ i, f (hT.eigenvalues i) ≠ 0) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, Aᴴ = A ∧ A * A * A = A ∧ A ≠ 0 ∧ J * A = -A * J ∧
      ∀ y : Fin n → ℂ, α * nsq (Pm A *ᵥ y) + β⁻¹ * nsq (Pz A *ᵥ y) ≤ nsq (H *ᵥ y) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ, U = (hT.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
    ⟨_, rfl⟩
  have h1 : Uᴴ * U = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff'.1 hT.eigenvectorUnitary.2
  have h2 : U * Uᴴ = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff.1 hT.eigenvectorUnitary.2
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin n → ℝ, lam = hT.eigenvalues := ⟨_, rfl⟩
  rw [← hlam] at hα hβ hne
  have hTc : Hᴴ * H = cj U lam := by
    have := hT.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, ← hUdef, ← hlam, Matrix.star_eq_conjTranspose] at this
    exact this
  have hTG : (Hᴴ * H) * (G * Gᴴ) = 1 := by
    calc _ = Hᴴ * (H * G) * Gᴴ := by simp only [Matrix.mul_assoc]
      _ = (G * H)ᴴ := by rw [hHG, Matrix.mul_one, conjTranspose_mul]
      _ = 1 := by rw [hGH, conjTranspose_one]
  have hHinj : Function.Injective H.mulVec := by
    intro x y hxy
    have h := congrArg (fun v => G *ᵥ v) hxy
    simpa only [mulVec_mulVec, hGH, one_mulVec] using h
  have hpos : ∀ i, 0 < lam i := fun i => by
    rw [hlam]
    open scoped ComplexOrder in
    exact (Matrix.PosDef.conjTranspose_mul_self H hHinj).eigenvalues_pos i
  have hinv : cj U (fun i => (lam i)⁻¹) = G * Gᴴ := by
    have e : cj U (fun i => (lam i)⁻¹) * (Hᴴ * H) = 1 := by
      rw [hTc, cj_mul h1, ← cj_one (U := U) h2]
      congr 1; funext i; exact inv_mul_cancel₀ (hpos i).ne'
    calc _ = cj U (fun i => (lam i)⁻¹) * ((Hᴴ * H) * (G * Gᴴ)) := by rw [hTG, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
  have hHc : Hᴴ = J * G * J := by
    rw [hHJ]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJc, Matrix.mul_assoc]
  have hJT : J * (Hᴴ * H) = (G * Gᴴ) * J := by
    rw [hHc, hHJ]
    calc _ = (J * J) * G * (J * J) * Gᴴ * J := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.one_mul, Matrix.mul_one]

  let S : Finset ℝ := Finset.univ.image lam ∪ Finset.univ.image (fun i => (lam i)⁻¹)
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Function.injective_id.injOn) hx
  have hp1 : ∀ i, p.eval (lam i) = f (lam i) := fun i =>
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hp2 : ∀ i, p.eval (lam i)⁻¹ = - f (lam i) := fun i => by
    rw [hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun i => (lam i)⁻¹) (Finset.mem_univ i)))]
    exact (hf _ (hpos i)).2
  obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ, a = fun i => f (lam i) := ⟨_, rfl⟩
  have ha3 : ∀ i, a i = -1 ∨ a i = 0 ∨ a i = 1 := fun i => by
    rw [ha]; exact (hf _ (hpos i)).1
  have hA : Polynomial.aeval (Hᴴ * H) p = cj U a := by
    rw [hTc, cj_aeval h1 h2, ha]; congr 1; funext i; exact hp1 i
  have hAi : Polynomial.aeval (G * Gᴴ) p = - cj U a := by
    rw [← hinv, cj_aeval h1 h2, ← cj_neg, ha]; congr 1; funext i; exact hp2 i
  have hPm : Pm (cj U a) = cj U (fun i => (1 / 2 : ℝ) * (a i * a i + - a i)) := by
    rw [cj_smul, cj_add, cj_neg, ← cj_mul h1, ← sub_eq_add_neg]
    simp only [Pm]
    congr 1
    push_cast; rfl
  have hPz : Pz (cj U a) = cj U (fun i => 1 + - (a i * a i)) := by
    rw [cj_add, cj_neg, ← cj_mul h1, cj_one h2, ← sub_eq_add_neg]
    rfl
  refine ⟨cj U a, cj_conj a, ?_, ?_, ?_, ?_⟩
  · rw [cj_mul h1, cj_mul h1]
    congr 1; funext i
    rcases ha3 i with h | h | h <;> rw [h] <;> norm_num
  · intro h0
    obtain ⟨i, hi⟩ := hne
    exact hi (by have := cj_eq_zero h1 h0 i; rwa [ha] at this)
  · have := aeval_intertwine hJT p
    rwa [hA, hAi] at this
  · intro y
    have hH : nsq (H *ᵥ y) = nsq (cj U (fun i => Real.sqrt (lam i)) *ᵥ y) := by
      refine nsq_eq_of_gram ?_ y
      rw [cj_conj, cj_mul h1, hTc]
      congr 1; funext i; exact (Real.mul_self_sqrt (hpos i).le).symm
    rw [hPm, hPz, hH, nsq_cj h1, nsq_cj h1, nsq_cj h1, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hc : 0 ≤ ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by positivity
    rw [Real.sq_sqrt (hpos i).le]
    have hfa : a i = f (lam i) := by rw [ha]
    rcases ha3 i with h | h | h
    · have h' := hα i (by rw [← hfa, h])
      rw [h]
      nlinarith
    · have h' := hβ i (by rw [← hfa, h])
      rw [h]
      nlinarith
    · rw [h]
      have := hpos i
      have h3 : 0 ≤ lam i * ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by positivity
      nlinarith

end GlobalTheory.CompanionTheory.UGeo.SpecGrad


open GlobalTheory.CompanionTheory.UGeo.SpecGrad in
theorem GlobalTheory.CompanionTheory.UGeo.SpecGrad.grading_of_spectral :
    ∀ (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) (f : ℝ → ℝ) (α β : ℝ), (∀ l : ℝ, 0 < l → (f l = -1 ∨ f l = 0 ∨ f l = 1) ∧ f l⁻¹ = - f l) → (∀ i, f (hT.eigenvalues i) = -1 → α ≤ hT.eigenvalues i) → (∀ i, f (hT.eigenvalues i) = 0 → β⁻¹ ≤ hT.eigenvalues i) → (∃ i, f (hT.eigenvalues i) ≠ 0) → ∃ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' ∧ ∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM g⁻¹ *ᵥ y) := by
  intro n ε g hT f α β hf hα hβ hne
  have hHG : S7.toM g⁻¹ * S7.toM g = 1 := by
    show ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val = 1
    simp
  have hGH : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val * ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
    simp
  obtain ⟨A, hc, h3, h0, hJ, hy⟩ := core (J := Formalism.REAL.Jm ε) (Formalism.REAL.Jm_mul_self ε) hHG hGH
    (Formalism.REAL.Jm_conjTranspose ε) (S7.toM_inv ε g) hT f α β hf hα hβ hne
  refine ⟨A, ⟨?_, hc, h3, h0⟩, hy⟩
  show Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0
  rw [hc, hJ, Matrix.neg_mul, add_neg_cancel]
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HilbertSchmidtProjectionBound
section
open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

noncomputable section

namespace GlobalTheory.CompanionTheory.UGeo.Est

variable {n : ℕ}

theorem nsq_nonneg (y : Fin n → ℂ) : 0 ≤ nsq y := Finset.sum_nonneg fun _ _ => by positivity

theorem nsq_add_le (u v : Fin n → ℂ) : nsq (u + v) ≤ 2 * nsq u + 2 * nsq v := by
  simp only [nsq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (u i) (v i)
  have h1 : ‖(u + v) i‖ ^ 2 ≤ (‖u i‖ + ‖v i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖u i‖ - ‖v i‖)]

theorem nsq_mulVec_le (M : Matrix (Fin n) (Fin n) ℂ) (y : Fin n → ℂ) :
    nsq (M *ᵥ y) ≤ Formalism.REAL.hs M * nsq y := by
  have e1 : nsq (M *ᵥ y) = ∑ i, ‖(M *ᵥ y) i‖ ^ 2 := rfl
  have e2 : Formalism.REAL.hs M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := rfl
  rw [e1, e2, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(M *ᵥ y) i‖ ≤ ∑ j, ‖M i j‖ * ‖y j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M i j‖) (fun j => ‖y j‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem nsq_eq_re (y : Fin n → ℂ) : nsq y = (star y ⬝ᵥ y).re := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  simp [← Complex.ofReal_pow]

theorem nsq_unitary {U : Matrix (Fin n) (Fin n) ℂ} (h : Uᴴ * U = 1) (y : Fin n → ℂ) :
    nsq (U *ᵥ y) = nsq y := by
  rw [nsq_eq_re, nsq_eq_re, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.one_mulVec]

theorem nsq_proj {P : Matrix (Fin n) (Fin n) ℂ} (h1 : Pᴴ = P) (h2 : P * P = P) (y : Fin n → ℂ) :
    nsq (P *ᵥ y) = (star y ⬝ᵥ (P *ᵥ y)).re := by
  rw [nsq_eq_re, Matrix.star_mulVec, h1, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2]

theorem nsq_three {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGrad ε A) (y : Fin n → ℂ) :
    nsq y = nsq (Pm A *ᵥ y) + nsq (Pz A *ᵥ y) + nsq (Pp A *ᵥ y) := by
  rw [nsq_proj (Pm_conj hA) (Pm_idem hA), nsq_proj (Pz_conj hA) (Pz_idem hA),
    nsq_proj (Pp_conj hA) (Pp_idem hA), ← Complex.add_re, ← Complex.add_re, ← dotProduct_add,
    ← dotProduct_add, ← Matrix.add_mulVec, ← Matrix.add_mulVec, sum_proj, Matrix.one_mulVec, nsq_eq_re]

theorem mulVec_col (M P : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    (M *ᵥ fun i => P i j) = fun i => (M * P) i j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

theorem hs_eq_cols (M : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs M = ∑ j, nsq (fun i => M i j) := by
  simp only [Formalism.REAL.hs, nsq]
  exact Finset.sum_comm

theorem hs_mul_le_of_cols {X P : Matrix (Fin n) (Fin n) ℂ} {c : ℝ}
    (h : ∀ j, nsq (X *ᵥ fun i => P i j) ≤ c * nsq (fun i => P i j)) :
    Formalism.REAL.hs (X * P) ≤ c * Formalism.REAL.hs P := by
  rw [hs_eq_cols, hs_eq_cols P, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← mulVec_col]
  exact h j

theorem hs_proj_le {P : Matrix (Fin n) (Fin n) ℂ} (h1 : Pᴴ = P) (h2 : P * P = P) :
    Formalism.REAL.hs P ≤ n :=
  UGeo.hs_proj_le h1 h2

theorem hs_sub_comm (M N : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs (M - N) = Formalism.REAL.hs (N - M) := by
  simp only [Formalism.REAL.hs, Matrix.sub_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [norm_sub_rev]

theorem est : ∀ (n : ℕ) (ε : Fin n → Bool) (A₀ A' : Matrix (Fin n) (Fin n) ℂ) (α β : ℝ) (x : PSub ε A₀) (k : S7.KG ε), IsGrad ε A₀ → IsGrad ε A' → Formalism.REAL.hs (Pm A₀ - Pm A') ≤ 1 / 4 → Formalism.REAL.hs (Pp A₀ - Pp A') ≤ 1 / 4 → 1 ≤ β → β ≤ α → (∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM ((x : S7.UJ ε) * (k : S7.UJ ε))⁻¹ *ᵥ y)) → Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Pm A₀) ≤ 4 * n / α ∧ Formalism.REAL.hs (S7.toM (x : S7.UJ ε) * Pz A₀) ≤ 4 * n * β := by
  intro n ε A₀ A' α β x k h0 h' hm hp hβ hβα hyp
  have hβ0 : 0 < β := by linarith
  have hα0 : 0 < α := by linarith
  have hβi0 : 0 ≤ β⁻¹ := (inv_pos.2 hβ0).le
  have hβi1 : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ
  have hXiX : S7.toM ((x : S7.UJ ε)⁻¹) * S7.toM (x : S7.UJ ε) = 1 := by
    show (((x : S7.UJ ε)⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val *
      (((x : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val = 1
    simp
  have hU : (S7.toM ((k : S7.UJ ε)⁻¹))ᴴ * S7.toM ((k : S7.UJ ε)⁻¹) = 1 := by
    have hk : ((k : S7.UJ ε)⁻¹) ∈ S7.KG ε := (S7.KG ε).inv_mem k.2
    exact Unitary.star_mul_self_of_mem hk.1
  have H : ∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤
      nsq (S7.toM ((x : S7.UJ ε)⁻¹) *ᵥ y) := by
    intro y
    have h := hyp y
    have e : S7.toM ((x : S7.UJ ε) * (k : S7.UJ ε))⁻¹ =
        S7.toM ((k : S7.UJ ε)⁻¹) * S7.toM ((x : S7.UJ ε)⁻¹) := by
      rw [_root_.mul_inv_rev]; rfl
    rwa [e, ← Matrix.mulVec_mulVec, nsq_unitary hU] at h
  have s1 : ∀ y : Fin n → ℂ, Pm A₀ *ᵥ y = y → α / 4 * nsq y ≤ nsq (S7.toM ((x : S7.UJ ε)⁻¹) *ᵥ y) := by
    intro y hy
    have e : Pm A' *ᵥ y + (Pm A₀ - Pm A') *ᵥ y = y := by
      rw [Matrix.sub_mulVec, hy]; abel
    have h1 := nsq_add_le (Pm A' *ᵥ y) ((Pm A₀ - Pm A') *ᵥ y)
    rw [e] at h1
    have h2 := nsq_mulVec_le (Pm A₀ - Pm A') y
    have h3 := mul_le_mul_of_nonneg_right hm (nsq_nonneg y)
    have h4 : 0 ≤ β⁻¹ * nsq (Pz A' *ᵥ y) := mul_nonneg hβi0 (nsq_nonneg _)
    have h5 := H y
    have hN : nsq y / 4 ≤ nsq (Pm A' *ᵥ y) := by linarith
    have h6 := mul_le_mul_of_nonneg_left hN hα0.le
    linarith
  have s2 : ∀ y : Fin n → ℂ, Pp A₀ *ᵥ y = 0 →
      3 / 4 * β⁻¹ * nsq y ≤ nsq (S7.toM ((x : S7.UJ ε)⁻¹) *ᵥ y) := by
    intro y hy
    have e : Pp A' *ᵥ y = (Pp A' - Pp A₀) *ᵥ y := by
      rw [Matrix.sub_mulVec, hy, sub_zero]
    have h1 := nsq_mulVec_le (Pp A' - Pp A₀) y
    rw [← e, hs_sub_comm] at h1
    have h2 := mul_le_mul_of_nonneg_right hp (nsq_nonneg y)
    have h3 := nsq_three h' y
    have hN : 3 / 4 * nsq y ≤ nsq (Pm A' *ᵥ y) + nsq (Pz A' *ᵥ y) := by linarith
    have h4 := mul_le_mul_of_nonneg_left hN hβi0
    have h5 : β⁻¹ * nsq (Pm A' *ᵥ y) ≤ α * nsq (Pm A' *ᵥ y) :=
      mul_le_mul_of_nonneg_right (by linarith) (nsq_nonneg _)
    have h6 := H y
    nlinarith
  constructor
  · have hc : ∀ j, nsq (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pm A₀ i j) ≤ 4 / α * nsq (fun i => Pm A₀ i j) := by
      intro j
      have hv : (fun i => Pm A₀ i j) ∈ Vm A₀ := mem_Vm.2 ⟨Pi.single j 1, by ext i; simp⟩
      have hy := stable_of_keeps x.2.1 _ hv
      obtain ⟨z, hz⟩ := mem_Vm.1 hy
      have hP : Pm A₀ *ᵥ (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pm A₀ i j) =
          S7.toM (x : S7.UJ ε) *ᵥ fun i => Pm A₀ i j := by
        rw [← hz, Matrix.mulVec_mulVec, Pm_idem h0]
      have h := s1 _ hP
      rw [Matrix.mulVec_mulVec, hXiX, Matrix.one_mulVec] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ hα0]
      linarith
    have h1 := hs_mul_le_of_cols hc
    have h2 := hs_proj_le (Pm_conj h0) (Pm_idem h0)
    have h3 : 4 / α * Formalism.REAL.hs (Pm A₀) ≤ 4 / α * n :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ = 4 * n / α := by ring
  · have hc : ∀ j, nsq (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pz A₀ i j) ≤ 4 * β * nsq (fun i => Pz A₀ i j) := by
      intro j
      have hv : (fun i => Pz A₀ i j) ∈ Wm A₀ := by
        rw [mem_Wm, mulVec_col, Pp_Pz h0]
        rfl
      have hy := mem_Wm.1 (stable_of_keeps x.2.2 _ hv)
      have h := s2 _ hy
      rw [Matrix.mulVec_mulVec, hXiX, Matrix.one_mulVec] at h
      have h1 := mul_le_mul_of_nonneg_left h hβ0.le
      have e : β * (3 / 4 * β⁻¹ * nsq (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pz A₀ i j)) =
          3 / 4 * nsq (S7.toM (x : S7.UJ ε) *ᵥ fun i => Pz A₀ i j) := by
        field_simp
      rw [e] at h1
      have h2 : 0 ≤ β * nsq (fun i => Pz A₀ i j) := mul_nonneg hβ0.le (nsq_nonneg _)
      nlinarith
    have h1 := hs_mul_le_of_cols hc
    have h2 := hs_proj_le (Pz_conj h0) (Pz_idem h0)
    have h3 : 4 * β * Formalism.REAL.hs (Pz A₀) ≤ 4 * β * n :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    calc _ ≤ _ := h1
      _ ≤ _ := h3
      _ = 4 * n * β := by ring

end GlobalTheory.CompanionTheory.UGeo.Est
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TraceElementsActByGelfandValues
section

end

