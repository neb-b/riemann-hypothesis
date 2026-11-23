module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0057
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0017
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0060
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0065

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InverseTransformHolomorphicLines
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.InvLine

theorem integrable_exp_neg_abs_plane {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ × ℝ => Real.exp (-c * |t.1|) * Real.exp (-c * |t.2|)) :=
  (integrable_exp_neg_mul_abs hc).mul_prod (integrable_exp_neg_mul_abs hc)

theorem dot_add_smul (p v : ℂ × ℂ) (τ : ℂ) (t : ℝ × ℝ) :
    dot (p + τ • v) t = dot p t + τ * dot v t := by
  simp [dot]
  ring

theorem norm_cexp_dot (l : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖Complex.exp (dot l t)‖ = Real.exp (rdot (l.1.re, l.2.re) t) := by
  rw [Complex.norm_exp]
  simp [dot, rdot]

theorem norm_dot_le (v : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖dot v t‖ ≤ (‖v.1‖ + ‖v.2‖) * (|t.1| + |t.2|) := by
  have h1 : ‖dot v t‖ ≤ ‖v.1‖ * |t.1| + ‖v.2‖ * |t.2| := by
    refine (norm_add_le _ _).trans ?_
    simp [norm_mul]
  have := norm_nonneg v.1
  have := norm_nonneg v.2
  have := abs_nonneg t.1
  have := abs_nonneg t.2
  nlinarith [mul_nonneg (norm_nonneg v.1) (abs_nonneg t.2), mul_nonneg (norm_nonneg v.2) (abs_nonneg t.1)]

theorem le_two_div_mul_exp {ε s : ℝ} (hε : 0 < ε) : s ≤ 2 / ε * Real.exp (ε / 2 * s) := by
  have h := Real.add_one_le_exp (ε / 2 * s)
  have h2 : s = 2 / ε * (ε / 2 * s) := by field_simp
  have h3 : ε / 2 * s ≤ Real.exp (ε / 2 * s) := by linarith
  calc s = 2 / ε * (ε / 2 * s) := h2
    _ ≤ _ := by gcongr

theorem inv_differentiable_line : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by
  intro X _ _ _ T _ φ hφ hc g p v τ₀
  obtain ⟨ε, hε, U, hU, M, hM⟩ := hφ ((p + τ₀ • v).1.re, (p + τ₀ • v).2.re) g
  have hgU : g ∈ U := mem_of_mem_nhds hU
  have hA : 0 < ‖v.1‖ + ‖v.2‖ + 1 := by positivity
  have hr : 0 < ε / (‖v.1‖ + ‖v.2‖ + 1) := div_pos hε hA
  have hre : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ w : ℂ, ‖w‖ ≤ ‖v.1‖ + ‖v.2‖ + 1 →
      ∀ q : ℂ, |(q + τ * w).re - (q + τ₀ * w).re| ≤ ε := by
    intro τ hτ w hw q
    have h1 : (q + τ * w).re - (q + τ₀ * w).re = ((τ - τ₀) * w).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im]
      ring
    rw [h1]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h2 : ‖τ - τ₀‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) := by
      have := Metric.mem_ball.1 hτ
      rw [dist_eq_norm] at this
      exact this.le
    calc ‖τ - τ₀‖ * ‖w‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) * (‖v.1‖ + ‖v.2‖ + 1) := by gcongr
      _ = ε := by field_simp
  have key : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖φ t g‖ ≤ M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
        * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    refine hM _ ?_ ?_ g hgU t
    · exact hre τ hτ v.1 (by linarith [norm_nonneg v.2]) p.1
    · exact hre τ hτ v.2 (by linarith [norm_nonneg v.1]) p.2
  have hFn : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖Complex.exp (dot (p + τ • v) t) • φ t g‖ ≤ |M| * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    rw [norm_smul, norm_cexp_dot]
    have h1 := key τ hτ t
    have h2 := Real.exp_pos (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
    calc _ ≤ Real.exp (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t) *
          (M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
            * Real.exp (-ε * (|t.1| + |t.2|))) := by gcongr
      _ = M * Real.exp (-ε * (|t.1| + |t.2|)) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ _ := by gcongr; exact le_abs_self M
  have hcont : ∀ τ : ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot (p + τ • v) t) • φ t g := by
    intro τ
    refine Continuous.smul ?_ (hc g)
    simp only [dot]
    fun_prop
  have hdotc : Continuous fun t : ℝ × ℝ => dot v t := by
    unfold dot
    fun_prop
  have hint : Integrable (fun t : ℝ × ℝ => Complex.exp (dot (p + τ₀ • v) t) • φ t g) :=
    (integrable_and_norm_integral_le X (fun t => φ t g) (p + τ₀ • v) ε M hε (hc g)
      (fun t => hM _ (by simp [hε.le]) (by simp [hε.le]) g hgU t)).1
  have hbound : Integrable (fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|))) :=
    (integrable_exp_neg_abs_plane (half_pos hε)).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun (τ : ℂ) (t : ℝ × ℝ) => Complex.exp (dot (p + τ • v) t) • φ t g)
    (F' := fun (τ : ℂ) (t : ℝ × ℝ) => dot v t • (Complex.exp (dot (p + τ • v) t) • φ t g))
    (x₀ := τ₀) (s := Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)))
    (bound := fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)))
    (Metric.ball_mem_nhds _ hr)
    (Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
    hint
    (Continuous.aestronglyMeasurable (Continuous.smul hdotc (hcont τ₀)))
    (ae_of_all _ fun t τ hτ => by
      rw [norm_smul]
      have h1 := norm_dot_le v t
      have h2 := hFn τ hτ t
      have h3 := le_two_div_mul_exp (s := |t.1| + |t.2|) hε
      have h4 : Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h5 : Real.exp (ε / 2 * (|t.1| + |t.2|)) * Real.exp (-ε * (|t.1| + |t.2|))
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h4, ← h5]
      calc _ ≤ ((‖v.1‖ + ‖v.2‖) * (2 / ε * Real.exp (ε / 2 * (|t.1| + |t.2|)))) *
            (|M| * Real.exp (-ε * (|t.1| + |t.2|))) := by
            refine mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity)
            gcongr
        _ = _ := by ring)
    hbound
    (ae_of_all _ fun t τ _ => by
      have h1 : HasDerivAt (fun τ : ℂ => Complex.exp (dot (p + τ • v) t))
          (Complex.exp (dot (p + τ • v) t) * dot v t) τ := by
        have h2 : HasDerivAt (fun τ : ℂ => dot p t + τ * dot v t) (dot v t) τ := by
          simpa using ((hasDerivAt_id τ).mul_const (dot v t)).const_add (dot p t)
        have h3 := h2.cexp
        simp only [← dot_add_smul] at h3
        exact h3
      have h4 := h1.smul_const (φ t g)
      rw [smul_smul, mul_comm]
      exact h4)
  exact (hd.2.differentiableAt).const_smul (((2 * Real.pi) ^ 2 : ℂ)⁻¹)

end GlobalTheory.CompanionTheory.TubeFourier.InvLine
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumCongrInvariance
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegCov

section Ring

variable {A : Type} [CommRing A]

theorem cT_mul (τ : A →+* A) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) A)
    (y : Matrix (Fin b) (Fin c) A) : cT τ (x * y) = cT τ y * cT τ x := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one (τ : A →+* A) {a : ℕ} : cT τ (1 : Matrix (Fin a) (Fin a) A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.transpose_one]

theorem cT_cT (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (x : Matrix (Fin a) (Fin b) A) :
    cT τ (cT τ x) = x := by
  unfold cT
  ext i j
  exact hτ (x i j)

def covEquiv (τ : A →+* A) {m n : ℕ} (G G' : Matrix (Fin n) (Fin n) A)
    (P P' : Matrix (Fin m) (Fin m) A) (hG : G * G' = 1) (hG' : G' * G = 1)
    (hP : P * P' = 1) (hP' : P' * P = 1) :
    Matrix (Fin m) (Fin n) A ≃ Matrix (Fin m) (Fin n) A where
  toFun x := P' * x * cT τ G'
  invFun y := P * y * cT τ G
  left_inv x := by
    have h : cT τ G' * cT τ G = 1 := by rw [← cT_mul, hG, cT_one]
    calc P * (P' * x * cT τ G') * cT τ G = (P * P') * x * (cT τ G' * cT τ G) := by
          simp only [Matrix.mul_assoc]
      _ = x := by rw [hP, h, Matrix.one_mul, Matrix.mul_one]
  right_inv y := by
    have h : cT τ G * cT τ G' = 1 := by rw [← cT_mul, hG', cT_one]
    calc P' * (P * y * cT τ G) * cT τ G' = (P' * P) * y * (cT τ G * cT τ G') := by
          simp only [Matrix.mul_assoc]
      _ = y := by rw [hP', h, Matrix.one_mul, Matrix.mul_one]

theorem eq_of_conj (τ : A →+* A) {n : ℕ} {h D g g' : Matrix (Fin n) (Fin n) A}
    (hg : g * g' = 1) (hD : cT τ g * h * g = D) : h = cT τ g' * D * g' := by
  have hg2 : cT τ g' * cT τ g = 1 := by rw [← cT_mul, hg, cT_one]
  rw [← hD]
  calc h = (cT τ g' * cT τ g) * h * (g * g') := by
        rw [hg2, hg, Matrix.one_mul, Matrix.mul_one]
    _ = cT τ g' * (cT τ g * h * g) * g' := by simp only [Matrix.mul_assoc]

theorem trace_cov (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {m n : ℕ}
    (D g' : Matrix (Fin n) (Fin n) A) (E p' : Matrix (Fin m) (Fin m) A)
    (x : Matrix (Fin m) (Fin n) A) :
    Matrix.trace ((cT τ g' * D * g') * (cT τ x * (cT τ p' * E * p') * x)) =
      Matrix.trace (D * (cT τ (p' * x * cT τ g') * E * (p' * x * cT τ g'))) := by
  rw [cT_mul, cT_mul, cT_cT τ hτ]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (cT τ g')]
  simp only [Matrix.mul_assoc]

end Ring

section Red

variable {R : Type} [CommRing R]

theorem red_mul (ϖ : R) (k : ℕ) {a b c : ℕ} (x : Matrix (Fin a) (Fin b) R)
    (y : Matrix (Fin b) (Fin c) R) : red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  unfold red
  exact Matrix.map_mul

theorem red_cT (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) : red ϖ k (cT σ x) = cT (barσ σ ϖ hf k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ hf k (x j i)).symm

theorem red_one (ϖ : R) (k : ℕ) {a : ℕ} : red ϖ k (1 : Matrix (Fin a) (Fin a) R) = 1 := by
  unfold red
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem barσ_inv (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (hσ : ∀ a, σ (σ a) = a) (k : ℕ)
    (a : R ⧸ lev ϖ k) : barσ σ ϖ hf k (barσ σ ϖ hf k a) = a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [barσ_mk, barσ_mk, hσ]

end Red

theorem gauss_cov (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ)
    (hσ : ∀ a, σ (σ a) = a) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ)
    (m n : ℕ) (h D g g' : Matrix (Fin n) (Fin n) R) (S E p p' : Matrix (Fin m) (Fin m) R)
    (hg : g * g' = 1) (hg' : g' * g = 1) (hp : p * p' = 1) (hp' : p' * p = 1)
    (hD : cT σ g * h * g = D) (hE : cT σ p * S * p = E) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
        χ (Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) =
      ∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k),
        χ (Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  have hh : h = cT σ g' * D * g' := eq_of_conj σ hg hD
  have hS : S = cT σ p' * E * p' := eq_of_conj σ hp hE
  have rg : red ϖ k g * red ϖ k g' = 1 := by rw [← red_mul, hg, red_one]
  have rg' : red ϖ k g' * red ϖ k g = 1 := by rw [← red_mul, hg', red_one]
  have rp : red ϖ k p * red ϖ k p' = 1 := by rw [← red_mul, hp, red_one]
  have rp' : red ϖ k p' * red ϖ k p = 1 := by rw [← red_mul, hp', red_one]
  refine Fintype.sum_equiv
    (covEquiv (barσ σ ϖ hf k) (red ϖ k g) (red ϖ k g') (red ϖ k p) (red ϖ k p') rg rg' rp rp')
    _ _ ?_
  intro x
  have key : Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)) =
      Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) (red ϖ k p' * x * cT (barσ σ ϖ hf k) (red ϖ k g')) *
        red ϖ k E * (red ϖ k p' * x * cT (barσ σ ϖ hf k) (red ϖ k g')))) := by
    rw [hh, hS, red_mul, red_mul, red_mul, red_mul, red_cT σ ϖ hf, red_cT σ ϖ hf]
    exact trace_cov (barσ σ ϖ hf k) (barσ_inv σ ϖ hf hσ k) (red ϖ k D) (red ϖ k g') (red ϖ k E)
      (red ϖ k p') x
  exact congrArg (⇑χ) key

end GlobalTheory.CompanionTheory.SiegCov
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixGaussSumDiagonalFactor
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.GaussProd

theorem sum_pi_prod {ι Q : Type} [Fintype ι] [DecidableEq ι] [Fintype Q] (g : ι → Q → ℂ) :
    (∑ y : ι → Q, ∏ i, g i (y i)) = ∏ i, ∑ w, g i w := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem chi_sum {ι Q : Type} [AddCommMonoid Q] (χ : AddChar Q ℂ) (s : Finset ι) (g : ι → Q) :
    χ (∑ i ∈ s, g i) = ∏ i ∈ s, χ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem trace_diag {Q : Type} [CommRing Q] (τ : Q →+* Q) (m n : ℕ) (d : Fin n → Q) (e : Fin m → Q)
    (y : Matrix (Fin m) (Fin n) Q) :
    Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)) =
      ∑ i, ∑ l, e l * d i * (τ (y l i) * y l i) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  ring

theorem red_diagonal {R : Type} [CommRing R] (ϖ : R) (k n : ℕ) (D : Fin n → R) :
    red ϖ k (Matrix.diagonal D) =
      Matrix.diagonal fun i => Ideal.Quotient.mk (lev ϖ k) (D i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [red]
  · simp [red, Matrix.diagonal_apply_ne _ h]

theorem sum_fun_prod {Q : Type} [Fintype Q] (m n : ℕ) (f : Fin n → Fin m → Q → ℂ) :
    (∑ y : Fin m → Fin n → Q, ∏ l, ∏ i, f i l (y l i)) = ∏ i, ∏ l, ∑ w, f i l w := by
  have h1 : ∀ l, ∑ v : Fin n → Q, ∏ i, f i l (v i) = ∏ i, ∑ w, f i l w := fun l =>
    sum_pi_prod (fun i => f i l)
  have h2 := sum_pi_prod (ι := Fin m) (Q := Fin n → Q) (fun l v => ∏ i, f i l (v i))
  simp only [h1] at h2
  rw [Finset.prod_comm]
  exact h2

theorem gauss_gen {Q : Type} [CommRing Q] [Fintype Q] (τ : Q →+* Q) (χ : AddChar Q ℂ) (m n : ℕ)
    (d : Fin n → Q) (e : Fin m → Q) :
    (∑ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y)))) =
      ∏ i : Fin n, ∏ l : Fin m, ∑ w : Q, χ (e l * d i * (τ w * w)) := by
  let f : Fin n → Fin m → Q → ℂ := fun i l w => χ (e l * d i * (τ w * w))
  have hterm : ∀ y : Matrix (Fin m) (Fin n) Q,
      χ (Matrix.trace (Matrix.diagonal d * (cT τ y * Matrix.diagonal e * y))) =
        ∏ l, ∏ i, f i l (y l i) := by
    intro y
    rw [trace_diag, chi_sum, Finset.prod_comm (s := Finset.univ) (t := Finset.univ)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [chi_sum]
  exact (Fintype.sum_equiv Matrix.of.symm _ _ fun y => hterm y).trans (sum_fun_prod m n f)

theorem gauss_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R), (∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k (Matrix.diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (Matrix.diagonal E) * y)))) = ∏ i : Fin n, ∏ l : Fin m, ∑ w : R ⧸ lev ϖ k, χ (Ideal.Quotient.mk (lev ϖ k) (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  intro R _ σ ϖ hf k _ χ m n D E
  have h := gauss_gen (barσ σ ϖ hf k) χ m n (fun i => Ideal.Quotient.mk (lev ϖ k) (D i))
    (fun l => Ideal.Quotient.mk (lev ϖ k) (E l))
  simp only [red_diagonal, map_mul]
  exact h

end GlobalTheory.CompanionTheory.GaussProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeetOverHypersurfaceOfGermStatement
section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meet_over_hypersurface_of_germ : FiniteFibreGermIntegral.Statement → IrreducibleGermMeetOverHypersurface.Statement := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral | exact GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemPowSmulTopIff
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Completion

theorem mem_pow_smul_top_iff {T : Type} [CommRing T] (t y : T) (n : ℕ) :
    y ∈ ((Ideal.span {t}) ^ n • ⊤ : Submodule T T) ↔ y ∈ Ideal.span {t ^ n} := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

theorem aic_of_isCompl : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T),
    IsCompl π g → π ∈ nonZeroDivisors B → AIC B → VAL π → AIC T := by
  intro B _ T _ π g hc hπ hA hV P hP hd
  have step := _root_.GlobalTheory.CompanionTheory.AicStep.aic_step B T π g hc hπ hA hV P hP hd
  set d := P.natDegree with hdd
  set t := g π with ht

  let S : ℕ → Type := fun M => {a : B // P.eval (g a) ∈ Ideal.span {t ^ (d * M)}}
  have s0 : P.eval (g 0) ∈ Ideal.span {t ^ (d * 0)} := by simp
  let seq : (M : ℕ) → S M := fun M =>
    Nat.rec (motive := S) ⟨0, s0⟩ (fun M a => ⟨(step M a.1 a.2).choose, (step M a.1 a.2).choose_spec.2⟩) M
  have hstep : ∀ M, (seq (M + 1)).1 - (seq M).1 ∈ Ideal.span {π ^ M} := fun M =>
    (step M (seq M).1 (seq M).2).choose_spec.1
  let a : ℕ → T := fun M => g (seq M).1
  have hg : ∀ M, a (M + 1) - a M ∈ Ideal.span {t ^ M} := by
    intro M
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton'.1 (hstep M)
    refine Ideal.mem_span_singleton'.2 ⟨g c, ?_⟩
    simp only [a, ht, ← map_pow, ← map_mul, hc', map_sub]
  have hpow : ∀ {m n : ℕ}, m ≤ n → Ideal.span {t ^ n} ≤ Ideal.span {t ^ m} := by
    intro m n hmn
    rw [Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow t hmn
  have hcau : ∀ {m n : ℕ}, m ≤ n → a n - a m ∈ Ideal.span {t ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := Ideal.add_mem _ ih (hpow hmn (hg n))
      simpa using this
  have hpre := hc.compl.toIsPrecomplete
  obtain ⟨x, hx⟩ := hpre.prec' a (fun {m n} hmn => by
    rw [SModEq.sub_mem, mem_pow_smul_top_iff]
    have := Ideal.neg_mem_iff _ |>.2 (hcau hmn)
    simpa using this)
  refine ⟨x, ?_⟩
  have hz : ∀ n, P.eval x ∈ Ideal.span {t ^ n} := by
    intro n
    have h1 : a n - x ∈ Ideal.span {t ^ n} := by
      have := hx n
      rwa [SModEq.sub_mem, mem_pow_smul_top_iff] at this
    have h2 : P.eval (a n) ∈ Ideal.span {t ^ n} :=
      hpow (Nat.le_mul_of_pos_left n hd) (seq n).2
    have h3 : a n - x ∣ P.eval (a n) - P.eval x := Polynomial.sub_dvd_eval_sub _ _ _
    have h4 : P.eval (a n) - P.eval x ∈ Ideal.span {t ^ n} := Ideal.mem_of_dvd _ h3 h1
    have := Ideal.sub_mem _ h2 h4
    simpa using this
  have := hc.compl.toIsHausdorff.haus' (P.eval x) (fun n => by
    rw [SModEq.zero, mem_pow_smul_top_iff]
    exact hz n)
  exact this

end GlobalTheory.CompanionTheory.Completion
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonApproximationLocalToGlobalStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newton_approximation_local_to_global : ∀ {S : Type} [CommRing S] (ϖ : S), (∀ m : Ideal S, m.IsMaximal → Step (Ideal.Quotient.mk (compI m) ϖ)) → Step ϖ := by
  first | exact @GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal | exact GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal | (intros; apply GlobalTheory.CompanionTheory.NewtonStep.step_of_forall_maximal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionOffDiagonalIdentity
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem pfOrth : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ),
    Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k →
      1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  intro m d d' hinj i k hik
  have hi := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj i
  have hk := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj k
  have hne : d i - d k ≠ 0 := sub_ne_zero.mpr fun h => hik (Sum.inl.inj (@hinj (Sum.inl i) (Sum.inl k) h))
  have hij : ∀ j, d i - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h =>
    Sum.inl_ne_inr (@hinj (Sum.inl i) (Sum.inr j) h)
  have hkj : ∀ j, d k - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h =>
    Sum.inl_ne_inr (@hinj (Sum.inl k) (Sum.inr j) h)
  have hdiff : ∑ j, pfR d d' j / (d i - d' j) - ∑ j, pfR d d' j / (d k - d' j) =
      -(d i - d k) * ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hij j, hkj j]
    ring
  have key : (d i - d k) * (1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j))) = 0 := by
    linear_combination hi - hk - hdiff
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

end GlobalTheory.CompanionTheory.RgHeFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectTensorProductStatement
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_tensor_product : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K → Pf p (B ⊗[A] K) := by
  first | exact @GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | exact GlobalTheory.CompanionTheory.PerfectRing.pf_tensor | (intros; apply GlobalTheory.CompanionTheory.PerfectRing.pf_tensor <;> assumption)
end

