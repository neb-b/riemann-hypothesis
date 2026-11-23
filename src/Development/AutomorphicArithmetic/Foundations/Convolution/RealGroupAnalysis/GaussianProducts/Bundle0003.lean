module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatInv
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance

variable {F : Type} [Field F] [NumberField F]

private theorem one_int (h : (Fin 1 → A F) → ℂ) :
    ∫ a, h a ∂(adeleMeasurePi F) = ∫ s : A F, h (fun _ => s) ∂(adeleMeasure F) :=
  ((measurePreserving_funUnique (adeleMeasure F) (Fin 1)).symm.integral_comp' h).symm

private theorem reindex_mem {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι)
    {f : (κ → A F) → ℂ} (hf : f ∈ schwartzBruhatPi (K := F) (ι := κ)) :
    (fun x : ι → A F => f (x ∘ e)) ∈ schwartzBruhatPi (K := F) (ι := ι) := by
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi
    ((1 : Matrix ι ι F).submatrix e id) ((1 : Matrix ι ι F).submatrix id e)
    (by rw [Matrix.submatrix_mul_equiv]; simp) (by
      ext i j
      simp [Matrix.mul_apply, Matrix.one_apply]) hf
  convert h using 2
  rename_i x
  congr 1
  ext k
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

private def eS : Fin 4 ≃ Fin 3 ⊕ Fin 1 where
  toFun := ![.inl 0, .inr 0, .inl 1, .inl 2]
  invFun := Sum.elim ![0, 2, 3] fun _ => 1
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    rintro (i | i)
    · fin_cases i <;> rfl
    · fin_cases i; rfl

private theorem slice_mem {φ : V4 F → ℂ} (hφ : φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (v : V4 F) :
    (fun y : Fin 1 → A F => φ (Function.update v 1 (y 0))) ∈ schwartzBruhatPi (K := F) (ι := Fin 1) := by
  have h1 := reindex_mem (F := F) eS hφ
  have h2 := GroundTheory.Heights₂.Theta.schwartzBruhatPi_sumElim_mem h1 ![v 0, v 2, v 3]
  convert h2 using 2
  rename_i y
  congr 1
  ext i
  fin_cases i <;> simp [eS, Function.update]

end UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance

open UpperTheory.ConvolutionTheory.R2.G.FourierHatInvariance in
theorem UpperTheory.ConvolutionTheory.R2.G.hatInv :
    ∀ (F : Type) [Field F] [NumberField F] (φ : S4 F) (v : V4 F), hat (hat φ.1) v = φ.1 (Function.update v 1 (-v 1)) := by
  intro F _ _ φ v
  have hg := slice_mem φ.2 v
  have inv := congrFun (adelicFourierPi_adelicFourierPi hg) (fun _ => v 1)
  rw [adelicFourierPi, one_int] at inv
  have key : ∀ s : A F, hat φ.1 (Function.update v 1 (-s)) =
      adelicFourierPi F (fun y : Fin 1 → A F => φ.1 (Function.update v 1 (y 0))) (fun _ => s) := by
    intro s
    rw [hat, adelicFourierPi, one_int]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [ψ]
  rw [hat, ← integral_neg_eq_self]
  refine Eq.trans ?_ (inv.trans ?_)
  · refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [key]
    simp [ψ]
  · simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatMeas
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

namespace UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem hat_n {D : Dat F E} (W : Weil D) (Ψ : S4 F) (ξ : Fin 2 → F) (b : A F) (g : G1 F) :
    hat (W.Om (nU b * g) Ψ).1 (pt ξ) = ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) * hat (W.Om g Ψ).1 (pt ξ) := by
  have hH := (_root_.UpperTheory.ConvolutionTheory.R2.hatSt F E D W).n b (W.Om g Ψ) (pt ξ)
  have e : W.Om (nU b * g) Ψ = W.Om (nU b) (W.Om g Ψ) := by rw [map_mul]; rfl
  have e1 : pt ξ 1 + b * pt ξ 0 = pt ξ 1 := by simp [pt]
  have e3 : b * (pt ξ 2 ^ 2 - rt D.δ * pt ξ 3 ^ 2) = rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b := by
    simp only [pt, rt, map_sub, map_mul, map_pow]
    simp
    ring
  rw [e, hH, e1, Function.update_eq_self, e3]

private theorem hat_meas {D : Dat F E} (W : Weil D) (Ψ : S4 F) (v : V4 F) :
    Measurable fun g : G1 F => hat (W.Om g Ψ).1 v := by
  have hc : Continuous fun p : G1 F × A F =>
      (W.Om p.1 Ψ).1 (Function.update v 1 p.2) * ψ (-(p.2 * v 1)) := by
    have h2 : Continuous fun s : A F => Function.update v 1 s := continuous_const.update 1 continuous_id
    have h1 : Continuous fun p : G1 F × A F => (p.1, Function.update v 1 p.2) :=
      continuous_fst.prodMk (h2.comp continuous_snd)
    have h3 : Continuous fun s : A F => ψ (-(s * v 1)) :=
      Pp.cont_ψ.comp ((continuous_id.mul continuous_const).neg)
    exact ((W.cont Ψ).comp h1).mul (h3.comp continuous_snd)
  exact (hc.stronglyMeasurable.integral_prod_right (ν := adeleMeasure F)).measurable

end UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage

open UpperTheory.ConvolutionTheory.R2.G.UnipotentAverage in
theorem UpperTheory.ConvolutionTheory.R2.G.uxAv :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (f : GL (Fin 2) (A F) → ℂ), Pp.Lf f → ∀ φ h ξ, NInv (ux W f φ h ξ) ∧ av (ux W f φ h ξ) = wx W f φ h ξ ∧
    ∀ b g, ‖ux W f φ h ξ (nU b * g)‖ = ‖f (gl (nU b * g) * dM (nu F h))‖ * ‖hat (W.Om g (W.L h φ)).1 (pt ξ)‖ := by
  intro F E _ _ _ _ _ _ _ D W f hf φ h ξ
  have hgl : ∀ x y : G1 F, gl (x * y) = gl x * gl y := fun x y => map_mul _ x y
  have hux : ∀ b g, ux W f φ h ξ (nU b * g) =
      f (gl (nU b) * (gl g * dM (nu F h))) * ψ (rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * b) *
        hat (W.Om g (W.L h φ)).1 (pt ξ) := by
    intro b g
    simp only [ux]
    rw [hat_n, hgl, mul_assoc (gl (nU b)), mul_assoc]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · have h1 : Continuous fun g : G1 F => f (gl g * dM (nu F h)) :=
      hf.1.comp (_root_.UpperTheory.ConvolutionTheory.R2.M.continuous_gl.mul continuous_const)
    exact h1.measurable.mul (hat_meas W _ _)
  · intro c g
    rw [hux]
    have e : rt (ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * rt c = rt ((ξ 0 ^ 2 - D.δ * ξ 1 ^ 2) * c) := (map_mul _ _ _).symm
    have e2 : f (gl (nU (rt c)) * (gl g * dM (nu F h))) = f (gl g * dM (nu F h)) := by
      obtain ⟨γ, hγ⟩ := Pp.rat_n c
      rw [← hγ, hf.2]
    rw [e, Pp.ψ_rt, mul_one, e2]
    rfl
  · funext g
    simp only [av, wx]
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun b => hux b g)
  · intro b g
    simp only [ux]
    rw [hat_n, norm_mul, norm_mul, Pp.norm_ψ, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Hermite1Integrable
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private lemma hermite1_integrable (n : ℕ) :
    Integrable (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos (s := (n : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  refine (h.ofReal (𝕜 := ℂ)).congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Real.rpow_natCast]
  show ((s ^ n * Real.exp (-Real.pi * s ^ 2) : ℝ) : ℂ) = _
  push_cast
  rfl

private lemma hermite1_norm (s x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (s * x))‖ = 1 := by
  have : (2 * Real.pi * Complex.I * (s * x) : ℂ) = ((2 * Real.pi * (s * x) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma hermite1_integrable' (n : ℕ) (x : ℝ) :
    Integrable (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
      Complex.exp (2 * Real.pi * Complex.I * (s * x))) := by
  refine (hermite1_integrable n).mono
    (Continuous.aestronglyMeasurable (by fun_prop)) (Filter.Eventually.of_forall fun s => ?_)
  rw [norm_mul, hermite1_norm, mul_one]

private lemma hermite1_rec (n : ℕ) (x : ℝ) :
    2 * (Real.pi : ℂ) * ∫ s : ℝ, (s : ℂ) ^ (n + 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
      (n : ℂ) * (∫ s : ℝ, (s : ℂ) ^ (n - 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x))) +
      2 * Real.pi * Complex.I * x * ∫ s : ℝ, (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) := by
  set A : ℝ → ℂ := fun s => (s : ℂ) ^ (n - 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hA
  set B : ℝ → ℂ := fun s => (s : ℂ) ^ (n + 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hB
  set C : ℝ → ℂ := fun s => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * (s * x)) with hC
  have iA : Integrable A := hermite1_integrable' _ x
  have iB : Integrable B := hermite1_integrable' _ x
  have iC : Integrable C := hermite1_integrable' _ x
  have hd : ∀ s : ℝ, HasDerivAt C
      ((n : ℂ) * A s - 2 * Real.pi * B s + 2 * Real.pi * Complex.I * x * C s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
    have h2 := h1.pow n
    have h3 := ((h1.pow 2).const_mul (-(Real.pi : ℂ))).cexp
    have h4 := ((h1.mul_const (x : ℂ)).const_mul (2 * (Real.pi : ℂ) * Complex.I)).cexp
    refine ((h2.mul h3).mul h4).congr_deriv ?_
    simp only [A, B, C, Pi.pow_apply, Pi.mul_apply]
    push_cast
    simp only [Nat.add_one_sub_one, pow_one]
    ring
  have key := integral_eq_zero_of_hasDerivAt_of_integrable hd
    (((iA.const_mul _).sub (iB.const_mul _)).add (iC.const_mul _)) iC
  have e : ∫ s, ((n : ℂ) * A s - 2 * Real.pi * B s + 2 * Real.pi * Complex.I * x * C s) =
      (n : ℂ) * (∫ s, A s) - 2 * Real.pi * (∫ s, B s) + 2 * Real.pi * Complex.I * x * ∫ s, C s := by
    have a1 := integral_add (μ := volume) (f := fun s => (n : ℂ) * A s - 2 * Real.pi * B s)
      (g := fun s => 2 * Real.pi * Complex.I * x * C s)
      ((iA.const_mul _).sub (iB.const_mul _)) (iC.const_mul _)
    have a2 := integral_sub (μ := volume) (f := fun s => (n : ℂ) * A s)
      (g := fun s => 2 * Real.pi * B s) (iA.const_mul _) (iB.const_mul _)
    rw [a1, a2, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [e] at key
  linear_combination -key

private lemma hermite1_zero (x : ℝ) :
    ∫ s : ℝ, (s : ℂ) ^ 0 * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) *
      Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
    Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) := by
  have h := fourierIntegral_gaussian (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos)
    (2 * Real.pi * x : ℂ)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : ((Real.pi : ℂ) / Real.pi) ^ (1 / 2 : ℂ) = 1 := by simp [hpi]
  have e2 : -(2 * Real.pi * x : ℂ) ^ 2 / (4 * Real.pi) = -(Real.pi : ℂ) * (x : ℂ) ^ 2 := by
    field_simp
    ring
  rw [e1, one_mul, e2] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [pow_zero, one_mul]
  rw [mul_comm]
  congr 2
  ring

theorem UpperTheory.ConvolutionTheory.R2.G.hermite1 :
    ∀ n : ℕ, Integrable (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2)) ∧ ∃ P : Polynomial ℂ, ∀ x : ℝ,
    ∫ s : ℝ, (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
    P.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have two : ∀ n : ℕ,
      (∃ P : Polynomial ℂ, ∀ x : ℝ,
        ∫ s : ℝ, (s : ℂ) ^ n * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
        P.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) ∧
      (∃ P : Polynomial ℂ, ∀ x : ℝ,
        ∫ s : ℝ, (s : ℂ) ^ (n + 1) * Complex.exp (-(Real.pi : ℂ) * (s : ℂ) ^ 2) * Complex.exp (2 * Real.pi * Complex.I * (s * x)) =
        P.eval (x : ℂ) * Complex.exp (-(Real.pi : ℂ) * (x : ℂ) ^ 2)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨⟨1, fun x => ?_⟩, ⟨Polynomial.C Complex.I * Polynomial.X, fun x => ?_⟩⟩
      · simpa using hermite1_zero x
      · have h := hermite1_rec 0 x
        rw [hermite1_zero x] at h
        simp only [Nat.cast_zero, zero_mul, zero_add] at h
        simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        have h2 : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hpi
        apply mul_left_cancel₀ h2
        rw [h]
        ring
    | succ n ih =>
      obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := ih
      refine ⟨⟨Q, hQ⟩, ⟨Polynomial.C (1 / (2 * (Real.pi : ℂ))) *
        (Polynomial.C ((n + 1 : ℕ) : ℂ) * P +
          Polynomial.C (2 * Real.pi * Complex.I) * Polynomial.X * Q), fun x => ?_⟩⟩
      have h := hermite1_rec (n + 1) x
      simp only [Nat.add_sub_cancel] at h
      rw [hP x, hQ x] at h
      have h2 : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hpi
      apply mul_left_cancel₀ h2
      rw [h]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
      field_simp
  intro n
  exact ⟨hermite1_integrable n, (two n).1⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Kern
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

private def eqv (F : Type) : (Fin 2 → F) × (Fin 2 → F) ≃ (Fin 4 → F) where
  toFun p := ![p.1 0, p.1 1, p.2 0, p.2 1]
  invFun x := (![x 0, x 1], ![x 2, x 3])
  left_inv p := by
    rcases p with ⟨a, b⟩
    refine Prod.ext ?_ ?_ <;> (ext i; fin_cases i <;> rfl)
  right_inv x := by ext i; fin_cases i <;> rfl

theorem UpperTheory.ConvolutionTheory.R2.G.kern :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (σ : Rw F → Matrix.SpecialLinearGroup (Fin 2) F), M.RowSec σ → ∀ φ : S4 F,
    Th φ.1 = ThRow 0 0 φ.1 + ∑' r : Rw F, ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) := by
  intro F E _ _ _ _ _ _ _ D W σ hσ φ
  have H := UpperTheory.ConvolutionTheory.R2.hatSt F E D W
  have hs : Summable (fun ξ : Fin 4 → F => hat φ.1 fun i => rt (ξ i)) :=
    (poisson_of_mem_schwartzBruhatPi (H.mem φ)).1.of_norm
  have hs2 : Summable (fun p : (Fin 2 → F) × (Fin 2 → F) => hat φ.1 ![rt (p.1 0), rt (p.1 1), rt (p.2 0), rt (p.2 1)]) := by
    have h := ((eqv F).summable_iff).2 hs
    refine h.congr fun p => ?_
    simp only [Function.comp]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hrowsum : Summable (fun r : Fin 2 → F => ThRow (rt (r 0)) (rt (r 1)) φ.1) := hs2.prod
  have hth : Th φ.1 = ∑' r : Fin 2 → F, ThRow (rt (r 0)) (rt (r 1)) φ.1 := by
    rw [H.th φ, Th, ← (eqv F).tsum_eq, ]
    have : (fun p : (Fin 2 → F) × (Fin 2 → F) => hat φ.1 fun i => rt ((eqv F) p i)) =
        fun p => hat φ.1 ![rt (p.1 0), rt (p.1 1), rt (p.2 0), rt (p.2 1)] := by
      funext p
      congr 1
      ext i
      fin_cases i <;> rfl
    rw [this, hs2.tsum_prod]
    rfl
  have hr : ∀ r : Rw F, ThRow (rt (r.1 0)) (rt (r.1 1)) φ.1 =
      ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) := by
    intro r
    have hv : (![0, 1] : Fin 2 → F) ᵥ* (σ r).1 = r.1 := by
      rw [← hσ r]
      ext j
      simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have h := H.row (σ r) ![0, 1] φ
    rw [hv] at h
    rw [← h]
    simp [ThRow, pt]
  rw [hth, hrowsum.tsum_eq_add_tsum_ite (0 : Fin 2 → F)]
  have h0 : ThRow (rt ((0 : Fin 2 → F) 0)) (rt ((0 : Fin 2 → F) 1)) φ.1 = ThRow 0 0 φ.1 := by simp
  rw [h0]
  refine congrArg _ ?_
  have h1 := tsum_subtype {r : Fin 2 → F | r ≠ 0} (fun r => ThRow (rt (r 0)) (rt (r 1)) φ.1)
  have h2 : ∑' r : Rw F, ∑' ξ : Fin 2 → F, hat (W.Om (ratS F (σ r)) φ).1 (pt ξ) =
      ∑' r : {r : Fin 2 → F | r ≠ 0}, ThRow (rt (r.1 0)) (rt (r.1 1)) φ.1 :=
    tsum_congr fun r => (hr r).symm
  rw [h2, h1]
  refine tsum_congr fun r => ?_
  by_cases h : r = 0
  · simp [h]
  · simp [h]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.LamRight
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors


open scoped Pointwise in
private theorem lint_add {F : Type} [Field F] [NumberField F] {h : A F → ℝ≥0∞}
    (hh : ∀ (k : F) x, h (rt k + x) = h x) (a : A F) :
    ∫⁻ b in fundamentalSet F, h (b + a) ∂(adeleMeasure F) = ∫⁻ b in fundamentalSet F, h b ∂(adeleMeasure F) := by
  have hD := isAddFundamentalDomain_fundamentalSet F
  haveI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
    refine (Set.countable_range (fun ξ : F => (rt ξ : A F))).mono ?_ |>.to_subtype
    rintro _ ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  have hT := hD.vadd_of_comm a
  have hp := measurePreserving_add_right (adeleMeasure F) a
  have e : (fun b : A F => b + a) ⁻¹' (a +ᵥ fundamentalSet F) = fundamentalSet F := by
    ext x
    simp [Set.mem_vadd_set, add_comm]
  have h1 := hp.setLIntegral_comp_preimage_emb (MeasurableEquiv.addRight a).measurableEmbedding h (a +ᵥ fundamentalSet F)
  rw [e] at h1
  rw [h1]
  refine hT.setLIntegral_eq hD h ?_
  rintro ⟨_, k, rfl⟩ x
  exact hh k x

theorem UpperTheory.ConvolutionTheory.R2.G.lamRight :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : Meas F) (u : G1 F → ℂ), NInv u → ∀ (c : ℂ) (g₀ : G1 F), abelian₂ M (fun g => c * u (g * g₀)) = ‖c‖ₑ * abelian₂ M u := by
  intro F _ _ _ M₀ u hu c g₀
  have hnU : Measurable (nU : A F → G1 F) := M.continuous_nU.measurable
  set U : G1 F → ℝ≥0∞ := fun g => ∫⁻ b in fundamentalSet F, ‖u (nU b * g)‖ₑ ∂(adeleMeasure F) with hUdef
  have hUm : Measurable U :=
    Measurable.lintegral_prod_right' (ν := (adeleMeasure F).restrict (fundamentalSet F))
      (f := fun q : G1 F × A F => ‖u (nU q.2 * q.1)‖ₑ)
      (hu.1.comp ((hnU.comp measurable_snd).mul measurable_fst)).enorm
  have hUi : ∀ b g, U (nU b * g) = U g := by
    intro a g
    have := lint_add (F := F) (h := fun b => ‖u (nU b * g)‖ₑ) (fun k x => by
      simp only [M.nU_add, mul_assoc, hu.2]) a
    simp only [hUdef]
    rw [← this]
    simp only [M.nU_add, mul_assoc]
  have hc : ‖c‖ₑ ≠ ⊤ := enorm_ne_top
  have hJ := M.lintegral_unipotent_quotient_right_invariant F M₀ U hUm hUi g₀
  have hL : abelian₂ M₀ (fun g => c * u (g * g₀)) = ‖c‖ₑ * M.J0 M₀ (fun g => U (g * g₀)) := by
    simp only [abelian₂, M.J0]
    rw [← lintegral_const_mul' _ _ hc]
    refine lintegral_congr fun p => ?_
    have : ∫⁻ b in fundamentalSet F, ‖c * u (nU b * (mD p.1 * p.2) * g₀)‖ₑ ∂(adeleMeasure F) =
        ‖c‖ₑ * U (mD p.1 * p.2 * g₀) := by
      simp only [hUdef, enorm_mul, mul_assoc]
      exact lintegral_const_mul' _ _ hc
    rw [this]
    ring
  rw [hL, hJ]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomChar
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.momChar :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X →
    (∀ R : ℝ, Integrable (fun ω => ((Real.exp (R * ∑ i, |X ω i|) : ℝ) : ℂ) * ρ ω) ν) →
    (∀ (n : ℕ) (t : ι → ℝ), ∫ ω, ((∑ i, t i * X ω i : ℝ) : ℂ) ^ n * ρ ω ∂ν = 0) →
    ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hint hmom t
  have hym : Measurable (fun ω => ∑ i, t i * X ω i) :=
    Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp hX).const_mul (t i))
  have hρ : Integrable ρ ν := by simpa using hint 0
  have hbound : ∀ ω, |∑ i, t i * X ω i| ≤ (∑ i, |t i|) * ∑ i, |X ω i| := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => |X ω j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
      (abs_nonneg _)
  have hdom : Integrable (fun ω => Real.exp |∑ i, t i * X ω i| * ‖ρ ω‖) ν := by
    refine (hint (∑ i, |t i|)).norm.mono'
      (((Real.measurable_exp.comp (continuous_abs.measurable.comp hym)).aestronglyMeasurable).mul hρ.norm.aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    simp only [norm_mul, norm_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [abs_norm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbound ω)) (norm_nonneg (ρ ω))
  have hsum := hasSum_integral_of_dominated_convergence (μ := ν)
    (F := fun (n : ℕ) ω => (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω)
    (f := fun ω => Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
    (fun (n : ℕ) ω => |∑ i, t i * X ω i| ^ n / (n.factorial : ℝ) * ‖ρ ω‖)
    (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · have hz : (fun n : ℕ => ∫ ω, (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω ∂ν)
        = fun _ => 0 := by
      funext n
      have : ∀ ω, (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) * ρ ω
          = (Complex.I ^ n / (n.factorial : ℂ)) * (((∑ i, t i * X ω i : ℝ) : ℂ) ^ n * ρ ω) := by
        intro ω; rw [mul_pow]; ring
      simp_rw [this]
      rw [integral_const_mul, hmom n t, mul_zero]
    rw [hz] at hsum
    exact hsum.unique hasSum_zero |>.symm ▸ rfl
  · have hc : Measurable (fun ω => ((∑ i, t i * X ω i : ℝ) : ℂ)) := Complex.measurable_ofReal.comp hym
    exact ((((hc.mul_const Complex.I).pow_const n).div_const _).aestronglyMeasurable).mul hρ.aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Complex.norm_natCast, Real.norm_eq_abs]
  · exact Eventually.of_forall fun ω =>
      (Real.summable_pow_div_factorial _).mul_right _
  · have : (fun ω => ∑' n : ℕ, |∑ i, t i * X ω i| ^ n / (n.factorial : ℝ) * ‖ρ ω‖)
        = fun ω => Real.exp |∑ i, t i * X ω i| * ‖ρ ω‖ := by
      funext ω
      rw [tsum_mul_right, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    rw [this]; exact hdom
  · refine Eventually.of_forall fun ω => ?_
    have := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)).mul_right (ρ ω)
    rwa [← Complex.exp_eq_exp_ℂ] at this
end

