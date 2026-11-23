module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Vol
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.LiftCentre
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Growth
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem dM_one' {F : Type} [Field F] [NumberField F] : dM (1 : (A F)ˣ) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dM]

private theorem growth_alg (a b c d V : ℝ) (n m : ℕ) :
    (a * (2 * (c * d)) ^ n) * (b * (4 * (c * d) ^ 2) ^ m * V) =
      a * (2 * c) ^ n * (b * (4 * c ^ 2) ^ m * V) * d ^ (n + 2 * m) := by
  ring

theorem UpperTheory.ConvolutionTheory.R2.Ff.growth :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), Growth W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  obtain ⟨f', hf', φ', hφ', y₀, k, -, hφk, -, hred⟩ := UpperTheory.ConvolutionTheory.R2.Ff.redLift F E D W M π f hf φ hφ h
  obtain ⟨ω, hωc, hω⟩ := UpperTheory.ConvolutionTheory.R2.cen F π
  obtain ⟨σ, τ, -, -, hdec⟩ := UpperTheory.ConvolutionTheory.R2.Ff.dec F E D
  obtain ⟨C₁, N₁, hC₁⟩ := (UpperTheory.ConvolutionTheory.R2.Ff.omGrowth F E D).2 ω hωc
  have hht := (UpperTheory.ConvolutionTheory.R2.Ff.htLe E).2
  have hφ'F : φ' ∈ Fock D.δ := hφ'
  obtain ⟨B, N₂, hB⟩ := UpperTheory.ConvolutionTheory.R2.Ff.thBound F E D W π f' hf' φ' hφ'F {1} isCompact_singleton
  have hv : M.μ M.D < ⊤ := UpperTheory.ConvolutionTheory.R2.Ff.vol F M
  have hV0 : 0 ≤ M.μ.real M.D := measureReal_nonneg
  have hone : ∀ z, UpperTheory.ConvolutionTheory.R2.Ff.One F z →
      ‖UpperTheory.ConvolutionTheory.R2.lift W M f'.1 φ' (infGL E 2 z)‖ ≤ |B| * UpperTheory.ConvolutionTheory.R2.Ff.Ht z ^ N₂ * M.μ.real M.D := by
    intro z hz
    have hz' : nu F (infGL E 2 z) = 1 := hz
    unfold UpperTheory.ConvolutionTheory.R2.lift
    rw [hz', dM_one']
    refine norm_setIntegral_le_of_norm_le_const hv fun g _ => ?_
    refine (hB z hz g 1 rfl).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg (by linarith [(hht z).1]) _)
  have hcen := (UpperTheory.ConvolutionTheory.R2.equiv F E D W M π f' hf' φ').2 ω (hω f' hf')
  have hy₀ := (hht y₀).1
  refine ⟨|C₁| * (2 * (6 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀)) ^ N₁ *
    (|B| * (4 * (6 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀) ^ 2) ^ N₂ * M.μ.real M.D), N₁ + 2 * N₂, fun y => ?_⟩
  rw [hred φ y, ← hφk]
  obtain ⟨e, h1, h2, h3⟩ := hdec (y₀ * y)
  have hH1 := (hht (y₀ * y)).1
  have hy := hht y
  have hmul := (hht y₀).2.2 y
  have hhy : 0 ≤ GlobalTheory.CuspRep.height y := by linarith [hy.1, hy.2.1]
  have hc0 : 0 ≤ 6 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀ := by linarith
  have hHle : UpperTheory.ConvolutionTheory.R2.Ff.Ht (y₀ * y) ≤ 6 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀ * GlobalTheory.CuspRep.height y := by
    have : 2 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀ * UpperTheory.ConvolutionTheory.R2.Ff.Ht y ≤
        2 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀ * (3 * GlobalTheory.CuspRep.height y) :=
      mul_le_mul_of_nonneg_left hy.2.1 (by linarith)
    linarith
  have hH0 : 0 ≤ UpperTheory.ConvolutionTheory.R2.Ff.Ht (y₀ * y) := by linarith
  have hS0 : 0 ≤ 1 + ‖(σ (y₀ * y)).val‖ + ‖(σ (y₀ * y))⁻¹.val‖ := by
    have n0 := norm_nonneg (σ (y₀ * y)).val
    have n1 := norm_nonneg (σ (y₀ * y))⁻¹.val
    linarith
  have a1 : ‖((ω (ideleNorm F E (infId E (σ (y₀ * y)))) : ℂˣ) : ℂ)‖ ≤
      |C₁| * (2 * (6 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀ * GlobalTheory.CuspRep.height y)) ^ N₁ := by
    refine (hC₁ _).trans ?_
    refine mul_le_mul (le_abs_self _) ?_ (pow_nonneg hS0 _) (abs_nonneg _)
    exact pow_le_pow_left₀ hS0 (h3.trans (by linarith)) _
  have a2 : ‖UpperTheory.ConvolutionTheory.R2.lift W M f'.1 φ' (infGL E 2 (τ (y₀ * y)))‖ ≤
      |B| * (4 * (6 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀ * GlobalTheory.CuspRep.height y) ^ 2) ^ N₂ * M.μ.real M.D := by
    refine (hone _ h1).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hV0
    refine pow_le_pow_left₀ (by linarith [(hht (τ (y₀ * y))).1]) (h2.trans ?_) _
    have := pow_le_pow_left₀ hH0 hHle 2
    linarith
  rw [e, hcen, norm_mul]
  calc _ ≤ (|C₁| * (2 * (6 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀ * GlobalTheory.CuspRep.height y)) ^ N₁) *
        (|B| * (4 * (6 * UpperTheory.ConvolutionTheory.R2.Ff.Ht y₀ * GlobalTheory.CuspRep.height y) ^ 2) ^ N₂ * M.μ.real M.D) :=
        mul_le_mul a1 a2 (norm_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) (mul_nonneg hc0 hhy)) _))
    _ = _ := growth_alg _ _ _ _ _ _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RowBoundH
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.rowBoundH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2), RowBoundH W π := by
  intro F E _ _ _ _ _ _ _ D W π f hf φ hφ h x
  obtain ⟨y, hy, φ₁, hφ₁, m, e⟩ := redH F E D W h φ hφ
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  obtain ⟨B₁, hB₁⟩ := rowMaj F E D W φ₁ hφ₁ y hy c hc
  have hC : IsCompact ((fun k : G1 F => gl k * ((gl m)⁻¹ * x)) '' KK F) :=
    (iwa F).1.image (M.continuous_gl.mul continuous_const)
  obtain ⟨B₂, hB₂⟩ := (UpperTheory.ConvolutionTheory.R2.decay F π f hf).2 _ hC c hc 1
  have hinv := (thMeas F E D W (W.L (infGL E 2 y) φ₁)).2.2.2.1
  refine ⟨B₂ * B₁, fun g => ?_⟩
  have e1 : W.Om g (W.L h φ) = W.Om (g * m) (W.L (infGL E 2 y) φ₁) := by
    simpa using e g 1
  obtain ⟨γ, b, a, k, hk, ek, ha⟩ := hred (g * m)
  have e2 : ThRow 0 0 (W.Om g (W.L h φ)).1 =
      ThRow 0 0 (W.Om (nU b * mD a * k) (W.L (infGL E 2 y) φ₁)).1 := by
    rw [e1, ← ek]
    exact (hinv γ (g * m)).symm
  have e3 : f.1 (gl g * x) = f.1 (gl (nU b * mD a) * (gl k * ((gl m)⁻¹ * x))) := by
    have e4 : gl (nU b * mD a) * (gl k * ((gl m)⁻¹ * x)) =
        ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) * (gl g * x) := by
      have e5 : ratGL F 2 (Matrix.SpecialLinearGroup.toGL γ) = gl (ratS F γ) := Units.ext rfl
      rw [← mul_assoc, ← gl_mul, ← mul_assoc, ← ek, gl_mul, gl_mul, e5]
      group
    rw [e4]
    exact ((π.cusp _ hf).1.left _ _).symm
  rw [norm_mul, e2, e3]
  have hp := M.ab_pos a
  have h1 := hB₁ b a k hk ha
  have h2 := hB₂ b a _ ⟨k, hk, rfl⟩ ha
  calc _ ≤ (B₂ * (ab a)⁻¹ ^ 1) * (B₁ * ab a) :=
        mul_le_mul h2 h1 (norm_nonneg _) ((norm_nonneg _).trans h2)
    _ = B₂ * B₁ := by field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ThBoundH
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem one_mul_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] {y y' : GL (Fin 2) (Cinf E)} (hy : Ff.One F y) (hy' : Ff.One F y') :
    Ff.One F (y * y') := by
  unfold Ff.One nu at *
  rw [map_mul, map_mul, map_mul, hy, hy', _root_.one_mul]

theorem UpperTheory.ConvolutionTheory.R2.Ff.thBoundH :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (π : TR.CuspSub F 2), ThBoundH W π := by
  intro F E _ _ _ _ _ _ _ D W π f hf φ hφ h C hC C' hC' hOne
  obtain ⟨y₀, hy₀, φ₁, hφ₁, m, hred⟩ := redH F E D W h φ hφ
  obtain ⟨B, N, hB⟩ := thBound F E D W π f hf φ₁ hφ₁ ((fun x => (gl m)⁻¹ * x) '' C)
    (hC.image (continuous_const.mul continuous_id))
  obtain ⟨M, hM⟩ := (hC'.image (htLe E).1).bddAbove
  refine ⟨|B| * (2 * Ht y₀ * |M|) ^ N, fun g x hx y hy => ?_⟩
  have e : gl g * x = gl (g * m) * ((gl m)⁻¹ * x) := by
    rw [gl_mul, _root_.mul_assoc, mul_inv_cancel_left]
  rw [hred g y, e]
  refine (hB _ (one_mul_one hy₀ (hOne y hy)) (g * m) _ ⟨x, hx, rfl⟩).trans ?_
  have h1 : 1 ≤ Ht (y₀ * y) := ((htLe E).2 _).1
  have h2 : Ht (y₀ * y) ≤ 2 * Ht y₀ * Ht y := ((htLe E).2 y₀).2.2 y
  have h3 : Ht y ≤ |M| := (hM ⟨y, hy, rfl⟩).trans (le_abs_self M)
  have h4 : 1 ≤ Ht y₀ := ((htLe E).2 y₀).1
  have h5 : Ht (y₀ * y) ≤ 2 * Ht y₀ * |M| :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (by linarith))
  have h6 : Ht (y₀ * y) ^ N ≤ (2 * Ht y₀ * |M|) ^ N :=
    pow_le_pow_left₀ (by linarith) h5 N
  calc B * Ht (y₀ * y) ^ N ≤ |B| * Ht (y₀ * y) ^ N :=
        mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    _ ≤ |B| * (2 * Ht y₀ * |M|) ^ N := mul_le_mul_of_nonneg_left h6 (abs_nonneg B)
end

