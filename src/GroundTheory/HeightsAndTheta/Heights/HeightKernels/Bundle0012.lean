module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0005
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaSummandNorm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Real

noncomputable section

namespace KThetaSummandNorm

lemma im_dot_period {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) (w v : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (v i : ℂ))).im = w ⬝ᵥ (Y *ᵥ v) := by
  simp only [dotProduct, mulVec, periodMatrix, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_sum, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  simp

lemma im_dot_real {g : ℕ} (w c : Fin g → ℝ) :
    ((fun i => (w i : ℂ)) ⬝ᵥ fun i => (c i : ℂ)).im = 0 := by
  simp [dotProduct, Complex.im_sum]

lemma qf_add {g : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.IsSymm) (w u : Fin g → ℝ) :
    qf Y (w + u) = qf Y w + 2 * (w ⬝ᵥ (Y *ᵥ u)) + qf Y u := by
  have h : u ⬝ᵥ (Y *ᵥ w) = w ⬝ᵥ (Y *ᵥ u) := by
    rw [dotProduct_mulVec, ← vecMul_transpose, hY.eq, dotProduct_comm]
  simp only [qf, mulVec_add, dotProduct_add, add_dotProduct, h]
  ring

end KThetaSummandNorm

open KThetaSummandNorm in
theorem ThetaSummandNorm.proof : ThetaSummandNorm.Statement := by
  intro g X Y a b u₁ u₂ k hY
  set w : Fin g → ℝ := intVec k + a with hw
  have hW : (fun i => ((intVec k i + a i : ℝ) : ℂ)) = fun i => (w i : ℂ) := rfl
  have hzb : (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => (u₂ i : ℂ)) +
      (fun i => (b i : ℂ)) =
      periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ) := by
    ext i; simp [add_assoc]
  have hre : (π * Complex.I *
      ((fun i => (w i : ℂ)) ⬝ᵥ (periodMatrix X Y *ᵥ fun i => (w i : ℂ))) +
      2 * π * Complex.I * ((fun i => (w i : ℂ)) ⬝ᵥ
        (periodMatrix X Y *ᵥ (fun i => (u₁ i : ℂ)) + fun i => ((u₂ + b) i : ℂ)))).re =
      -π * qf Y w - 2 * π * (w ⬝ᵥ (Y *ᵥ u₁)) := by
    rw [dotProduct_add]
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im,
      im_dot_period, im_dot_real]
    simp only [qf]
    ring
  unfold thetaSummand
  rw [hW, hzb, Complex.norm_exp, hre, ← Real.exp_add]
  congr 1
  have : intVec k + a + u₁ = w + u₁ := rfl
  rw [this, qf_add Y hY w u₁]
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartCutoffEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def chartCutoff {D : ℕ} (k : ℕ) (y : Fin D → ℂ) : ℝ :=
  Real.smoothTransition (2 - (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2)

def ChartCutoffEnergy.Statement : Prop :=
  ∀ (n : ℕ) (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ), (∀ i, (T i).PosDef) →
    ∃ K : ℝ, ∀ k : ℕ,
      ∫ y : Fin (n + 1) → ℂ,
        ReciprocityTheory.AnForm.A.gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartDensityIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartDensityIntegrable.Statement : Prop :=
  ∀ (e : ℕ) (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef →
    Integrable (fun y : Fin e → ℂ => maDensity (fun _ : Fin e => hermChartPot M) y)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def chartMixedEnergy {e : ℕ} (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (k : ℕ) : ℝ :=
  ∫ y : Fin e → ℂ, (hermChartPot M y - hermChartPot N y) *
    maDensity (fun j : Fin e => if (j : ℕ) < k then hermChartPot M else hermChartPot N) y

def ChartEnergy.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef →
    ∑ k ∈ Finset.range (e + 1), chartMixedEnergy M N k =
      1 / 2 * (Real.log M.det.re - Real.log N.det.re) *
        chartMass (1 : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartHessCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder

noncomputable section

def ChartHessCompare.Statement : Prop :=
  ∀ (e : ℕ) (M N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ), M.PosDef → N.PosDef →
    ∃ C : ℝ, ∀ y : Fin e → ℂ, (cxHessian (hermChartPot M) y).PosDef ∧
      ((C : ℂ) • cxHessian (hermChartPot N) y - cxHessian (hermChartPot M) y).PosSemidef

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartIbpSymm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory
open scoped ComplexOrder

noncomputable section

def ChartIbpSymm.Statement : Prop :=
  ∀ (n : ℕ) (A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ),
    A.PosDef → B.PosDef → C.PosDef → D.PosDef → (∀ i, (T i).PosDef) →
    ∫ y : Fin (n + 1) → ℂ, (hermChartPot A y - hermChartPot B y) *
        maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
          fun i => hermChartPot (T i)) y =
      ∫ y : Fin (n + 1) → ℂ, (hermChartPot C y - hermChartPot D y) *
        maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
          fun i => hermChartPot (T i)) y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLocallyPrincipalCoprime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def LocallyPrincipalCoprime.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L) (M : AddSubgroup L) (ι : Type) [Fintype ι]
    (a : ι → L),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : L, x ∈ M ↔ ∃ y ∈ I, (β : L) * x = δ * y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsOrderIdealIndexExtension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def OrderIdealIndexExtension.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (B : Subring L), Module.Finite ℤ B →
    ∃ (r : ℕ) (s : B), s ≠ 0 ∧ Module.finrank ℚ L = r * Module.finrank ℤ B ∧
      (∀ I : Ideal B, I ≠ ⊥ → I.toAddSubgroup.index ≠ 0) ∧
      ∀ I : Ideal B, I ≠ ⊥ → (I.IsPrincipal ∨ I ⊔ Ideal.span {s} = ⊤) →
        (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup.relIndex
            (1 : Submodule (𝓞 L) L).toAddSubgroup = I.toAddSubgroup.index ^ r

end

end GroundTheory.Heights₂.Heights
end

