module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.HatFock
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExPhi
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.exPhi :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (a : (A F)ˣ), ∀ k ∈ KK F, ∃ φ ∈ Fock D.δ, hat (W.Om (mD a * k) φ).1 ![0, 1, 1, 0] ≠ 0 := by
  intro F E _ _ _ _ _ _ _ D W a k hk
  have H := hatSt F E D W
  have K := fockSt F E D W
  obtain ⟨χ, hχ, hne⟩ := (fockMul F D.δ).2 ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0]
  obtain ⟨φ₁, hφ₁, hh⟩ := hatSurj F D.δ D.neg χ hχ
  have hk' : k⁻¹ ∈ KK F := by
    have hs := (M.kkCpt F).1
    rw [hs] at hk ⊢
    exact inv_mem hk
  obtain ⟨U, hU, -, hC⟩ := K.om φ₁ hφ₁ {k⁻¹} isCompact_singleton (by rintro _ rfl; exact hk'.1)
  refine ⟨W.Om k⁻¹ φ₁, hU (hC _ rfl), ?_⟩
  have e : W.Om (mD a * k) (W.Om k⁻¹ φ₁) = W.Om (mD a) φ₁ := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
  have hv : (![a * (![0, 1, 1, 0] : V4 F) 0, ((a⁻¹ : (A F)ˣ) : A F) * (![0, 1, 1, 0] : V4 F) 1,
      a * (![0, 1, 1, 0] : V4 F) 2, a * (![0, 1, 1, 0] : V4 F) 3] : V4 F) =
      ![0, ((a⁻¹ : (A F)ˣ) : A F), (a : A F), 0] := by
    ext1 i
    fin_cases i <;> simp
  rw [e, H.m, hh, hv]
  have hab : ((ab a : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ab a := (IdeleGroup.ideleModule F a).2
    exact_mod_cast this.ne'
  exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) hab) hne
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.MomZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

theorem UpperTheory.ConvolutionTheory.R2.G.momZero :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ∀ f ∈ π.V, (∀ φ ∈ Fock D.δ, W1 W M f.1 φ 1 = 0) → ∀ φ ∈ Fock D.δ, ∀ p ∈ polyOn F (Fin 2), ∀ T : Set (Fin 2 → FiniteAdeleRing (𝓞 F) F), IsCompact T → IsOpen T →
    ∫ x : IdeleGroup F × G1 F, p (row (mD x.1 * x.2)) * T.indicator 1 (finPartPi (row (mD x.1 * x.2))) * iw (w1 W f.1 φ 1) x ∂M.ν = 0 := by
  intro F E _ _ _ _ _ _ _ D W M π f hf h0 φ hφ p hp T hc ho
  obtain ⟨φ', hφ', he⟩ := hatSurj F D.δ D.neg _
    ((fockMul F D.δ).1 _ (hatFock F D.δ _ (mem_fock.1 hφ)) p hp T hc ho)
  have hrow := rowMul F E D W (fun r => p r * T.indicator 1 (finPartPi r)) φ φ'
    (fun v => by rw [he])
  have hw : ∀ g : G1 F, w1 W f.1 φ' 1 g =
      p (row g) * T.indicator 1 (finPartPi (row g)) * w1 W f.1 φ 1 g := by
    intro g
    have hr : (![(0 : A F), 1] ᵥ* g.1) = row g := by
      ext i
      simp [row, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have h1 := hrow g ![0, 1, 1, 0]
    have h2 : (![(![0, 1, 1, 0] : V4 F) 0, (![0, 1, 1, 0] : V4 F) 1] : Fin 2 → A F) = ![0, 1] := by
      ext i
      fin_cases i <;> rfl
    rw [h2, hr] at h1
    simp only [w1, map_one, Module.End.one_apply]
    rw [h1]
    ring
  have hz := h0 φ' hφ'
  rw [← hz]
  simp only [W1, Meas.I0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [iw, hw]
  ring
end

