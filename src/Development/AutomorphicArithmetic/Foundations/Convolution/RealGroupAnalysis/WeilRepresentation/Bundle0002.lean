module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierEqAdelic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ThetaSq
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Sl2InductionUnipotentWeyl
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.HatSt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.hatSt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), St.Hat W := by
  intro F E _ _ _ _ _ _ _ D W
  have hδ : D.δ ≠ 0 := by
    intro h0
    have hθ : D.θ = 0 := by
      have h := D.sq
      rw [h0, map_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    exact D.b.ne_zero 1 (by rw [D.b1, hθ])
  refine
    { n := _root_.UpperTheory.ConvolutionTheory.R2.D.hatN F E D W
      m := _root_.UpperTheory.ConvolutionTheory.R2.D.hatM F E D W
      w := ?_
      nE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatNE F E D W
      aE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatAE F E D W
      mem := fun φ => (_root_.UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1
      th := fun φ => (_root_.UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).2
      row := _root_.UpperTheory.ConvolutionTheory.R2.D.row F E D W }
  intro φ v
  have h : (W.Om (wW F) φ).1 = ft4 D.δ φ.1 := funext (W.Om_w φ)
  rw [h]
  exact _root_.UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ v hδ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsMore
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.inv :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Inv F := by
  intro F _ _ _ M₀ u hu hN hi
  obtain ⟨ρ, -, hρ, hρ'⟩ := M.iwDens F M₀
  have hp : Measurable fun p : IdeleGroup F × G1 F => mD p.1 * p.2 :=
    ((M.continuous_mD.comp continuous_fst).mul continuous_snd).measurable
  have hi' : Integrable (fun p : IdeleGroup F × G1 F => u (mD p.1 * p.2)) ρ := (hρ' _).1.2 hi
  refine ⟨fun g₀ => ?_, fun t => ?_⟩
  · have hg : Measurable fun g => u (g * g₀) := hu.comp (measurable_mul_const g₀)
    obtain ⟨h1, h2⟩ := M.transfer (m := ρ) (n := ρ) (hg.comp hp) (hu.comp hp) fun φ hφ =>
      (hρ (fun g => φ (u (g * g₀))) (hφ.comp hg)).trans
        ((M.lintegral_unipotent_quotient_right_invariant F M₀ (fun g => φ (u g)) (hφ.comp hu) (fun b g => by simp only [hN]) g₀).trans
          (hρ (fun g => φ (u g)) (hφ.comp hu)).symm)
    exact ⟨(hρ' _).1.1 (h1.2 hi'), (hρ' _).2.symm.trans (h2.trans (hρ' _).2)⟩
  · have hg : Measurable fun g => u (cD t g) := hu.comp (M.continuous_cD t).measurable
    obtain ⟨h1, h2⟩ := M.transfer (m := ρ) (n := ENNReal.ofReal (ab t)⁻¹ • ρ) (hg.comp hp) (hu.comp hp) fun φ hφ => by
      rw [lintegral_smul_measure, smul_eq_mul]
      exact (hρ (fun g => φ (u (cD t g))) (hφ.comp hg)).trans
        ((M.lintegral_unipotent_quotient_comp_diagonal_conj F M₀ (fun g => φ (u g)) (hφ.comp hu) (fun b g => by simp only [hN]) t).trans
          (congrArg _ (hρ (fun g => φ (u g)) (hφ.comp hu)).symm))
    refine ⟨(hρ' _).1.1 (h1.2 (hi'.smul_measure ENNReal.ofReal_ne_top)), (hρ' _).2.symm.trans (h2.trans ?_)⟩
    rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 (M.ab_pos t)).le, Complex.real_smul]
    exact congrArg _ (hρ' _).2
end

