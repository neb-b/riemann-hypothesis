module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0002
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.OpsRel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma psi_zero {F : Type} [Field F] [NumberField F] : ψ (0 : A F) = 1 := by
  simp [ψ]

private lemma psi_add {F : Type} [Field F] [NumberField F] (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, AddChar.map_add_eq_mul]

private lemma ab_one {F : Type} [Field F] [NumberField F] : ab (1 : (A F)ˣ) = 1 := by
  simp [ab]

private lemma ab_mul {F : Type} [Field F] [NumberField F] (a a' : (A F)ˣ) : ab (a * a') = ab a * ab a' := by
  simp [ab]

private lemma quadraticForm_scalar_mul {F : Type} [Field F] [NumberField F] (δ : F) (a : A F) (v : V4 F) :
    q4 δ (fun i => a * v i) = a ^ 2 * q4 δ v := by
  simp only [q4]; ring

private lemma quaternaryForm_unit_scaling {F : Type} [Field F] [NumberField F] (δ : F) (a : (A F)ˣ) (y v : V4 F) :
    B4 δ (fun i => (a : A F) * y i) (fun i => ((a⁻¹ : (A F)ˣ) : A F) * v i) = B4 δ y v := by
  have h : (a : A F) * ((a⁻¹ : (A F)ˣ) : A F) = 1 := a.mul_inv
  simp only [B4]
  linear_combination (2 * (y 2 * v 2 - rt δ * (y 3 * v 3)) - y 1 * v 0 - y 0 * v 1) * h

theorem UpperTheory.ConvolutionTheory.R2.C.opsRel :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (O : Ops δ η), δ ≠ 0 → (∀ a, η a ^ 2 = 1) → Rel O.N O.M O.W := by
  intro F _ _ δ η O hδ hη
  have hinv : ∀ a : (A F)ˣ, η a⁻¹ = η a := by
    intro a
    rw [map_inv, inv_eq_iff_mul_eq_one, ← pow_two, hη]
  have habinv : ∀ a : (A F)ˣ, ab a⁻¹ = (ab a)⁻¹ := by
    intro a
    have h1 : ab a * ab a⁻¹ = 1 := by rw [← ab_mul, mul_inv_cancel, ab_one]
    exact eq_inv_of_mul_eq_one_right h1
  have habpos : ∀ a : (A F)ˣ, ab a ≠ 0 := by
    intro a h
    have h1 : ab a * ab a⁻¹ = 1 := by rw [← ab_mul, mul_inv_cancel, ab_one]
    simp [h] at h1
  have hWW : ∀ (φ : S4 F) v, (O.W (O.W φ)).1 v = φ.1 (-v) := by
    intro φ v
    rw [O.W_apply]
    have : (O.W φ).1 = ft4 δ φ.1 := funext (O.W_apply φ)
    rw [this]
    exact (ftBasic F δ hδ φ.1 φ.2).2.1 v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext φ v
    simp [O.N_apply, psi_zero]
  · intro b c
    ext φ v
    simp only [Module.End.mul_apply, O.N_apply, add_mul, psi_add]
    ring
  · ext φ v
    simp [O.M_apply, ab_one]
  · intro a a'
    ext φ v
    simp only [Module.End.mul_apply, O.M_apply, ab_mul, map_mul, Units.val_mul]
    push_cast
    have : (fun i => (a : A F) * (a' : A F) * v i) = fun i => (a' : A F) * ((a : A F) * v i) := by
      funext i; ring
    rw [this]
    ring
  · intro a b
    ext φ v
    simp only [Module.End.mul_apply, O.M_apply, O.N_apply, quadraticForm_scalar_mul]
    have : b * ((a : A F) ^ 2 * q4 δ v) = (a : A F) ^ 2 * b * q4 δ v := by ring
    rw [this]
    ring
  · intro a
    ext φ v
    simp only [Module.End.mul_apply]
    rw [O.W_apply, O.M_apply, O.W_apply]
    have hM : (O.M a φ).1 = fun y => ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * y i :=
      funext (O.M_apply a φ)
    rw [hM, hinv, habinv]
    have hs := measScale F a (fun y => φ.1 y * ψ (B4 δ y (fun i => ((a⁻¹ : (A F)ˣ) : A F) * v i)))
    simp only [quaternaryForm_unit_scaling] at hs
    simp only [ft4]
    have hl : ∀ y, ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 (fun i => (a : A F) * y i) * ψ (B4 δ y v)
        = (((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ)) * (φ.1 (fun i => (a : A F) * y i) * ψ (B4 δ y v)) := by
      intro y; ring
    simp only [hl]
    rw [MeasureTheory.integral_const_mul, hs]
    have hne : ((ab a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habpos a
    push_cast
    field_simp
  · refine ⟨⟨O.W, O.W * O.W * O.W, ?_, ?_⟩, rfl⟩
    · ext φ v
      simp only [Module.End.mul_apply, Module.End.one_apply]
      rw [hWW, hWW]
      simp
    · ext φ v
      simp only [Module.End.mul_apply, Module.End.one_apply]
      rw [hWW, hWW]
      simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.TestEx
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private noncomputable abbrev g0 (F : Type) [Field F] [NumberField F] : FiniteAdeleRing (𝓞 F) F → ℂ :=
  cosetIndicator (1 : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) 0

private theorem gaussianTest_real_nonneg (x : A F) : ∃ r : ℝ, 0 ≤ r ∧ g1 (g0 F) x = (r : ℂ) := by
  refine ⟨(∏ w, Real.exp (-Real.pi * (TR.pInf F x w) ^ 2)) *
    (if x.2 - 0 ∈ idealFiniteAdeles (1 : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) then 1 else 0), ?_, ?_⟩
  · exact mul_nonneg (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le) (by split_ifs <;> norm_num)
  · simp only [g1, g0, cosetIndicator_apply]
    push_cast
    split_ifs <;> simp

private theorem four_real (v : V4 F) : ∃ r : ℝ, 0 ≤ r ∧ four (g1 (g0 F)) v = (r : ℂ) := by
  obtain ⟨a, ha, ea⟩ := gaussianTest_real_nonneg (F := F) (rt (2⁻¹ : F) * (v 1 - v 0))
  obtain ⟨b, hb, eb⟩ := gaussianTest_real_nonneg (F := F) (rt (2⁻¹ : F) * (v 1 + v 0))
  obtain ⟨c, hc, ec⟩ := gaussianTest_real_nonneg (F := F) (v 2)
  obtain ⟨d, hd, ed⟩ := gaussianTest_real_nonneg (F := F) (v 3)
  refine ⟨a * b * c * d, by positivity, ?_⟩
  simp only [four, ea, eb, ec, ed]
  push_cast
  rfl

private theorem gaussianTest_zero : g1 (g0 F) (0 : A F) = 1 := by
  have h : TR.pInf F (0 : A F) = 0 := by
    simp
  simp [g1, g0, cosetIndicator_apply, h]

private theorem four_zero : four (g1 (g0 F)) (0 : V4 F) = 1 := by
  simp [four, gaussianTest_zero]

private def Mt (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-2⁻¹, 2⁻¹, 0, 0; 2⁻¹, 2⁻¹, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def Nt (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![-1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private theorem NM : Nt F * Mt F = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nt, Mt, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> norm_num

private theorem MN : Mt F * Nt F = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Nt, Mt, Matrix.mul_apply, Fin.sum_univ_four] <;> field_simp <;> norm_num

private theorem four_mem : four (g1 (g0 F)) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  have h := GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi (Mt F) (Nt F) NM MN
    (gaussS F (Fin 4) (g0 F) (cosetIndicator_mem_finiteSchwartzBruhat _ _))
  convert h using 1
  funext v
  have hv : ((Mt F).map (algebraMap F (A F)) *ᵥ v) =
      ![rt (2⁻¹ : F) * (v 1 - v 0), rt (2⁻¹ : F) * (v 1 + v 0), v 2, v 3] := by
    funext i
    fin_cases i <;>
      simp [Mt, Matrix.mulVec, dotProduct, Fin.sum_univ_four, rt, mul_sub, mul_add] <;> ring
  rw [hv]
  simp [four, Fin.prod_univ_four]

end UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence

open UpperTheory.ConvolutionTheory.R2.C.TestFunctionExistence in
theorem UpperTheory.ConvolutionTheory.R2.C.testEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ g : FiniteAdeleRing (𝓞 F) F → ℂ, four (g1 g) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) ∧ ∫ v, four (g1 g) v ∂(adeleMeasurePi F) ≠ 0 ∧ Th (four (g1 g)) ≠ 0 := by
  intro F _ _ _
  have hm := four_mem (F := F)
  have hre : ∀ v : V4 F, four (g1 (g0 F)) v = (((four (g1 (g0 F)) v).re : ℝ) : ℂ) := by
    intro v
    obtain ⟨r, -, e⟩ := four_real (F := F) v
    rw [e]
    simp
  have hnn : ∀ v : V4 F, 0 ≤ (four (g1 (g0 F)) v).re := by
    intro v
    obtain ⟨r, h, e⟩ := four_real (F := F) v
    rw [e]
    simpa using h
  have hc : Continuous fun v : V4 F => (four (g1 (g0 F)) v).re :=
    Complex.continuous_re.comp (continuous_of_mem_schwartzBruhatPi hm)
  have hi : Integrable (fun v : V4 F => (four (g1 (g0 F)) v).re) (adeleMeasurePi F) :=
    (integrable_of_mem_schwartzBruhatPi hm).re
  refine ⟨g0 F, hm, ?_, ?_⟩
  · have hpos : 0 < ∫ v, (four (g1 (g0 F)) v).re ∂(adeleMeasurePi F) := by
      rw [integral_pos_iff_support_of_nonneg hnn hi]
      have ho : IsOpen (Function.support fun v : V4 F => (four (g1 (g0 F)) v).re) :=
        isOpen_compl_singleton.preimage hc
      refine ho.measure_pos _ ⟨0, ?_⟩
      simp [Function.mem_support, four_zero]
    have he : ∫ v, four (g1 (g0 F)) v ∂(adeleMeasurePi F) =
        ((∫ v, (four (g1 (g0 F)) v).re ∂(adeleMeasurePi F) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall hre)
    rw [he]
    exact_mod_cast hpos.ne'
  · have hs : Summable fun ξ : Fin 4 → F => four (g1 (g0 F)) fun i => rt (ξ i) :=
      (poisson_of_mem_schwartzBruhatPi hm).1.of_norm
    have hsr : Summable fun ξ : Fin 4 → F => (four (g1 (g0 F)) fun i => rt (ξ i)).re :=
      Complex.reCLM.summable hs
    have h1 : (1 : ℝ) ≤ ∑' ξ : Fin 4 → F, (four (g1 (g0 F)) fun i => rt (ξ i)).re := by
      have h := hsr.le_tsum (0 : Fin 4 → F) fun ξ _ => hnn _
      have h0 : (fun i : Fin 4 => rt ((0 : Fin 4 → F) i)) = (0 : V4 F) := by
        funext i
        simp [rt]
      rw [h0, four_zero] at h
      simpa using h
    intro hT
    have h2 : (Th (four (g1 (g0 F)))).re = ∑' ξ : Fin 4 → F, (four (g1 (g0 F)) fun i => rt (ξ i)).re :=
      Complex.re_tsum hs
    rw [hT] at h2
    simp at h2
    linarith
end

