module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpFunctionalSymm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private theorem continuous_chirp {F : Type} [Field F] [NumberField F] (δ : F) (b : A F) :
    Continuous fun v : V4 F => ψ (b * q4 δ v) := by
  have hq : Continuous fun v : V4 F => q4 δ v := by
    unfold q4
    fun_prop
  exact continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp (continuous_const.mul hq))

private theorem norm_chirp_le {F : Type} [Field F] [NumberField F] (δ : F) (b : A F) (v : V4 F) :
    ‖ψ (b * q4 δ v)‖ ≤ 1 := by
  exact (Circle.norm_coe _).le

private theorem chirpFunctional_symm {F : Type} [Field F] [NumberField F] (δ : F) (hδ : δ ≠ 0) (b : (A F)ˣ)
    (φ₁ φ₂ : V4 F → ℂ) (h1 : φ₁ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) (h2 : φ₂ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    Lam4 δ (b : A F) φ₁ * ∫ v, φ₂ v ∂(adeleMeasurePi F) =
      Lam4 δ (b : A F) φ₂ * ∫ v, φ₁ v ∂(adeleMeasurePi F) :=
  symm (V4 F) (adeleMeasurePi F) (fun v => ψ ((b : A F) * q4 δ v)) φ₁ φ₂
    (continuous_chirp δ (b : A F)).measurable (norm_chirp_le δ (b : A F))
    (integrable_of_mem_schwartzBruhatPi h1) (integrable_of_mem_schwartzBruhatPi h2)
    (integrable_of_mem_schwartzBruhatPi ((pcMem F δ).2 hδ b φ₁ h1))
    (integrable_of_mem_schwartzBruhatPi ((pcMem F δ).2 hδ b φ₂ h2))

theorem UpperTheory.ConvolutionTheory.R2.C.idxEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), δ ≠ 0 → ∀ b : (A F)ˣ, ∃! c, IsIdx δ (b : A F) c := by
  intro F _ _ _ δ hδ b
  obtain ⟨g, hmem, hne, -⟩ := testEx F
  refine ⟨Lam4 δ (b : A F) (four (g1 g)) / ∫ v, four (g1 g) v ∂(adeleMeasurePi F), ?_, ?_⟩
  · intro φ
    have h := chirpFunctional_symm δ hδ b φ.1 (four (g1 g)) φ.2 hmem
    field_simp
    exact h
  · intro c hc
    have h := hc ⟨four (g1 g), hmem⟩
    exact eq_div_of_mul_eq hne h.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.GaussOp
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private theorem quadraticForm_neg (δ : F) (y : V4 F) : q4 δ (-y) = q4 δ y := by
  simp only [q4, Pi.neg_apply]
  ring

private theorem quaternaryForm_neg_right (δ : F) (y v : V4 F) : B4 δ (-y) (-v) = B4 δ y v := by
  simp only [B4, Pi.neg_apply]
  ring

theorem UpperTheory.ConvolutionTheory.R2.C.gaussOp :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ (b : (A F)ˣ) (c : ℂ), IsIdx δ (b : A F) c → ∀ (φ : S4 F) (v : V4 F),
    Pc δ (b : A F) φ.1 v = c * ft4 δ (fun y => ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 y) v := by
  intro F _ _ δ hδ b c hc φ v
  have hmem := (pcMem F δ).2 hδ b φ.1 φ.2
  have h2 := (ftBasic F δ hδ _ hmem).2.1 (-v)
  rw [neg_neg] at h2
  rw [← h2]
  have e1 : ∀ y, ft4 δ (Pc δ (b : A F) φ.1) y * ψ (B4 δ y (-v)) =
      c * ψ (-(((b⁻¹ : (A F)ˣ) : A F) * q4 δ y)) * ft4 δ φ.1 (-y) * ψ (B4 δ y (-v)) := fun y => by
    rw [idxFt F δ b c hc φ y]
  conv_lhs => rw [ft4]
  simp only [e1]
  rw [← integral_neg_eq_self _ (adeleMeasurePi F)]
  simp only [neg_neg, quadraticForm_neg, quaternaryForm_neg_right]
  rw [ft4, ← integral_const_mul]
  congr 1
  funext y
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ImportsBis
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.level :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)), IsOm δ η Om → ∀ φ, ∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → Om g φ = φ := by
  intro F _ _ δ η Om hOm φ
  let H : Subgroup (G1 F) :=
    { carrier := {g | Om g φ = φ}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        have h : Om a⁻¹ (Om a φ) = φ := by
          rw [← Module.End.mul_apply, ← map_mul]; simp
        rwa [ha] at h }
  have key : ∀ (f : S4 F) (b : A F), (∀ v, ψ (b * q4 δ v) * f.1 v = f.1 v) → Om (nU b) f = f := by
    intro f b h
    exact Subtype.ext (funext fun v => (hOm.n b f v).trans (h v))
  have h : ∀ᶠ b in 𝓝 (0 : A F), b.1 = 0 → nU b ∈ H ∧ wW F * nU b * (wW F)⁻¹ ∈ H := by
    refine ((nLevel F δ φ).and (nLevel F δ (Om (wW F)⁻¹ φ))).mono fun b hb h0 => ⟨key φ b (hb.1 h0), ?_⟩
    show Om (wW F * nU b * (wW F)⁻¹) φ = φ
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, key _ _ (hb.2 h0),
      ← Module.End.mul_apply, ← map_mul]
    simp
  exact grpLevel F H h
end

