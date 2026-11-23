module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ExpIndep

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Z.Inf

def SatBd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (σ : CuspSub K n), ∃ c₀ : ℝ,
    ∀ (w : HeightOneSpectrum (𝓞 K)) (B : Multiset ℂˣ), (CG.mk σ).HasSat w B → ∀ b ∈ B,
      ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ∧ ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀

end UpperTheory.V.Z.Inf
