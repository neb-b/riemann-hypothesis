module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Development
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.RSHS.ProjectionSandwichLength

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem eq_of_isAbsPow {ν ν' : HChar E} {s : ℝ} (h : ν.IsAbsPow s) (h' : ν'.IsAbsPow s) : ν = ν' := by
  have h0 : (ν * ν'⁻¹).IsAbsPow 0 := by
    refine ⟨fun v x hx => ?_, fun v => ?_, fun k => ?_⟩
    · change ν.loc v x * (ν'.loc v x)⁻¹ = 1
      rw [h.1 v x hx, h'.1 v x hx, inv_one, mul_one]
    · have e : ν.val v = ν'.val v := Units.ext ((h.2.1 v).trans (h'.2.1 v).symm)
      simp [HChar.val_mul, HChar.val_inv, e]
    · have e : ν.inf k = ν'.inf k := Units.ext ((h.2.2 k).trans (h'.2.2 k).symm)
      simp [HChar.inf_mul, HChar.inf_inv, e]
  exact mul_inv_eq_one.1 (GlobalTheory.DiscSpec.Model.eq_one_of_isAbsPow h0)

section Quot

variable {I V : Submodule ℂ (Sm E N)} {f : Sm E N →ₗ[ℂ] Sm E N}

end Quot

end PositivityTheory.RSHS.ProjectionSandwichLength

end
