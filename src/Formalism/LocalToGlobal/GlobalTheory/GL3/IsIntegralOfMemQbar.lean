module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL3.Bundle0002
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.EqPAll
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0026
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

section Coef

variable {D : D7} {N N' : ℕ}

theorem taylor_lin {ι : Type*} [Fintype ι] (r : ι → ℂ) (F : ι → VC D N N' → ℂ)
    (hF : ∀ k (m : ℕ), ContDiff ℂ m (F k)) (α : Mono D N N') :
    taylor D (fun z => ∑ k, r k * F k z) α = ∑ k, r k * taylor D (F k) α := by
  unfold taylor
  have h1 : (fun z => ∑ k, r k * F k z) = fun z => ∑ k ∈ Finset.univ, r k • F k z := rfl
  rw [h1, iteratedFDeriv_sum (fun k _ => (hF k _).const_smul (r k)), Finset.sum_apply, _root_.sum_apply,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun x => r k • F k x) = r k • F k := rfl
  rw [e, iteratedFDeriv_const_smul_apply ((hF k _).contDiffAt), _root_.smul_apply, smul_eq_mul, mul_div_assoc]

end Coef

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestB

end
