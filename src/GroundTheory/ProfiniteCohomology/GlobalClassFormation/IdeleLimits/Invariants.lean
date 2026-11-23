module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.SmulOfEqOfMemFixingSubgroup
public import GroundTheory.GlobalFields.IdeleClassGroup.Invariants
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange

noncomputable section

namespace IdeleLimit

open FiniteSubfield

theorem smul_of_eq_of_ideleEquiv {M : FiniteSubfield}
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (τ : M.1 ≃+* M.1)
    (h : ∀ x : M.1, σ x = τ x) (x : IdeleGroup M.1) :
    σ • of M x = of M (ideleEquiv τ x) :=
  (smul_of σ M x).trans (of_ideleEquiv_congr _ _ h x)

end IdeleLimit

end

end GroundTheory.ProfCoh
