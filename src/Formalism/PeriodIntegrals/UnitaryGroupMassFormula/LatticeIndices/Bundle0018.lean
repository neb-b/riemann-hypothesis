module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0017
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImABwdEps
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_eps'_eq (p : TypX X) :
    1 - epsP X p = PI.FinKW.psiV X.B.I p.1 (sigA X.B.I X.ew) := by
  have h := imA_ew_split X p
  rw [epsP]
  linear_combination -h

theorem imA_bw_eps (p : TypX X) (i : Fin D.R.k) :
    epsP X p • PI.FinKW.vecV X.B.I p.1 (X.bw i) = PI.FinKW.vecV X.B.I p.1 (X.bw i) := by
  conv_rhs => rw [X.bw_w i]
  rw [imA_vecV_smul']

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOfBack
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem dual_fwd (hθ : IsSplitEquiv X p θ) (z : Fin X.B.I.n → FpX X p) (hz : z ∈ Mlat2 X p θ) :
    ∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p := by
  intro y hy
  induction hz using Submodule.span_induction with
  | mem z hz' =>
    obtain ⟨l', hl', rfl⟩ := hz'
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨l, hl, rfl⟩ := hy'
      exact dual_gen X p θ hθ l l' hl hl'
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Matrix.mulVec_add]
      first
      | (rw [dotProduct_add]; exact add_mem ha hb)
      | (rw [Matrix.dotProduct_add]; exact add_mem ha hb)
    | smul c a _ ha =>
      show _ ⬝ᵥ (J1 X p θ *ᵥ ((c : FpX X p) • a)) ∈ OpX X p
      rw [Matrix.mulVec_smul]
      first
      | (rw [dotProduct_smul, smul_eq_mul]; exact mul_mem c.2 ha)
      | (rw [Matrix.dotProduct_smul, smul_eq_mul]; exact mul_mem c.2 ha)
  | zero => simp
  | add a b _ _ ha hb =>
    first
    | (rw [add_dotProduct]; exact add_mem ha hb)
    | (rw [Matrix.add_dotProduct]; exact add_mem ha hb)
  | smul c a _ ha =>
    show ((c : FpX X p) • a) ⬝ᵥ _ ∈ OpX X p
    first
    | (rw [smul_dotProduct, smul_eq_mul]; exact mul_mem c.2 ha)
    | (rw [Matrix.smul_dotProduct, smul_eq_mul]; exact mul_mem c.2 ha)

def DualBack : Prop :=
  ∀ z, (∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p) → z ∈ Mlat2 X p θ

theorem latDual_of (hθ : IsSplitEquiv X p θ) (hB : DualBack X p θ) : LatDualP X p θ := by
  first
  | exact fun z => ⟨fun hz => dual_fwd X p θ hθ z hz, hB z⟩
  | exact ⟨fun z hz => dual_fwd X p θ hθ z hz, hB⟩
  | (unfold LatDualP; done)

theorem latBasisAll_of_back
    (hB : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → DualBack X p θ) :
    LatBasisAll X p :=
  latBasisAll_of X p (fun θ hθ => latSplit_of X p θ (unitElt_holds X p θ hθ)) (fun θ _ => latFree_holds X p θ)
    (fun θ hθ => latDual_of X p θ hθ (hB θ hθ))

end Loc

end MassDataIdxSteps
end
end

