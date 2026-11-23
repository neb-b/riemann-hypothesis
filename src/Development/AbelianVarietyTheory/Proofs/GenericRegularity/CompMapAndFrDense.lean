module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFramesOfHolPeriods
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD CompSplitPfB

namespace GlobalTheory.Reg.GenericFrameDensity

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}


theorem lact_mem_dom (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact γ x ∈ X.dom := by
  have h2 : ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re := hx
  show ∀ τ : X.Ψ, (mat (lact γ x) τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (lact γ x) τ i).re
  intro τ
  refine ⟨?_, fun i => by rw [dmin_lact X hγ]; exact (h2 τ).2 i⟩
  show ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ).det ≠ 0
  rw [Matrix.det_mul]
  refine mul_ne_zero ?_ (h2 τ).1
  have e : ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det :=
    (RingHom.map_det τ.1 _).symm
  rw [e]
  exact (map_ne_zero τ.1).2 (Matrix.GeneralLinearGroup.det_ne_zero γ)

end Gen

end GlobalTheory.Reg.GenericFrameDensity
