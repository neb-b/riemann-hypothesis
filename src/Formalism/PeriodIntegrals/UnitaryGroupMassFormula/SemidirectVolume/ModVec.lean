module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HermitianIsotropicProjComplement

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable (D : Dat A n r)

variable {D}

theorem pX_of_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) :
    D.pX x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [pX_apply]
    simp [fe H]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

end Dat

end PI.VolSemiDirect.W.PG
