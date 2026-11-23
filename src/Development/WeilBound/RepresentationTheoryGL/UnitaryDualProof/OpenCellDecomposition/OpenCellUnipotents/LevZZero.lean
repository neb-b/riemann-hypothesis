module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.IsInvForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331

@[expose] public section

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier

namespace PositivityTheory.RgUd.CellA

abbrev dd (r m : ℕ) : Fin 2 → ℕ := ![r, m]

theorem hdd (r m : ℕ) : ∑ a, dd r m a = r + m := by
  simp [Fin.sum_univ_two]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def levZ (r m : ℕ) (z : kˣ) : Levi k (fun a => Fin (dd r m a)) :=
  fun a => if a = 0 then 1 else GeneralLinearGroup.scalar (Fin (dd r m a)) z

end PositivityTheory.RgUd.CellA
