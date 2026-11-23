module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.CountOfHeisenbergIndex
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.CountOfHeisenbergIndexStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.count_of_heisenberg_index : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.CompanionTheory.InertCount.count | exact GlobalTheory.CompanionTheory.InertCount.count | (intros; apply GlobalTheory.CompanionTheory.InertCount.count <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.TwistedProofs.LatticeIndexOfSmithStatement
section
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_of_smith : Smith → LatIndex := by
  first | exact @GlobalTheory.CompanionTheory.InertIndex.latIndex | exact GlobalTheory.CompanionTheory.InertIndex.latIndex | (intros; apply GlobalTheory.CompanionTheory.InertIndex.latIndex <;> assumption)
end

