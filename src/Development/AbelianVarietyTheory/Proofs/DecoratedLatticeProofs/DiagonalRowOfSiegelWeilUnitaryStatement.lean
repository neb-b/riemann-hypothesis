module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitary

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.diagonalRow_of_siegelWeil_unitary :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
      GlobalTheory.Core.Rk.RowDiag (fun D L C' =>
        GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) :=
  GlobalTheory.Core.Rk.rowDiag_of_siegelWeilUnitary
