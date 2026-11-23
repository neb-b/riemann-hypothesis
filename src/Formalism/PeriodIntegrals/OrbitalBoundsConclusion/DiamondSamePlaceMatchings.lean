module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.DnDiaSame0FHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.UpSame
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnramifiedSameDiagonal.EqualDiagonalEntriesAll

@[expose] public section

namespace SameDiaZero

theorem diamond_same_place_matchings : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.SameAll := by
  intro D u T
  refine ⟨?_, ?_, ?_⟩
  · apply upSame <;> assumption
  · apply dnDiaSame0F_holds <;> assumption
  · first
      | (apply eSame <;> assumption)
      | (apply e_main <;> assumption)
      | (apply eDiaSame0F <;> assumption)

end SameDiaZero
