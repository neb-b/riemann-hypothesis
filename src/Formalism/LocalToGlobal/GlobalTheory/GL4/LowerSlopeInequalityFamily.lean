module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.ColumnLatticeExactSlope
public import Formalism.LocalToGlobal.GlobalTheory.GL4.Bundle0001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.SuccessiveMinima.StatementMink
public import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0014
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0011
public import Formalism.LocalRingCardinality.Bundle0005
public import Formalism.PeriodIntegrals.Bundle0007
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0015
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoordH

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

theorem column_exact_slope_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : fam0 Fm ColSlopeEq :=
  ⟨0, fun _ _ _ _ => column_lattice_exact_slope _⟩

theorem lower_slope_inequality_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : FamilySlopeLowerOpenPart Fm :=
  familySlopeLowerOpen_of_std standard_slope_lower hook_length_bound Fm (column_exact_slope_family Fm)

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
