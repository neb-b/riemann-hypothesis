module

public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0011
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0008
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
public import Formalism.GradedWeylDivisibility.Bundle0001
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0006
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010

@[expose] public section

namespace Formalism.GradedWeylDivisibility

theorem hwLine : HWLine := highest_weight_line
theorem hwLineTall : HWLineTall := highest_weight_line_tall
theorem fockQPos : FockQPos := fischerInnerRatPos
theorem fockQBilin : FockQBilin := fischerInnerRatBilinear
theorem fockQRowDivAdj : FockQRowDivAdj := fock_space_row_divided_adjoint
theorem rowDivClosedGraded : RowDivClosedGraded := row_divided_closed_graded
theorem hwInClosed : HWInClosed := hwInClosed_of hwLine rowDivClosedGraded
theorem closedEqNabla : ClosedEqNabla := closedEqNabla_of hwInClosed fockQPos fockQBilin fockQRowDivAdj
theorem weylEqNablaQ : WeylEqNablaQ := weylEqNablaQ_of closedEqNabla

theorem weylRational : WeylRational := weyl_module_rational weylEqNablaQ

end Formalism.GradedWeylDivisibility
