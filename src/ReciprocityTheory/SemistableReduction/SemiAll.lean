module

public import ReciprocityTheory.SemistableReduction.SemiDeg
public import ReciprocityTheory.SemistableReduction.Bundle0018
public import ReciprocityTheory.SemistableReduction.Bundle0029

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem semiPoint : SemiPointStatement := semiDeg_holds degAdd

theorem semistable : SemistableStatement := semiContract_holds semiPoint degAdd

end ReciprocityTheory.MultiplicativeHeights.Closed
