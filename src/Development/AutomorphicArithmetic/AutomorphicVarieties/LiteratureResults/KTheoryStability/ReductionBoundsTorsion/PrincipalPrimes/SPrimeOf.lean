module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PrincipalPrimes.ExistsPrincipal

@[expose] public section

namespace PositivityTheory.KB

theorem sPrime_of : SPrime := fun L _ _ => PrincipalPrimes.exists_prime L 25

end PositivityTheory.KB
