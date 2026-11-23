module

public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0008
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0011
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0012
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0013
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0009
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0010
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0005
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0003
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0002
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0004
public import Formalism.ZeroFreeRegion.FinalZFR

@[expose] public section

-- bundled from Formalism.LandauZeroFreeBounds.FinalSiegel
section
namespace Formalism.ZeroFreeDirichlet

theorem bqKey : BqKey :=
  product_lfunction_key_inequality dirichlet_product_coefficients dirichlet_product_entire product_lfunction_growth_bound lfunction_one_upper_bound

theorem siegelLower : SiegelLower :=
  siegel_theorem_of exists_product_character exists_real_nontrivial_character bqKey lfunction_one_upper_bound zeta_negative_real_axis
    real_lfunction_real_on_reals lfunction_one_same_character

end Formalism.ZeroFreeDirichlet
end

-- bundled from Formalism.LandauZeroFreeBounds.NoZeroComplex
section
namespace Formalism.ZeroFreeDirichlet

theorem localZeros : LocalZeros :=
  localZeroSumBoundOfBounds localZeroExpansionWithMultiplicity lfunction_polynomial_growth inverseBound

theorem noZeroComplex : NoZeroComplex :=
  zeroFreeNonRealCharOfBounds localZeros l_log_deriv_right negLogDerivPositivity

theorem realLargeT : RealLargeT :=
  realCharZeroFreeLargeHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity trivial_log_deriv_bound

theorem realSmallT : RealSmallT :=
  realCharZeroSmallHeightOfBounds localZeros l_log_deriv_right negLogDerivPositivity realCharConj

theorem twoReal : TwoReal :=
  twoRealCharNoCommonZeroOfBounds localZeros l_log_deriv_right negLogDerivPositivity

theorem zFRDirichlet : ZFRDirichlet :=
  zeroFreeRegionExceptionalZeroOfBounds Formalism.ZF.zeroFreeRegion trivialCharZerosOfZeta noZeroComplex realLargeT realSmallT twoReal

end Formalism.ZeroFreeDirichlet
end

