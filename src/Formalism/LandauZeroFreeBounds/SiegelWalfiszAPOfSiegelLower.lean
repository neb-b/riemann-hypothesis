module

public import Formalism.LandauZeroFreeBounds.Bundle0001
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0006
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PerronChi
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0007
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0012
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SmoothChiOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.PsiChiBoundOf
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0009
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SiegelWalfiszOf
public import Formalism.ZeroFreeRegion.LogDerivRegion

@[expose] public section

namespace Formalism.ZeroFreeDirichlet

theorem logDerivRegionChi : LogDerivRegionChi :=
  log_deriv_in_zero_free_region landau_local3 lfunction_polynomial_growth inverseBound l_log_deriv_right

theorem smoothChi : SmoothChi :=
  smoothed_character_sum_of perron_formula_character rectangle_contour_shift_character logDerivRegionChi l_log_deriv_right

theorem psiChiBound : PsiChiBound :=
  chebyshev_character_bound_of smoothChi Formalism.ZF.gzPNT

theorem excBound_of_siegelLower (hS : SiegelLower) : ExcBound :=
  exceptional_zero_bound_of hS lfunction_deriv_near_one

theorem siegelWalfisz_of_siegelLower (hS : SiegelLower) : SiegelWalfisz :=
  siegel_walfisz_character_of psiChiBound zFRDirichlet (excBound_of_siegelLower hS)

theorem excBound : ExcBound := excBound_of_siegelLower siegelLower

theorem siegelWalfisz : SiegelWalfisz := siegelWalfisz_of_siegelLower siegelLower

end Formalism.ZeroFreeDirichlet
