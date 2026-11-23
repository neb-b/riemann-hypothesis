module

public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0002
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0003
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0004
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0005
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNExtreme
public import Formalism.HarderNarasimhan.DegSupermodZ
public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
public import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle0001
public import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle0002
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameHermSharpB
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TheoremFSharp
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DualPl

@[expose] public section

namespace Formalism.HN

theorem satR : SatR := real_saturation_property
theorem finSup : FinSup := finite_supremum_slopes
theorem satBasic : SatBasic := saturation_basic_properties
theorem ratioMax : RatioMax := maximal_slope_ratio
theorem degSupermod : DegSupermod := degree_supermodular
theorem muChar : MuChar := slope_characterization
theorem hnStep_spec : HNStep := hnStep_of degSupermod muChar ratioMax finSup satR satBasic
theorem hnSum : HNSum := polygon_slope_sum
theorem hnSlopes : HNSlopes := polygon_slopes_characterization
theorem shiftInvariance : ShiftInvariance := shiftInvariance_of muChar muChar hnSlopes
theorem plLat : PlLat := place_lattice_structure
theorem sizeMu : SizeMu := size_maximal_slope
theorem rescaleCovol : RescaleCovol := rescale_covolume_formula
theorem twist : Twist := twist_of rescaleCovol plLat shiftInvariance
theorem slopeIneqMean : SlopeIneqMean := slope_inequality_mean
theorem htGram : HtGram := height_gram_determinant
theorem htImage : HtImage := height_image_formula
theorem sizeIneq : SizeIneq := sizeIneq_of size_maximal_slope height_image_formula place_lattice_structure
theorem rerealize : Rerealize := lattice_rerealization
theorem quotRealize : QuotRealize := quotient_lattice_realization
theorem theoremFSharp : TheoremFSharp := frame_theorem_sharp
theorem theoremF : TheoremF := frame_theorem_log_ideal
theorem dualPl : DualPl := dual_polygon_identity

end Formalism.HN
