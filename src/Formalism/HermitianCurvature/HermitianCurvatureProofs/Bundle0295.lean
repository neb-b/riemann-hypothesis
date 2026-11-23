module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0294
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0128
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPWordAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRFinal
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem polynomial_radial_holds : PolyRadialS := polyRadialS_of CP.radial_decomposition_holds CP.word_polynomial_vector_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GaugeConstructionHolds
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gauge_construction_holds : GCore := gCore_of_rotK rotation_K_invariance_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_SSnRep (hJ : JfSmoothDS) (h : JA.SSn.SSnRep) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_rotK hJ Gauge.GC.rotation_K_invariance_holds h

end Formalism.FourierDecayAlt.P.CutMP
end

