module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0141
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0140
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0087
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnReal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0150
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0078
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0131
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0135
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0068
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0170
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0293
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0175
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0237
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRDatumConst
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0114
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0290
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0103
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0165
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0110
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0109
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRCPPSCalc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerUnipotentHasRepresentation
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseInvOfCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRPHPhaseSec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0240

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreDone
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTCRefTrace_of_rotK (h : GTRRotK) : GTCRefTrace :=
  gTCRefTrace_of_cutK radial_gauge_move radial_gauge_constant_holds top_normal_form_of_curvature top_action_on_gauge_holds h radial_gauge_integrality_holds radial_gauge_transition_holds gauge_reality_holds

theorem gTCRef_of_rotK (h : GTRRotK) : GTCRef :=
  gTCRef_of_cut gauge_reality_holds curvature_identity_holds curvature_trace_holds (gTCRefTrace_of_rotK h) reference_annulus_holds

theorem gTConn_of_rotK (h : GTRRotK) : GTConn :=
  gTConn_of_leaves gauge_locality_holds gauge_reality_holds (gTCCurv_of_ref (gTCRef_of_rotK h)) (gTCHol_of_ref (gTCRef_of_rotK h)) annulus_condition_holds

theorem genTransfer_of_rotK (h : GTRRotK) : GenTransfer :=
  genTransfer_of_cut GT.gauge_function_holds gauge_kappa_holds (gTConn_of_rotK h) second_shift_gauge_holds

theorem gCore_of_rotK (h : GTRRotK) : GCore := gCore_of_genTransfer (genTransfer_of_rotK h)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_rotK (hJ : JfSmoothDS) (hR : Gauge.GC.GTRRotK) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_ssnRep hJ (Gauge.GC.genTransfer_of_rotK hR) h

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRRest
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR

theorem phase_invariance_holds : PhaseInv :=
  PH.phase_invariance_of_truncation PH.phase_section_holds PH.lower_unipotent_rotation_holds PH.rotation_radial_space_holds PH.theta_rotation_holds kappa_line_holds algebraic_shift_holds
    datum_constancy_holds fibre_stability_holds

theorem corePoly_of (hD : CP.Decomp) (hW : CP.WordPSVOfCut) : CorePoly :=
  CP.radial_polynomial_of_truncation CP.lower_unipotent_matrix_words
    (hW CP.radial_coefficient_linearity CP.radial_coefficient_smoothness CP.radial_coefficient_commutation CP.left_covariance_holds CP.right_covariance_holds CP.section_derivative_holds hD
      CP.polynomial_shift_calculation)
    CP.polynomial_shift_calculation

theorem polyRadialS_of (hD : CP.Decomp) (hW : CP.WordPSVOfCut) : PolyRadialS :=
  polynomialRadial_of_base polynomial_radial_base_holds SSn.Rep.theta_facts_hold transfer_holds datum_constancy_holds kappa_line_holds
    fibre_stability_holds algebraic_shift_holds (corePoly_of hD hW) phase_invariance_holds phase_extraction_holds word_nonvanishing_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR
end

