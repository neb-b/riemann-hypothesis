module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.TrInHolds
public import Development.EtaleCohomology.EtaleSheaves.EtaleEvenCohomologyGradedCommRingOfCupRingAxioms
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.EtaleCohomology.EtaleSheaves.UnimodularBlockEqToHomValEqOne
public import Development.EtaleCohomology.EtaleSheaves.Bundle0048
public import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono
public import Development.EtaleCohomology.EtaleSheaves.Bundle0026
public import Development.EtaleCohomology.EtaleSheaves.Bundle0012
public import Development.EtaleCohomology.EtaleSheaves.Bundle0016
public import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleAxioms.A0Alt
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SpecAbsolutelyIntegrallyClosedCohomology
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.E4
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134

@[expose] public section

namespace UpperTheory.Gal.KunnethLefschetz
open GlobalTheory.EtC

theorem upTo {P : Prop} (h : A1 → A2 → A3 → A4 → A5 → A7 → A8 → A9 → A10 → A11 → B1 → B2 → B3 → B4 → B5 → B7 → C1 → C2 → C3 → C4 →
    C5 → D1 → P) : P :=
  h GlobalTheory.T.quasiIso_hypercohomology_bijective _root_.GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology GlobalTheory.T.levelwiseEquivalence_isEquivalence GlobalTheory.T.mayerVietoris_equivalence_of_cover _root_.GlobalTheory.EtC.classes_die_on_etale_cover GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance _root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero
    GlobalTheory.T.etaleCohomology_bijective_of_support_bijective RedCoef.a11 GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity UpperTheory.etaleCohomology_functorialityAxioms_hold GlobalTheory.T.etC_b3 UpperTheory.etaleCohomology_excisionAxiom_holds GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology
    GlobalTheory.EtC.gaugeSplitting_holds GlobalTheory.EtC.etC_c2 UpperTheory.Cb.etale_cohomology_ind_etale_base_change HomotopyInv.homotopy_invariance_etale GlobalTheory.EtC.laurentPolynomial_cohomology_strictlyHenselian_vanishing projectiveBundleFormula_vectorBundle_any_space

theorem duality_diagonalClass_of_affineProperBaseChange (e1 : E1) : E2 :=
  UpperTheory.Et.E2.main ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, _root_.GlobalTheory.EtC.smooth_surjective_cech_descent_cohomology, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, _root_.GlobalTheory.EtC.classes_die_on_etale_cover, GlobalTheory.T.etaleCohomology_coefficient_longExactSequence, GlobalTheory.T.etaleCohomology_coefficientRing_invariance,
    _root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero, GlobalTheory.T.etaleCohomology_bijective_of_support_bijective, GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity, UpperTheory.etaleCohomology_functorialityAxioms_hold, GlobalTheory.T.etC_b3, UpperTheory.etaleCohomology_excisionAxiom_holds, GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic, e1⟩

end UpperTheory.Gal.KunnethLefschetz
