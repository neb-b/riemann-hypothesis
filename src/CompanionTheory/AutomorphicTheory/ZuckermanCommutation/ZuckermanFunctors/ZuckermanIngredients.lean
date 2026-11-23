module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.DecompositionOfInjective
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0027
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0029
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExteriorPowerIntegral
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSum
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0032
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.CapelliEigenvalues.Bundle0001
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.AdjFromApply
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.LieAlgebraHomomorphism
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.OrbitDerivatives.EtaleClosedPointLiftsSimpleRootsMonic
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ShiftApply

@[expose] public section

namespace CompanionTheory.Zuck

theorem zuckerman_ingredients : Steps := by
  exact {
    infChar := CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
    decOfInj := decomposition_of_injective
    decOfTrace := _root_.GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace
    homCat := _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat
    okTriv := trivial_rep_admissible
    okVr := vector_rep_admissible
    okWedge := _root_.GlobalTheory.CompanionTheory.ZuckWedge.okWedge
    okTens := _root_.GlobalTheory.CompanionTheory.ZuckTens.okTens
    matHom := _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom
    uIso := _root_.GlobalTheory.CompanionTheory.ZuckUIso.uIso
    homLie := CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism
    casSplit := _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit
    casDS := _root_.GlobalTheory.CompanionTheory.CasimirDS.casDS
    wedgeInt := _root_.GlobalTheory.CompanionTheory.WedgeEmb.wedgeInt
    wedgeQ := _root_.GlobalTheory.CompanionTheory.WedgeSplitCasimir.wedgeQ _root_.GlobalTheory.CompanionTheory.ZuckStdD.stdD _root_.GlobalTheory.CompanionTheory.WedgeDeriv.dC_wedge_single
    schur := CompanionTheory.D.gk.FinalFormK.schur'
    adj := adj_of _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom
    multOne := multOne_of _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.casSplit _root_.GlobalTheory.CompanionTheory.ZuckStdD.stdD
      CompanionTheory.D.gk.FinalFormK.kerZero' trivial_rep_admissible vector_rep_admissible _root_.GlobalTheory.CompanionTheory.ZuckTens.okTens
    inj := CompanionTheory.D.gk.FinalFormK.injectivity_induction
    occ := CompanionTheory.D.gk.FinalFormK.occurrence_induction
    zuckH := _root_.GlobalTheory.CompanionTheory.ZuckTransport.zuckerman_hypothesis_holds
    decTens := _root_.GlobalTheory.CompanionTheory.ZuckDecTens.decTens _root_.GlobalTheory.CompanionTheory.ZuckHomCat.homCat _root_.GlobalTheory.CompanionTheory.ZuckMatHom.matHom _root_.GlobalTheory.CompanionTheory.ZuckTensHom.tensHom CompanionTheory.D.gk.FinalFormK.lie_algebra_homomorphism trivial_rep_admissible
    toRaw := _root_.GlobalTheory.CompanionTheory.ZuckToRaw.toRaw
    count := _root_.GlobalTheory.CompanionTheory.ZuckCount.count
  }

end CompanionTheory.Zuck
