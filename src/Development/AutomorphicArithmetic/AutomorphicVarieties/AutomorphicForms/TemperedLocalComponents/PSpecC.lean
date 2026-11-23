module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrCusp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.BrRepHolds

@[expose] public section

open UpperTheory.V.KernelIndexFullLattice in
theorem UpperTheory.V.Af.cuspSpectrumGL :
    GlobalTheory.Published.CuspidalSpectrumGL :=
  ⟨partA muHaar_holds quotPres_holds cmpEquiv_holds rangeLe_holds contMem_holds absCompact_holds,
    partB splitEq_holds muHaar_holds quotPres_holds cmpEquiv_holds cmpForm_holds rangeLe_holds contMem_holds
      absIrr_holds kernelIndexFullLattice_neBot kFinTr_holds kFinMem_holds brRep_holds,
    partC splitEq_holds brCusp_holds⟩
