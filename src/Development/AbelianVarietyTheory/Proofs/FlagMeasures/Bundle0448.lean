module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0444

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowMainEqPOfSiegelWeil
section
namespace GlobalTheory

theorem rowMainEqP_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsPos.RowMainEqP :=
  fun h => GlobalTheory.rowMainEqP_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h
      (fun _ X u u' hg => Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz
        CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.bDat_theoremB_global

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil
section
namespace GlobalTheory

theorem rowNGP_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsPos.RowNGP :=
  fun h => GlobalTheory.rowNGP_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h (fun _ X u u' hg =>
      Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.analytic_pinnedTheoremB_uniform

end GlobalTheory
end

