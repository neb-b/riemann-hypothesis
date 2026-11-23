module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ProdNH
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.EvalVOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.UnipotentIntegralInLevel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Bundle0009
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0024
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes

@[expose] public section

noncomputable section

namespace MassDataLevelSSteps

open Formalism.L2.SG.TypedSets Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem levelSAll_holds : Formalism.L2.SG.Volumes.LevelSAll := level_s_all_split

theorem inLevelSAt_holds :
    ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
      (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
      (L : LocIn (TypX X)) (A : AnIn), InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  inLevelSAt_of_parts levelSAll_holds kSpCompact_holds kSpOpen_holds cmInst_holds frameStd_holds
    latAdapted_holds prodNH_holds globFromParts_holds haarIdxLoc_holds haarIdxGlob_holds locLevi_holds
    globProd_holds

end MassDataLevelSSteps
