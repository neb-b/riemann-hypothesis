module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0022
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.BetaLUniqOfAnisoEigen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.EigenvalueLastLineOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FundamentalDomainOfCompactOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0010

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BetaLUniq
section
theorem beta_l_unique : PI.BetaLUniq :=
  PI.UnitaryGroupMassFormula.BetaLUniq.betaLUniq_of_aniso_eigen PI.UnitaryGroupMassFormula.BetaLUniq.weight_space_anisotropic
    PI.UnitaryGroupMassFormula.BetaLUniq.eigenvalue_last_line_eq_one
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataMasses
section
open Formalism.L2.SG.TypedSets

theorem massDataMasses_of' (hH : MassDataMassesW.HinfCompact) (hK : MassDataMassesW.KCompactOpen)
    (hC : MassDataMassesW.ClassFinite) (hSA : MassDataMassesW.StrongApproxN) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InMassesAt X hb hK FdN FdN' u u' X0 L A :=
  MassDataMassesW.massDataMasses_of_strongApprox hH hK hC hSA (MassDataMassesW.fundamental_domain_of_compact_open hK MassDataMassesW.nRatBridge_holds)
end

