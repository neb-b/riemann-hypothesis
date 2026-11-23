module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.LemmaN
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEnds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.GramJoint
public import Formalism.SatakeDualWeyl.Statement
public import Formalism.LocalToGlobal.Columns.Bundle0015
public import Formalism.HermitianLattices.Bundle0003
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SplitDensity.FiberCardHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SiegelMassRatioOfLI

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Closed

theorem GramDetFlag_holds : Formalism.L2.SG.GramJoint.GramDetFlag := Formalism.L2.SG.GramJoint.gramDetFlag

theorem GNonnegAt_holds : Formalism.L2.SG.GramJoint.GNonnegAt := by
  have h : PI.FlagGramNonneg := flag_gram_nonneg
  intro E _ _ _ S τ hτ hsig r T T' hr hT hT' F F'
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.HasSignature (S.gram.map τ) p (r + 1) := ⟨(S.sig τ).1, hr ▸ hsig τ⟩
  exact h E S.V S.hT S.herm S.nondeg S.rank S.frame τ hτ p r T T' hp hT hT' F.e F'.e F.z F'.z
    ⟨F.e_indep, F.e_iso, F.z_orth, F.z_norm⟩ ⟨F'.e_indep, F'.e_iso, F'.z_orth, F'.z_norm⟩

theorem DNeZeroAt_holds : Formalism.L2.SG.GramJoint.DNeZeroAt := Formalism.L2.SG.GramJoint.dNeZeroAt_of GNonnegAt_holds


end Formalism.L2.SG.Closed
