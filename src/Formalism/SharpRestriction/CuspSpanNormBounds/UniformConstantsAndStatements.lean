module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UniformConstantsAndStatements

export Formalism.MainNotions.S.UnitaryVolumeMass (Kng scalG)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants ValuativeRel IsDedekindDomain NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def adm5 (D : D7) (C : ℝ) : Prop :=
  UnitaryVolumeMass.stNG D C

structure Given where
  C0 : ℝ
  Cg : ℝ
  cb : ℝ
  Cu : ℝ
  cT : ℝ
  CT : ℝ
  one_le_window_constant : 1 ≤ C0
  cb_pos : 0 < cb
  cT_pos : 0 < cT

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (g : Given)

def admF5 (C : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i) C

end Fam

end Formalism.MainNotions.UniformConstantsAndStatements
