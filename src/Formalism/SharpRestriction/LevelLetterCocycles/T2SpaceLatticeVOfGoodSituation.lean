module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0016

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

def PGen (S : Sit) : Set S.G :=
  {g | S.W.resΓ g ∈ Subgroup.closure (insert S.W.gamK (S.W.DelF : Set S.W.Gam))}

variable {l : ℕ} [Fact l.Prime]

instance contAddLL (LL : FinExt l) : ContinuousAdd ↥LL.1 :=
  ⟨continuous_induced_rng.2 ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd))⟩

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
