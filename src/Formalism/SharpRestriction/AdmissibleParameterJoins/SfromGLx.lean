module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0006
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.BasicNotions

theorem splitsF_of_splitsE (D : D7) (p : ℕ) (hp : p.Prime) (h : S.SplitsE D p) : StandardLattice.SplitsF D p := by
  have hF := BridgeLemma.splitsCompl_down D.host.F D.host.E p hp h
  refine ⟨?_, fun v hv => ?_⟩
  · exact (Nat.card_coe_set_eq _).trans ((BridgeLemma.ncard_plOver D.host.F hp hF).trans (finrank_F_eq D))
  · have h1 := (hF v.asIdeal v.isMaximal hv).1
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1

end Formalism.MainNotions.J

end
