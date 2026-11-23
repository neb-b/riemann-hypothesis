module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0067

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

theorem gram_xi_eq_of_lawsFull {D : D7} {T : Full D} (h : LawsFull T) :
    ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0 := by
  intro j hj k k'

  obtain ⟨hr, hW⟩ := h.j.modelW j hj T.J.σ₀ T.J.good_σ₀
  obtain ⟨hG, hξ⟩ := hW k
  obtain ⟨hG', hξ'⟩ := hW k'
  exact ⟨hG.trans hG'.symm, hξ.trans hξ'.symm⟩

end GlobalTheory.Dict
