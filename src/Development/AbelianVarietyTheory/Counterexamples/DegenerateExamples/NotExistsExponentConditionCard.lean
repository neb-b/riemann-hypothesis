module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0001

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory.ToricDenomCheck
variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem conj_conj' {R : Ranks} (H : Host R) (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  have h1 := H.conjE_apply H.φ₀ (H.conj x)
  have h2 := H.conjE_apply H.φ₀ x
  refine h1.trans ?_
  show starRingEnd ℂ (H.φ₀ (H.conj x)) = _
  rw [h2, Complex.conj_conj]

theorem isConj_symm {R : Ranks} {H : Host R} {P P' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H P P') : IsConjPl H P' P :=
  fun x y hy => (h y x (by rw [hy, conj_conj'])).symm

end GlobalTheory.ToricDenomCheck
