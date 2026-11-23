module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0029

@[expose] public section

namespace PositivityTheory.Tls2.BZGL

theorem standardFunctorsFiniteLength_top : GlobalTheory.Published.StandardFunctorsFiniteLength := by
  intro k _ _ _ _ r d _
  refine ⟨fun V _ _ π hπ hl => ?_, fun W _ _ ρ hρ hl => ?_⟩
  · exact _root_.GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k (Fin r) (Fin (∑ a, d a)) (fun a => Fin (d a)) finSigmaFinEquiv V π hπ hl
  · exact GlobalTheory.T.parabolic_induction_finite_length k (Fin r) (Fin (∑ a, d a)) (fun a => Fin (d a)) finSigmaFinEquiv W ρ hρ hl

end PositivityTheory.Tls2.BZGL
