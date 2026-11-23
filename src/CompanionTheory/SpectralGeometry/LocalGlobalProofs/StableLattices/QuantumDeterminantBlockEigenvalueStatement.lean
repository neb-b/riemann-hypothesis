module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0058
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0060
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0059

@[expose] public section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_determinant_block_eigenvalue : ∀ {n : ℕ} (Q : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (w : Q.V), (∀ a b, blk (stdBlocks d h) b < blk (stdBlocks d h) a → Q.E a b w = 0) → ∀ c : Fin 3 → ℂ → ℂ, (∀ i Y, Qd Q d h i Y w = c i Y • w) → ∀ Y : ℂ, qdet Q.E (Y + ((n : ℂ) - 1) / 2) w = (∏ i, c i Y) • w := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.qdet_eigen_of_killed | exact GlobalTheory.CompanionTheory.RgTransport.qdet_eigen_of_killed | (intros; apply GlobalTheory.CompanionTheory.RgTransport.qdet_eigen_of_killed <;> assumption)
