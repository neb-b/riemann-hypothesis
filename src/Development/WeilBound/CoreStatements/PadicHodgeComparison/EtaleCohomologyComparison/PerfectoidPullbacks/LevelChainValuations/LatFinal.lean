module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0159
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0160
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIsAdicComplete
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0164

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open DividedPowers

namespace CrystallineSemistableComparison.Pb.Lat

section Lat
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem dp_ι (hc : DPClosed (ι f ξ l M) (γB f ξ)) : IsDPMorphism (γ f ξ l M hc) (γB f ξ) (ι f ξ l M) :=
  ⟨Ideal.map_le_iff_le_comap.2 fun _ hx => hx, fun {n} a ha => (ι_γ f ξ l M hc ha).symm⟩

end Lat

section Map
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

end Map

end CrystallineSemistableComparison.Pb.Lat
