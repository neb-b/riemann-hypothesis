module

public import Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
public import Formalism.LogFactorialIndices.Bundle0001
public import Formalism.HarderNarasimhan.Bundle0001

@[expose] public section

open Module NumberField IsDedekindDomain
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LBrDiv

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2

section Defs1
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}

end Defs1

section Defs2
variable {U0 : Type} {W : U0 → Type} {Top : Type} {m f : ℕ}

end Defs2

section Defs3
variable {U0 : Type} {W : U0 → Type} [∀ u0, Fintype (W u0)] {Top : Type} {m f : ℕ}

end Defs3

section Defs4
variable {K : Type} [Field K] [NumberField K]

def lw (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ) / (finrank ℚ K : ℝ)

def plOf (w : HeightOneSpectrum (𝓞 K)) : slopeLatticeData.FinPl K := ⟨w.asIdeal, w.isMaximal⟩

end Defs4

end Formalism.LFunctionChainParameters.LBrDiv
