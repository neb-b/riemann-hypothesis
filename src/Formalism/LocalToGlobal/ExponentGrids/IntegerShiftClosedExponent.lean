module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.Inputs
public import Formalism.QuotientMetricDivisors.Bundle0002
public import Formalism.TranslateCocycles.StatementHC
public import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols SPer IndefNum IndefCore)
open Formalism.L2.GlobalTheoryTheory (Arith.Cst Arith.Lev Arith.Lev.admitted Arith.sg Arith.elt Arith.eltBar Arith.pOf Arith.EatT)

noncomputable section

namespace Formalism.AtG

section Defs

variable {K : Type} [Field K] [NumberField K]

def PerBd [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (t : Bs.Tup) (w : HeightOneSpectrum (𝓞 K)) (s : ℝ) : Prop :=
  ∀ φ ∈ Nu, ∀ F ∈ Df.Mt t, Dc.Pt u t φ F = 0 ∨ s ≤ (vw w (Dc.Pt u t φ F) : ℝ)

def colRhs {J : Type} (s : Finset J) (g : ℕ) (nn : J → K) (cg : K) (E0 : ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  -(∑ j ∈ s, (vw w (nn j) : ℝ)) + (vw w cg : ℝ) - E0 * (vw w (g : K) : ℝ)


end Defs

end Formalism.AtG
