module

public import Mathlib
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G
open scoped BigOperators

def degPi (D : D7) (u : D.what₂.Word) (j : ℕ) : ℝ := ∑ τ : D.what₂.Tau, nuAbs D u j τ

def topSum {D : D7} (L : SizeData₂ D) : ℝ := ∑ t : D.host.TT, (L.aT t : ℝ)


open Classical in
def sizeOffTops (D : D7) (j : ℕ) : ℝ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : D.what₂.Tau => τ ∉ topsOf D.host D.eTau), wj D j τ

def degErr {D : D7} (L : SizeData₂ D) : ℝ :=
  (D.R.f : ℝ) * ((D.R.k : ℝ) * L.Sc + Nm D ^ 2 + (D.R.m : ℝ) * (D.R.t : ℝ) * L.etaSz) +
    (D.host.TT.card : ℝ) * L.sc.b' / L.sc.x


end GlobalTheory.IndefiniteRowSideFullHecke.LevelLossDegreeBounds

end
