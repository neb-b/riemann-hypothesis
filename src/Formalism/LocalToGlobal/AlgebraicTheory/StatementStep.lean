module

public import Formalism.LocalToGlobal.Divisibility.JetBounds.Bundle0001
public import Formalism.GaussJetBounds.FinalB
public import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.AlgTh

open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

def GAt {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (Dc : DefCols Df) (u : Dc.Mem)
    (t : Bs.Tup) (Nu : Submodule (𝓞 K) (Fin (Dc.a u) → K)) (w : HeightOneSpectrum (𝓞 K)) (g : ℕ) [Fact g.Prime] (pb : K)
    (Dg : Bs.J → ℕ) (Rg : Bs.J → ℝ) : Prop :=
  ∃ (ι : K →+* ℂ_[g]) (X : PathData K g Bs.J (Fin (Dc.a u) → K) (Fin (Df.nV t) → K)) (D : ℕ) (j1 : Bs.J),
    EmbAt w g ι ∧ IsExpansion X ι (Dc.Pt u t) (Nu : Set (Fin (Dc.a u) → K)) (Df.Mt t : Set (Fin (Df.nV t) → K)) ∧
    ColsInt X w (Nu : Set (Fin (Dc.a u) → K)) ∧ RowsInt X w (Df.Mt t : Set (Fin (Df.nV t) → K)) ∧
    LastInt X ∧ UnitsInt X ∧ StabDvd X D j1 ∧ ¬ g ∣ D ∧
    ∀ π j, ‖X.e π j‖ * ‖ι pb‖ ^ (Dg j) * ‖(g : ℂ_[g])‖ ^ (Rg j) ≤ 1

end Formalism.L2.AlgTh
