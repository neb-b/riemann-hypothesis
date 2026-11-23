module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice NumberField Formalism.IndefR.Links

namespace GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def intVecs (D : D7) (n : ℕ) : Set (Fin n → D.host.E) :=
  {x | ∀ a, x a ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)}

variable {D : D7}

theorem baseLat_eq {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0) (i : Fin D.R.m) :
    (L.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = L0c D (Vc D i) := by
  obtain ⟨c, hc⟩ := hL.βV i
  unfold Formalism.IndefR.Lev.IsBaseFrame at hc
  obtain ⟨-, -, -, h1, h2⟩ := hc
  ext x
  constructor
  · intro hx
    simpa using h2 x hx
  · intro hx
    simpa using h1 x hx

end GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace

end
