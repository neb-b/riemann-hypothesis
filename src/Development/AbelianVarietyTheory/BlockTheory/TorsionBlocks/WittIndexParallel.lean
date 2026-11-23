module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

open Formalism.BasicNotions Formalism.BasicNotions.TH

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParallelSig {D : D7} (V : HSp D) (p q : ℕ) : Prop :=
  ∀ τ : D.host.E →+* ℂ, Formalism.UG.HasSignature (V.gram.map τ) p q

theorem parallelSig_of_sigOK {D : D7} {V : HSp D} {p q : ℕ} (h : V.SigOK) (hs : ∀ τ, V.sig τ = (p, q)) :
    ParallelSig V p q := fun τ => by
  have := h τ
  rwa [hs τ] at this

end GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

end
