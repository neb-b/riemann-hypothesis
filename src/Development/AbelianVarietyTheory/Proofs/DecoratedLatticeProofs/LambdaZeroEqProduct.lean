module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevelComb
open GlobalTheory.FinPl (MxAt idAt)

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

section Red
variable {PP : Formalism.L2.DIV.Pl D.host.E} (G : GAt d τ PP)

end Red

section Grp
variable (G : ∀ PP : d.c.Pg, GAt d τ PP.1)

end Grp

end GlobalTheory.LevelComb

noncomputable section
namespace GlobalTheory.LevelComb
open GlobalTheory.FinPl (MxAt idAt)

section Comb
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D}

theorem comb_single_zero (f : WO S T → ℂ) : comb ψ S T (Finsupp.single 0 1) f = f := by
  funext w
  simp [comb, Finsupp.support_single_ne_zero, heisO, symplOH, symplO, hO]

end Comb

variable {D : D7} {u : D.what₂.Word} {d : Dat D u} {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E}

end GlobalTheory.LevelComb

namespace GlobalTheory.LevelComb

end GlobalTheory.LevelComb
