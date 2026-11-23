module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev RPt (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Fin m → Fin n → ℂ

def IsRealPtO (θ : InfFam D) {m n : ℕ} (z : RPt D m n) (w : Mx D m n) : Prop :=
  w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Matrix.of (z τ)

def RealPtEx (D : D7) : Prop :=
  ∀ (θ : InfFam D) (m n : ℕ), IsInfFam θ → ∀ z : RPt D m n, ∃! w, IsRealPtO θ z w

end Formalism.IndefR.Mi
