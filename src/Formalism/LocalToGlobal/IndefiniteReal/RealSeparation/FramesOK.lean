module

public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Datum Formalism.IndefR.Links NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def betaY (Rl : RealDat3 D A3 Ks) (j : ℕ) : GL (Fin (D.sp.Y j).rank) (EAf D) :=
  if h : j ≤ D.R.m then
    (show GL (Fin (Yc D j).rank) (EAf D) = GL (Fin (D.sp.Y j).rank) (EAf D) by
      show GL (Fin (D.sp.Y (min j D.R.m)).rank) (EAf D) = _
      rw [Nat.min_eq_left h]) ▸ Rl.βY j
  else 1


end Formalism.IndefR.Mi

end
