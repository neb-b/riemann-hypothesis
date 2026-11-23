module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.LB

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def castZp {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) : ℤ_[a] →+* ℤ_[b] := by
  subst e; exact RingHom.id _

theorem castZp_symm {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) (x : ℤ_[b]) :
    castZp e (castZp e.symm x) = x := by
  subst e; rfl

theorem castZp_val {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) (x : ℤ_[a]) :
    (castZp e x).valuation = x.valuation := by
  subst e; rfl

theorem castZp_inj {a b : ℕ} [Fact a.Prime] [Fact b.Prime] (e : a = b) :
    Function.Injective (castZp e) := by
  subst e; exact fun x y h => h

end Formalism.MainNotions.N.Pv.LocalLengthBound.LB
