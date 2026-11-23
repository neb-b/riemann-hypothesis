module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData

structure CData : Type 1 where
  I : AutInst
  b : ℝ
  lam : InfinitePlace I.F → Fin I.n → ℝ
  g : ℕ
  g₀ : ℕ
  e : I.Gf → ℂ
  H : InfinitePlace I.F → Type
  [hN : ∀ v, NormedAddCommGroup (H v)]
  [hI : ∀ v, InnerProductSpace ℂ (H v)]
  [hC : ∀ v, CompleteSpace (H v)]
  σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)
  w : ∀ v, H v
  Hs : Type
  [sN : NormedAddCommGroup Hs]
  [sI : InnerProductSpace ℂ Hs]
  [sC : CompleteSpace Hs]
  σs : I.Ginf → (Hs →L[ℂ] Hs)
  tens : (∀ v, H v) → Hs
  μf : Measure I.Gf
  [sf : SigmaFinite μf]
  fund : Set I.GA
  R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)
  Re : I.L2 μf fund →L[ℂ] I.L2 μf fund
  h : ℝ

attribute [instance] CData.hN CData.hI CData.hC CData.sN CData.sI CData.sC CData.sf

namespace CData

variable (X : CData)

abbrev L2 : Type := X.I.L2 X.μf X.fund


end CData

namespace CData

variable (X : CData)

end CData

namespace CData

variable (X : CData)


end CData

def cartanDistance {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : ℝ :=
  sInf {t | ∃ k X : Matrix (Fin n) (Fin n) ℂ, k ∈ Formalism.REAL.Kset ε ∧ Formalism.REAL.inP ε X ∧
    umat g = k * NormedSpace.exp X ∧ t = Real.sqrt (Formalism.REAL.hs X)}

namespace CData

variable (X : CData)




end CData

namespace CData

variable (X : CData)

end CData

namespace CData

variable (X : CData)


end CData

section Numbers

open Formalism.HermitianLatticeCounting.S7 (Ydat epsN)

end Numbers

namespace CData

variable (X : CData)

end CData


namespace CData

variable (X : CData)

end CData

end Formalism.MainNotions.BridgeLemma

end
