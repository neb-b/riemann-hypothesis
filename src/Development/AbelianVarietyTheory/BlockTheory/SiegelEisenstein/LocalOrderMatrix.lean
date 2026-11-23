module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

@[expose] public section

open MeasureTheory ValuativeRel Matrix NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix
open GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SymChain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV

def ordX (R : Ranks) (j : ℕ) : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j) :=
  ((finSumFinEquiv.sumCongr finProdFinEquiv).trans finSumFinEquiv).trans
    (finCongr (by unfold Ranks.N; ring))

theorem ordX_d (R : Ranks) (j : ℕ) (i : Fin j) (l : Fin R.t) :
    (ordX R j (.inr (i, l))).val = R.k + j + (l.val + R.t * i.val) := rfl

section Points
variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {a b : ℕ} {I J : Type}

def locVec (e : I ≃ Fin b) (y : Fin b → E) : I → k := fun r => ι (y (e r))

def locRow (e' : J ≃ Fin a) (η : (Fin a → E) →ₗ[E] E) : J → k := fun s => ι (η (Pi.single (e' s) 1))

end Points

section Match
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (σ₀ : X.K →+* ℂ)
  {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k)
  {s : ℕ} (S : SymData k s R.k)

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

end Match

end GlobalTheory.IndefiniteRowSideFullHecke.LocalOrderMatrix
