module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0493
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.WeilBound.CoreStatements.SatakeConjugation.CapEqQdet

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC Polynomial Finset

namespace PositivityTheory.RgBcC.Bridge

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


open Classical in
def atW (w : InfinitePlace E) (x : Matrix (Fin a) (Fin a) ℂ) : Lie E a :=
  fun i j v => if v = w then x i j else (1 : Matrix (Fin a) (Fin a) ℂ) i j

def along (w : InfinitePlace E) (g : GA E a) (φ : GA E a → ℂ) : Matrix (Fin a) (Fin a) ℂ → ℂ :=
  fun x => chart φ g (atW w x)

def eopW (w : InfinitePlace E) (s : Bool) : Fin a → Fin a → Module.End ℂ (Sm E a) :=
  if s then Eop w.embedding else Eop (ComplexEmbedding.conjugate w.embedding)

def defect (t : ℕ → ℂ) (m N : ℕ) (D : ℂ[X]) : ℂ[X] :=
  (X - C (m : ℂ)) ^ (N + 1) * (D.comp (X + 1) - D) -
    D * ∑ k ∈ range (N + 1), C ((-1) ^ k * t k) * (X - C (m : ℂ)) ^ (N - k)

end PositivityTheory.RgBcC.Bridge
