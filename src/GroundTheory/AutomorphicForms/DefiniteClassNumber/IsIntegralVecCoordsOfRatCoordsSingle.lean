module

public import Mathlib
public import GroundTheory.AutomorphicForms.DefiniteClassNumber.AdelicLattice

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)


variable (K) in
abbrev IntBasisIdx := Free.ChooseBasisIndex ℤ (𝓞 K)

def ratCoords (x : ι → K ⊗[K] E) : (ι × κ) × IntBasisIdx K → ℚ :=
  fun j => (integralBasis K).repr (vecCoords K b x j.1) j.2










variable (H : Matrix ι ι E)

variable {H}









def ratEmb (x : ι → K ⊗[K] E) : (ι × κ) × IntBasisIdx K → ℝ := fun j => (ratCoords b x j : ℝ)




end GroundTheory.Automorphic
