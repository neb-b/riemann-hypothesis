module

public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import GroundTheory.AutomorphicForms.GL2.Bundle0003

@[expose] public section

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace Ad3

section Mat

variable {R : Type*} [CommRing R]

def uni2 (x : R) : GL (Fin 2) R :=
  ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def dg2 (a b : Rˣ) : GL (Fin 2) R :=
  ⟨!![(a : R), 0; 0, b], !![((a⁻¹ : Rˣ) : R), 0; 0, (b⁻¹ : Rˣ)],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

def w0 : GL (Fin 2) R :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

end Mat

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

end Ad3
