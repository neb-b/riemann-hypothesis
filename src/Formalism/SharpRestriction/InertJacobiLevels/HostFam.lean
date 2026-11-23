module

public import Formalism.LocalRingCardinality.DataHost
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.TameInertiaTowers.TowerFieldFoundations
public import Formalism.CyclotomicNorms.Bundle0001
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField
open scoped Pointwise

def Rt (s : ℕ) : Ranks where
  toFrame := Formalism.HC.cyclicFrame 2
  k := 8
  m := 2
  t := 2 * s + 15
  k_even := ⟨4, rfl⟩
  m_even := ⟨1, rfl⟩
  t_odd := ⟨s + 7, by ring⟩
  two_le_m := le_refl _
  m_add_three_le_k := by norm_num
  rank_add_five_le := by omega
  three_m_lt_t := by omega
  m_le_f := show 2 ≤ 2 * 2 ^ 2 by norm_num
  f_le_k := show 2 * 2 ^ 2 ≤ 8 by norm_num
  m_sq_le_N := by omega

structure Arith (B N : ℕ) where
  L : Type
  [instField : Field L]
  [instNF : NumberField L]

attribute [instance] Arith.instField Arith.instNF

variable {s B : ℕ} (A : Arith B (4 * (2 * s + 15) * 9 + 1))

end Formalism.MainNotions.Inhab

end
