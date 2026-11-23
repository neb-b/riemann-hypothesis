module

public import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal

section One

variable {n P Q : ℕ} (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n)
  (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)




end One

def nT {n : ℕ} (ε : Fin n → Bool) : ℕ := Fintype.card {i // ε i = true}
def nF {n : ℕ} (ε : Fin n → Bool) : ℕ := Fintype.card {i // ¬ ε i = true}

def e0 {n : ℕ} (ε : Fin n → Bool) : Fin (nT ε) ⊕ Fin (nF ε) ≃ Fin n :=
  (Equiv.sumCongr (Fintype.equivFin {i // ε i = true}).symm
    (Fintype.equivFin {i // ¬ ε i = true}).symm).trans (Equiv.sumCompl fun i => ε i = true)

theorem sign_split_equiv_inl {n : ℕ} (ε : Fin n → Bool) (i) : ε (e0 ε (Sum.inl i)) = true := by
  simp only [e0, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin {i // ε i = true}).symm i).2

theorem sign_split_equiv_inr {n : ℕ} (ε : Fin n → Bool) (j) : ε (e0 ε (Sum.inr j)) = false := by
  show ε (((Fintype.equivFin {i // ¬ ε i = true}).symm j : {i // ¬ ε i = true}) : Fin n) = false
  simpa using ((Fintype.equivFin {i // ¬ ε i = true}).symm j).2

variable (C : CDHaar)

end Formalism.BasicNotions.Examples₂.CD
