module

public import Mathlib

@[expose] public section

namespace GlobalTheory

def chainEdge (k : ℕ) {r : ℕ} (i j : Fin r) : Prop := j.val = i.val + 1 ∧ i.val + 1 ≠ k

instance (k : ℕ) {r : ℕ} : DecidableRel (chainEdge k (r := r)) := fun i j =>
  inferInstanceAs (Decidable (j.val = i.val + 1 ∧ i.val + 1 ≠ k))

end GlobalTheory
