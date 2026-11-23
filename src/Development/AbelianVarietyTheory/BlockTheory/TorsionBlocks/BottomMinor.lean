module

public import Mathlib
public import Formalism.FockGram.Bundle0001

@[expose] public section

open MvPolynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors

def nextPart {l : ℕ} (a : Fin l → ℕ) (i : Fin l) : ℕ :=
  if h : (i : ℕ) + 1 < l then a ⟨i + 1, h⟩ else 0

def topMinor {n l : ℕ} (h : l ≤ n) (i : Fin l) : MvPolynomial (Fin n × Fin l) ℂ :=
  (Matrix.of fun r c : Fin (i + 1) =>
    (X (⟨r, by have := r.2; have := i.2; omega⟩, ⟨c, by have := c.2; have := i.2; omega⟩) :
      MvPolynomial (Fin n × Fin l) ℂ)).det

def bottomMinor {n l : ℕ} (h : l ≤ n) (i : Fin l) : MvPolynomial (Fin n × Fin l) ℂ :=
  (Matrix.of fun r c : Fin (i + 1) =>
    (X (⟨n - (i + 1) + r, by have := r.2; have := i.2; omega⟩,
        ⟨c, by have := c.2; have := i.2; omega⟩) :
      MvPolynomial (Fin n × Fin l) ℂ)).det

def delTop {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) : MvPolynomial (Fin n × Fin l) ℂ :=
  ∏ i : Fin l, topMinor h i ^ (a i - nextPart a i)

def delBottom {n l : ℕ} (h : l ≤ n) (a : Fin l → ℕ) : MvPolynomial (Fin n × Fin l) ℂ :=
  ∏ i : Fin l, bottomMinor h i ^ (a i - nextPart a i)

def hookDen {l : ℕ} (a : Fin l → ℕ) : ℚ :=
  ∏ i : Fin l, ∏ j ∈ Finset.Ioi i, ((a i : ℚ) - (a j : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ))

def hookProd {l : ℕ} (a : Fin l → ℕ) : ℚ :=
  (∏ i : Fin l, ((a i + (l - ((i : ℕ) + 1))).factorial : ℚ)) / hookDen a

def HookNorm : Prop :=
  ∀ (n l : ℕ) (h : l ≤ n) (a : Fin l → ℕ), Antitone a →
    Formalism.E.fock (delTop h a) (delTop h a) = ((hookProd a : ℚ) : ℂ)

def HookNormBottom : Prop :=
  ∀ (n l : ℕ) (h : l ≤ n) (a : Fin l → ℕ), Antitone a →
    Formalism.E.fock (delBottom h a) (delBottom h a) = ((hookProd a : ℚ) : ℂ)

open MvPolynomial in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart_le {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) (i : Fin l) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart a i ≤ a i := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.nextPart
  split_ifs with h
  · exact ha (show i ≤ (⟨i + 1, h⟩ : Fin l) from Fin.le_def.mpr (Nat.le_succ _))
  · exact Nat.zero_le _

open MvPolynomial in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen_pos {l : ℕ} {a : Fin l → ℕ} (ha : Antitone a) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen a := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors.hookDen
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j hj => ?_
  have hij : i < j := Finset.mem_Ioi.mp hj
  have hle : a j ≤ a i := ha hij.le
  have h1 : ((a j : ℕ) : ℚ) ≤ (a i : ℚ) := by exact_mod_cast hle
  have h2 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
  linarith

end GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
