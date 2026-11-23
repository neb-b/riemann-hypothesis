module

public import Mathlib

@[expose] public section

open Module

namespace GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula

def gaussBinom (q m : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun j => Nat.casesOn j 1 fun _ => 0)
    (fun m b j => Nat.casesOn j 1 fun j => b (j + 1) + q ^ (m - j) * b j) m

open Module in
@[simp] theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right (q m : ℕ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m 0 = 1 := by
  cases m <;> rfl

@[simp] theorem gaussBinom_zero_succ (q j : ℕ) : gaussBinom q 0 (j + 1) = 0 := rfl

theorem gaussBinom_succ_succ (q m j : ℕ) :
    gaussBinom q (m + 1) (j + 1) = gaussBinom q m (j + 1) + q ^ (m - j) * gaussBinom q m j := rfl

open Module in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero (q : ℕ) :
    ∀ m j : ℕ, m < j → _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j = 0 := by
  intro m
  induction m with
  | zero =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rfl
  | succ m ih =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, ih (j + 1) (by omega), ih j (by omega)]
    simp

def SubspaceCount : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (j : ℕ),
    Nat.card {L : Submodule k V // finrank k L = j} = gaussBinom (Nat.card k) (finrank k V) j

end GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula
