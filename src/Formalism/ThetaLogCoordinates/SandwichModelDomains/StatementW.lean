module

public import Formalism.GradedWeylDivisibility.StatementA

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.INST

open Formalism.GradedWeylDivisibility

def sExp (p r l : ℕ) : ℕ := r * (r - 1) / 2 * Nat.log p (l + r - 1)

def LBound (r : ℕ) {n : ℕ} (ν : Fin n → ℕ) (l : ℕ) : Prop :=
  (∀ t, ν t ≤ l) ∨ (n = r ∧ ∀ s t, ν s ≤ ν t + l)

def PrimeToPUnits (p : ℕ) (O : Type) [CommRing O] : Prop :=
  ∀ c : ℤ, ¬ (p : ℤ) ∣ c → IsUnit ((c : ℤ) : O)

def SandwichZp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ x ∈ dualWeyl ℤ_[p] r n ν, ((p : ℤ_[p]) ^ sExp p r l) • x ∈ weyl ℤ_[p] r n hn ν

def SandwichZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ f ∈ dualWeyl ℤ r n ν, ∃ c : ℤ, ¬ (p : ℤ) ∣ c ∧ (c * (p : ℤ) ^ sExp p r l) • f ∈ weyl ℤ r n hn ν

def SandwichDomain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ (O : Type) [CommRing O] [IsDomain O], PrimeToPUnits p O →
      (∀ x ∈ dualWeyl O r n ν, ((p : O) ^ sExp p r l) • x ∈ weyl O r n hn ν) ∧
      weyl O r n hn ν ≤ dualWeyl O r n ν

def UnitsOfLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O], ¬ IsUnit ((p : ℕ) : O) → PrimeToPUnits p O

def SandwichLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ l : ℕ, LBound r ν l →
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], ¬ IsUnit ((p : ℕ) : O) →
      (∀ x ∈ dualWeyl O r n ν, ((p : O) ^ sExp p r l) • x ∈ weyl O r n hn ν) ∧
      weyl O r n hn ν ≤ dualWeyl O r n ν

end Formalism.InvariantFactorPaths.INST
