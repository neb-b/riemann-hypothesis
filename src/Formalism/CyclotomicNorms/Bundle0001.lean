module

public import Mathlib

@[expose] public section

-- bundled from Formalism.CyclotomicNorms.StatementI
section
open Finset Polynomial
open scoped ComplexOrder

noncomputable section

namespace Formalism.CyclotomicNorms

def Exc (g d ℓ : ℕ) : Prop := ℓ.Prime ∧ g ^ d < ℓ ^ (4 * padicValNat ℓ (g ^ d - 1))

def BB (N g : ℕ) : Set ℕ := {g} ∪ {ℓ | ∃ d, 1 ≤ d ∧ d ≤ N ∧ Exc g d ℓ}

def BBCount : Prop :=
  ∀ g : ℕ, 2 ≤ g →
    (∀ d : ℕ, 1 ≤ d → Set.Finite {ℓ | Exc g d ℓ} ∧ Set.ncard {ℓ | Exc g d ℓ} ≤ 3) ∧
    ∀ N : ℕ, Set.Finite (BB N g) ∧ Set.ncard (BB N g) ≤ 3 * N + 1

def RootsOfUnityCount : Prop :=
  ∀ ℓ w d : ℕ, ℓ.Prime → 1 ≤ w → 1 ≤ d →
    (ℓ ≠ 2 → Nat.card {x : ZMod (ℓ ^ w) // x ^ d = 1} ≤ d * ℓ ^ padicValNat ℓ d) ∧
    Nat.card {x : ZMod (ℓ ^ w) // x ^ d = 1} ≤ 2 * d

def ChoiceCount : Prop :=
  ∀ (Y : ℝ) (N g₁ : ℕ), 2 ≤ Y → 1 ≤ N → Y ≤ g₁ → (g₁ : ℝ) ≤ 2 * Y →
    ∀ S : Finset ℕ, (∀ g ∈ S, Y ≤ g ∧ (g : ℝ) ≤ 2 * Y ∧ (BB N g ∩ BB N g₁).Nonempty) →
      (S.card : ℝ) ≤ (3 * N + 1) * (1 + 2 * N ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1))

def BlocksCycle : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (B : Finset (Finset Ω))
    (m p : ℕ) (g₀ : G),
    (∀ b ∈ B, b.card = m) → (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → Disjoint b b') → (∀ x, ∃ b ∈ B, x ∈ b) →
    (∀ g : G, ∀ b ∈ B, b.image (fun x => g • x) ∈ B) →
    p.Prime → Fintype.card Ω < 2 * p →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).IsCycle →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).support.card = p →
    B.card = 1 ∨ B.card = Fintype.card Ω

def JordanTransitive : Prop :=
  ∀ (G Ω : Type) [Group G] [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] (p : ℕ) (g₀ : G),
    MulAction.IsPretransitive G Ω → p.Prime → Fintype.card Ω < 2 * p →
    p + 3 ≤ Fintype.card Ω →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).IsCycle →
    (MulAction.toPerm g₀ : Equiv.Perm Ω).support.card = p →
    alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range ∧ ¬ Group.IsSolvable G

def Restriction : Prop :=
  ∀ (G k V : Type) [Group G] [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (N : ℕ) (H : Subgroup G) [H.Normal] (I : Subgroup G) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → G → k) (φ : G) (π : Equiv.Perm (Fin N)) (p : ℕ),
    8 ≤ N → Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) → I ≤ H →
    (∀ W : Submodule k V, (∀ g, ∀ x ∈ W, ρ g x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ i, ∀ y ∈ I, ρ y (e i) = χ i y • e i) →
    (∀ i j, i ≠ j → ∃ y ∈ I, χ i y ≠ χ j y) →
    (∀ y, y ∈ I ↔ φ * y * φ⁻¹ ∈ I) →
    (∀ i, ∀ y ∈ I, χ (π i) y = χ i (φ⁻¹ * y * φ)) →
    p.Prime → Fintype.card (Fin N) < 2 * p → p + 3 ≤ N → p ∈ π.cycleType →
    ∀ W : Submodule k V, (∀ h ∈ H, ∀ x ∈ W, ρ h x ∈ W) → W = ⊥ ∨ W = ⊤

def monicOf {K : Type} [Field K] {N : ℕ} (a : Fin N → K) : K[X] :=
  X ^ N + ∑ i : Fin N, C (a i) * X ^ (i : ℕ)


end Formalism.CyclotomicNorms
end
end

-- bundled from Formalism.CyclotomicNorms.StatementTW
section
open Finset Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms

def vl {L : Type*} [NormedField L] (ℓ : ℕ) (x : L) : ℝ := -Real.logb ℓ ‖x‖

end Formalism.CyclotomicNorms
end
end

