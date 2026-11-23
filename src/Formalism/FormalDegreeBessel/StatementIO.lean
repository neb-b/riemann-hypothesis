module

public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Formalism.RealPlaceAnalysis.Bundle0003

@[expose] public section

open Matrix
open scoped ContDiff

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Top (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (u : ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => (if a = b then u • f g else 0) + Eop a b f g

def qminorOp {t : ℕ} (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (a b : Fin t → Fin n) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun k : Fin t => Top Eop (u - ((k : ℕ) : ℂ)) (a (σ k)) (b k)).foldr (fun T h => T h) f)

def qdetOp (Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E))
    (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  qminorOp Eop id id u f

def capelli (ε : Fin n → Bool) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  qdetOp (EabV ε) u f

def minorOp {m : ℕ}
    (Eop : Fin (m + 1) → Fin (m + 1) → (Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → E) →
      (Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → E))
    (i j : Fin (m + 1)) (u : ℂ) (f : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → E) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → E :=
  qminorOp Eop (Fin.succAbove i) (Fin.succAbove j) u f

def chatOp {m : ℕ}
    (Eop : Fin (m + 1) → Fin (m + 1) → (Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → E) →
      (Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → E))
    (u : ℂ) (a β : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → Fin (m + 1) → ℂ)
    (f : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → E) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ → E :=
  fun g => ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * β g i * a g j) • minorOp Eop i j u f g

def drop2 {m : ℕ} (i : Fin (m + 2)) (i' : Fin (m + 1)) : Fin m → Fin (m + 2) :=
  fun k => i.succAbove (i'.succAbove k)

def minor2Op {m : ℕ}
    (Eop : Fin (m + 2) → Fin (m + 2) → (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E) →
      (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E))
    (i : Fin (m + 2)) (i' : Fin (m + 1)) (j : Fin (m + 2)) (j' : Fin (m + 1)) (u : ℂ)
    (f : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E :=
  qminorOp Eop (drop2 i i') (drop2 j j') u f

def chat2Op {m : ℕ}
    (Eop : Fin (m + 2) → Fin (m + 2) → (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E) →
      (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E))
    (u : ℂ) (a a' β β' : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → Fin (m + 2) → ℂ)
    (f : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E :=
  fun g => ∑ i : Fin (m + 2), ∑ i' : Fin (m + 1), ∑ j : Fin (m + 2), ∑ j' : Fin (m + 1),
    if (i : ℕ) ≤ (i' : ℕ) ∧ (j : ℕ) ≤ (j' : ℕ) then
      ((-1 : ℂ) ^ ((i : ℕ) + (i.succAbove i' : ℕ) + (j : ℕ) + (j.succAbove j' : ℕ)) *
        (β g i * β' g (i.succAbove i') - β g (i.succAbove i') * β' g i) *
        (a g j * a' g (j.succAbove j') - a g (j.succAbove j') * a' g j)) •
        minor2Op Eop i i' j j' u f g
    else 0

def QQop {m : ℕ}
    (Eop : Fin (m + 2) → Fin (m + 2) → (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E) →
      (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E))
    (c Y : ℂ) (y yb : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → Fin (m + 2) → ℂ) (x' x'b : Fin (m + 2) → ℂ) :
    Fin 2 → Fin 2 → (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E) → (Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ → E) :=
  fun p q f =>
    match p, q with
    | 0, 0 => qdetOp Eop (Y + c) f
    | 0, 1 => -(chatOp (m := m + 1) Eop (Y + c - 1) (fun _ => x') yb f)
    | 1, 0 => -(chatOp (m := m + 1) Eop (Y + c) y (fun _ => x'b) f)
    | 1, 1 => -(chat2Op Eop (Y + c - 1) y (fun _ => x') yb (fun _ => x'b) f)

def inUH (H g : Matrix (Fin n) (Fin n) ℂ) : Prop := gᴴ * H * g = H

def SmoothOnH (H : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀, inUH H g₀ → ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (F : Matrix (Fin n) (Fin n) ℂ → E),
    IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ ∀ g ∈ U, inUH H g → f g = F g

def hpart1 (H Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Z - H⁻¹ * Zᴴ * H)

def hpart2 (H Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / (2 * Complex.I) : ℂ) • (Z + H⁻¹ * Zᴴ * H)

def EabH (H : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => RdV (hpart1 H (Matrix.single a b 1)) f g + Complex.I • RdV (hpart2 H (Matrix.single a b 1)) f g

def capelliH (H : Matrix (Fin n) (Fin n) ℂ) (u : ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) :
    Matrix (Fin n) (Fin n) ℂ → E :=
  qdetOp (EabH H) u f

def GlRelAd : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 →
    GlRel (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d)

def EabHGl : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (H P Q : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E) (a b c d : Fin n)
    (g : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → P * Q = 1 → H = Pᴴ * Jm ε * P → SmoothOnH H f → inUH H g →
    EabH H a b (EabH H c d f) g - EabH H c d (EabH H a b f) g =
      (if b = c then EabH H a d f g else 0) - (if d = a then EabH H c b f g else 0)

end Formalism.QuantumDeterminants
