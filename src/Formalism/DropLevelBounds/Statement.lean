module

public import Formalism.IncomingBounds.Bundle0001

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.UnitaryBoundIntegral

open Formalism.IncomingBounds

def rowOf {n0 : ℕ} : PVar n0 → Fin n0 := Sum.elim Prod.fst Prod.fst

def rowDegZ {n0 : ℕ} (m : PVar n0 →₀ ℕ) (b : Fin n0) : ℕ := ∑ c : Fin n0, m (Sum.inl (b, c))

def rowDegZ' {n0 : ℕ} (m : PVar n0 →₀ ℕ) (b : Fin n0) : ℕ := ∑ c : Fin n0, m (Sum.inr (b, c))

def DetPowDiag : Prop :=
  ∀ (R : Type) [CommRing R] (n0 n : ℕ) (hn : n0 ≤ n) (Y : ℕ) (e : (Fin n × Fin n) →₀ ℕ),
    (∀ ρ c : Fin n, n0 ≤ ρ.val → e (ρ, c) = if c = ρ then Y else 0) →
    AddMonoidAlgebra.coeff ((Matrix.of fun b c : Fin n =>
          (MvPolynomial.X (b, c) : MvPolynomial (Fin n × Fin n) R)).det ^ Y)
        e =
      AddMonoidAlgebra.coeff ((Matrix.of fun b c : Fin n0 =>
          (MvPolynomial.X (Fin.castLE hn b, Fin.castLE hn c) :
            MvPolynomial (Fin n × Fin n) R)).det ^ Y)
        (e.filter fun x => x.1.val < n0)

def embV {n0 n : ℕ} (hn : n0 ≤ n) : PVar n0 → PVar n :=
  Sum.map (Prod.map (Fin.castLE hn) (Fin.castLE hn)) (Prod.map (Fin.castLE hn) (Fin.castLE hn))

def restr {C : Type} [Field C] {n0 n : ℕ} (hn : n0 ≤ n) (G : MvPowerSeries (PVar n) C) :
    MvPowerSeries (PVar n0) C :=
  fun m => MvPowerSeries.coeff (m.mapDomain (embV hn)) G

def diagMon (n0 n L y : ℕ) : PVar n →₀ ℕ :=
  ∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val),
    (Finsupp.single (Sum.inl (ρ, ρ)) (L * y) + Finsupp.single (Sum.inr (ρ, ρ)) y)

def BlockJet : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 n : ℕ) (hn : n0 ≤ n) (L y : ℕ)
    (G1 H : MvPowerSeries (PVar n) C),
    (∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m G1 ≠ 0 → ∀ x ∈ m.support, (rowOf x).val < n0) →
    (∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m H ≠ 0 → ∀ x ∈ m.support, n0 ≤ (rowOf x).val) →
    (∀ m : PVar n →₀ ℕ, (∀ x ∈ m.support, n0 ≤ (rowOf x).val) →
      (∀ ρ : Fin n, n0 ≤ ρ.val → rowDegZ m ρ ≤ L * y ∧ rowDegZ' m ρ ≤ y) →
      MvPowerSeries.coeff m H = if m = diagMon n0 n L y then 1 else 0) →
    jetAt0 (detL C n ^ (L * y) * detR C n ^ y) (G1 * H) =
      ((((L * y).factorial * y.factorial) ^ (n - n0) : ℕ) : C) *
        jetAt0 (detL C n0 ^ (L * y) * detR C n0 ^ y) (restr hn G1)

def RestrictMul : Prop :=
  ∀ (C : Type) [Field C] (n0 n : ℕ) (hn : n0 ≤ n) (G G' : MvPowerSeries (PVar n) C),
    restr hn (G * G') = restr hn G * restr hn G'

def RestrictExp : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 n : ℕ) (hn : n0 ≤ n) (h : MvPowerSeries (PVar n) C),
    restr hn (mvExp h) = mvExp (restr hn h)

def DropLevelsBasic : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → ∀ (W : ZMod d → ℝ), 0 ≤ W → ∀ i0 : ℕ,
    ∃ ys : ZMod d → ℕ → ℝ, IsFlow l d W ys ∧ (∀ a i, (i0 ≤ i ∨ i ∉ oddLevels d) → ys a i = 0) ∧
      (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
        (fun p => ys p.1 p.2 ≠ 0)).card ≤ d ∧
      maxFlow l d W - (∑ a, W a) / (l : ℝ) ^ i0 ≤ flowVal d ys

end Formalism.UnitaryBoundIntegral
