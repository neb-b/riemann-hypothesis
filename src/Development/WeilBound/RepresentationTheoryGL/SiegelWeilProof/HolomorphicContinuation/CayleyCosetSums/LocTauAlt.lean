module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0002

@[expose] public section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

def fz (m : ℕ) (e : ℤ) (z : ℂ) (x : M2 n) : ℂ :=
  x.det ^ e * (u1 x).det ^ (-(m : ℤ)) * ((u1 x).det * (ub1 x).det) ^ (-z)

def sig (X : M2 n) : M2 n := -((JJ n)⁻¹ * Xᴴ * JJ n)

def rC (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) : ℂ :=
  deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) 0 +
    Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) 0

def lowQ (Q : Matrix (Fin n) (Fin n) ℂ) : M2 n := mX 1 Q 0 1 - 1

def tOp {Kg : Type} [MeasurableSpace Kg] (μ : Measure Kg) (ι : Kg → M2 n) (ρ : Kg → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) (a b : M2 n) (F : M2 n → ℂ) (x : M2 n) : ℂ :=
  ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F (x * ι k * a * nU (herm t) * b) * ψ t) ∂μ

def LocTau : Prop :=
  ∀ (n m : ℕ) (e : ℤ), m < n → ∀ (Kg : Type) [Group Kg] [TopologicalSpace Kg] [IsTopologicalGroup Kg] [CompactSpace Kg]
    [MeasurableSpace Kg] [BorelSpace Kg] (μ : Measure Kg) [μ.IsHaarMeasure] (ι : Kg →* M2 n), Continuous ι →
    (∀ g, InK g ↔ ∃ k, ι k = g) → ∀ Q : Matrix (Fin n) (Fin n) ℂ,
    ∃ (N : ℕ) (ρ : Fin N → Kg → ℂ) (ψ : Fin N → (Fin n → Fin n → ℝ) → ℂ) (a b : Fin N → M2 n) (D : ℂ → ℂ)
      (M : Fin N → ℂ → ℂ), (∀ l, Continuous (ρ l)) ∧ (∀ l, IsSingTest (ψ l)) ∧ (∀ l, InG (a l) ∧ InG (b l)) ∧
      Differentiable ℂ D ∧ D 0 ≠ 0 ∧ (∀ l, Differentiable ℂ (M l)) ∧
      ∀ (z : ℂ) (x : M2 n), InG x →
        D z * rC (lowQ Q) (fz m e z) x = ∑ l, M l z * tOp μ ι (ρ l) (ψ l) (a l) (b l) (fz m e z) x

end PositivityTheory.Rg.Sw.HSt
