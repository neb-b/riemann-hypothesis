module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def scaledInt (ϖ : kˣ) (a : ℕ) (m : ℤ) : Set (Matrix (Fin a) (Fin a) k) :=
  {Z | ∀ i j, valuation k (Z i j) ≤ valuation k ((ϖ ^ m : kˣ) : k)}

theorem mem_scaledInt_iff (ϖ : kˣ) (a : ℕ) (m : ℤ) (Z : Matrix (Fin a) (Fin a) k) :
    Z ∈ scaledInt ϖ a m ↔ Z ∈ matLat (A := Fin a) (ϖ ^ m • stdLat (k := k) (D := Fin a)) := by
  have hmem {Λ : Submodule 𝒪[k] (Fin a → k)} :
      Z ∈ matLat (A := Fin a) Λ ↔ ∀ i, Z.row i ∈ Λ := Iff.rfl
  rw [stdLat, smul_diagLat, hmem]
  simp only [mem_diagLat, Pi.one_apply, mul_one]
  rfl

def IsPeriodic (ϖ : kˣ) {a : ℕ} (M : ℤ) (φ : Matrix (Fin a) (Fin a) k → ℂ) : Prop :=
  ∀ X, ∀ Z ∈ scaledInt ϖ a M, φ (X + Z) = φ X

end Defs

def ShellLemma : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), IsUnif ϖ →
    ∀ (ν : kˣ →* ℂˣ) (e : ℕ), ¬ IsUnram ν → CondLE ϖ e ν →
    ∀ (a : ℕ) (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (φ : Matrix (Fin a) (Fin a) k → ℂ),
      φ ∈ SB (Matrix (Fin a) (Fin a) k) →
      (∀ (n : Fin a → ℤ) (z : ℂ),
        IntegrableOn (fun g : GL (Fin a) k => φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z) (shellSet ϖ n) μ) ∧
      (∀ M : ℤ, IsPeriodic ϖ M φ → ∀ n : Fin a → ℤ, (∃ i, M ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0) ∧
      (∀ M' : ℕ, Function.support φ ⊆ scaledInt ϖ a (-(M' : ℤ)) →
        ∀ n : Fin a → ℤ, ¬ (∀ i, -(M' : ℤ) ≤ n i) → ∀ z : ℂ, shell μ ϖ ν z φ n = 0) ∧
      {n : {n : Fin a → ℤ // Antitone n} | ∃ z : ℂ, shell μ ϖ ν z φ n.1 ≠ 0}.Finite

end GlobalTheory.IndefiniteRowSideFullHecke.ScaledIntegerPeriodic
