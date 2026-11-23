module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Formalism.LogFactorialIndices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedLastEntry
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

def ph (y : ℝ) : ℝ := y * Real.log y - y

def size {a : ℕ} (nu : DomWeight a) : ℕ := ∑ i, (nu.w i).toNat

def lastEntry {a : ℕ} (nu : DomWeight a) : ℕ := nu.detShift.toNat

def padZero {a : ℕ} (b : ℕ) (nu : DomWeight a) (j : Fin b) : ℤ :=
  if h : j.1 < a then nu.w ⟨j.1, h⟩ else 0

def StepWeights {a b : ℕ} (lam nu : DomWeight a) (lam' : DomWeight b) : Prop :=
  (∀ i, 0 ≤ nu.w i) ∧ (∃ s' : ℤ, ∀ i, nu.w i = lam.w i + s') ∧
    ∃ s : ℤ, ∀ j, lam'.w j + s = padZero b nu j

def invNormSq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (P : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) P P).re

def OpNormSqLe {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) : Prop :=
  ∀ P : VV ℂ lam, invNormSq lam' (T P) ≤ t * invNormSq lam P

def unitSq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) : ℝ :=
  ∑ τ, ∑ β, ∑ α, ‖(r τ : ℂ) * z τ β α‖ ^ 2

def tmax {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (nu : ι → DomWeight a) (S : ℝ) (Om : ι → ℝ) : ℝ :=
  S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ size (nu τ) * Real.exp 1 * (2 * (size (nu τ) : ℝ) + 2) ^ (2 * (a * b)) *
    Real.exp (∑ i, ph ((nu τ).w i : ℝ)))

def BlockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
  ∀ (lam nu : ι → DomWeight a) (lam' : ι → DomWeight b),
    (∀ τ, StepWeights (lam τ) (nu τ) (lam' τ)) →
    (a = b → ∀ τ, lastEntry (nu τ) = 0) →
  ∀ (r Om : ι → ℝ) (cD : ι → ℂ),
    (∀ τ, 0 < r τ) → (∀ τ, 0 < Om τ) → (∀ τ, ‖cD τ * (r τ : ℂ)‖ ^ 2 = 1 / Om τ) →
  ∀ (G : VCx ι a b → ℂ) (S : ℝ), Differentiable ℂ G →
    (∀ z, ‖G z‖ ≤ S * Real.exp (unitSq r z / 2)) →
    OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => lastEntry (nu τ)) (tmax b nu S Om)

end GlobalTheory.IndefiniteRowSideFullHecke.PaddedLastEntry
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PaddedWittNormSquare
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PaddedWittNormSquare

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

def padZero {a : ℕ} (b : ℕ) (ν : DomWeight a) : Fin b → ℤ :=
  fun i => if h : i.1 < a then ν.w ⟨i.1, h⟩ else 0

def IsStepWeight {a b : ℕ} (lam ν : DomWeight a) (lam' : DomWeight b) (s' s : ℤ) : Prop :=
  (∀ i, ν.w i = lam.w i + s') ∧ (∀ i, 0 ≤ ν.w i) ∧ (∀ i, lam'.w i + s = padZero b ν i)

def wtSize {a : ℕ} (ν : DomWeight a) : ℕ := ∑ i, (ν.w i).toNat

def lastEntry {a : ℕ} (ν : DomWeight a) : ℕ := ν.detShift.toNat

def normSq {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (v : VV ℂ lam) : ℝ :=
  (pairK lam (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) v v).re

def OpNormSqLe {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b)
    (T : VV ℂ lam →ₗ[ℂ] VV ℂ lam') (t : ℝ) : Prop :=
  ∀ v : VV ℂ lam, normSq lam' (T v) ≤ t * normSq lam v

def unitNormSq {ι : Type} [Fintype ι] {a b : ℕ} (r : ι → ℝ) (z : VCx ι a b) : ℝ :=
  ∑ τ, ∑ β, ∑ α, ‖(r τ : ℂ) * z τ β α‖ ^ 2

def tmax {ι : Type} [Fintype ι] {a : ℕ} (b : ℕ) (ν : ι → DomWeight a) (Om : ι → ℝ) (S : ℝ) : ℝ :=
  S ^ 2 * ∏ τ, ((Om τ)⁻¹ ^ wtSize (ν τ) * Real.exp 1 * (2 * (wtSize (ν τ) : ℝ) + 2) ^ (2 * (a * b)) *
    Real.exp (∑ i, Formalism.LatticeIndexTer.ph ((ν τ).w i : ℝ)))

def BlockBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℕ), a ≤ b →
  ∀ (lam ν : ι → DomWeight a) (lam' : ι → DomWeight b) (s' s : ι → ℤ),
    (∀ τ, IsStepWeight (lam τ) (ν τ) (lam' τ) (s' τ) (s τ)) →
    (∀ τ, a < b ∨ lastEntry (ν τ) = 0) →
  ∀ (G : VCx ι a b → ℂ) (S : ℝ) (r Om : ι → ℝ) (cD : ι → ℂ),
    Differentiable ℂ G →
    (∀ τ, 0 < r τ) →
    (∀ z, ‖G z‖ ≤ S * Real.exp (unitNormSq r z / 2)) →
    (∀ τ, 0 < Om τ) →
    (∀ τ, ‖cD τ * (r τ : ℂ)‖ ^ 2 = 1 / Om τ) →
    OpNormSqLe lam lam' (jetOp lam lam' (jetC cD G) fun τ => lastEntry (ν τ)) (tmax b ν Om S)

theorem natW_eq_padZero {a b : ℕ} (hab : a ≤ b) {lam ν : DomWeight a} {lam' : DomWeight b} {s' s : ℤ}
    (h : IsStepWeight lam ν lam' s' s) (hg : a < b ∨ lastEntry ν = 0) (i : Fin b) :
    ((lam'.natW i : ℕ) : ℤ) = padZero b ν i := by
  obtain ⟨h1, h2, h3⟩ := h
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) i.2
  have hpad : ∀ j, 0 ≤ padZero b ν j := by
    intro j
    unfold padZero
    split_ifs
    · exact h2 _
    · exact le_rfl
  let j0 : Fin b := ⟨b - 1, by omega⟩
  have hlast : padZero b ν j0 = 0 := by
    unfold padZero
    split_ifs with hlt
    · have hlt' : b - 1 < a := hlt
      rcases hg with hg | hg
      · omega
      · have ha : 0 < a := by omega
        have hz : ν.w ⟨a - 1, by omega⟩ ≤ 0 := by
          unfold lastEntry DomWeight.detShift at hg
          rw [dite_eq_left ha] at hg
          exact Int.toNat_eq_zero.mp hg
        have hidx : (⟨j0.1, hlt⟩ : Fin a) = ⟨a - 1, by omega⟩ := Fin.ext (by simp [j0]; omega)
        rw [hidx]
        exact le_antisymm hz (h2 _)
    · rfl
  have hshift : lam'.detShift = -s := by
    unfold DomWeight.detShift
    rw [dite_eq_left hb]
    show lam'.w j0 = -s
    have h30 := h3 j0
    rw [hlast] at h30
    linarith
  unfold DomWeight.natW
  rw [hshift]
  have hw : lam'.w i - -s = padZero b ν i := by linarith [h3 i]
  rw [hw, Int.toNat_of_nonneg (hpad i)]

end GlobalTheory.IndefiniteRowSideFullHecke.PaddedWittNormSquare
end
end

