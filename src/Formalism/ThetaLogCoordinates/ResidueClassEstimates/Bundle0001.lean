module

public import Mathlib

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.ResidueClassEstimates.Letters
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def Dom (n : ℕ) (la : ℕ → ℤ) : Prop := ∀ m, m + 1 < n → la (m + 1) ≤ la m

def HStrip (n : ℕ) (mu mu' : ℕ → ℤ) : Prop :=
  (∀ m, m < n → mu m ≤ mu' m) ∧ ∀ m, m + 1 < n → mu' (m + 1) ≤ mu m

def Interl (n : ℕ) (la mu : ℕ → ℤ) : Prop := ∀ l, l < n → la l ≤ mu l ∧ mu (l + 1) ≤ la l

def wsize (n : ℕ) (la : ℕ → ℤ) : ℤ := ∑ m ∈ range n, la m

def tailPos (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : ℤ := ∑ m ∈ (range n).filter (fun m => u ≤ m), max (la m) 0

def tailNeg (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : ℤ :=
  ∑ m ∈ (range n).filter (fun m => u ≤ m), max (-(la (n - 1 - m))) 0

def weylDim (n : ℕ) (la : ℕ → ℤ) : ℝ :=
  ∏ j ∈ range n, ∏ i ∈ range j, (((la i - la j : ℤ) : ℝ) + ((j : ℝ) - (i : ℝ))) / ((j : ℝ) - (i : ℝ))

def fT (k' : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Icc 1 k', Real.log ((y + j) / j)

def fT' (k' : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Icc 1 k', 1 / (y + j)

structure Letters where
  r : ℕ
  K : ℕ
  Ns : ℕ
  vec : ℕ → Bool
  B : ℕ → ℕ

namespace Letters

def k (D : Letters) : ℕ := D.r + D.K

def n0 (D : Letters) : ℕ := D.Ns - D.r

def Wf (D : Letters) : Prop :=
  1 ≤ D.r ∧ 1 ≤ D.K ∧ 3 * D.r ≤ D.Ns ∧ (∀ i, 1 ≤ i → i ≤ D.r → D.vec i = true) ∧
  ∀ i, D.n0 < i → i ≤ D.Ns → D.vec i = true

def be (D : Letters) : ℕ := ∑ i ∈ Icc 1 D.n0, D.B i

def bePos (D : Letters) : ℕ := ∑ i ∈ (Icc 1 D.n0).filter (fun i => D.vec i = true), D.B i

def beNeg (D : Letters) : ℕ := ∑ i ∈ (Icc 1 D.n0).filter (fun i => D.vec i = false), D.B i

def latestV (D : Letters) (i : ℕ) : List ℕ :=
  (((List.range' 1 (min i D.n0)).filter fun l => D.vec l).reverse).map D.B

def latestC (D : Letters) (i : ℕ) : List ℕ :=
  (((List.range' 1 (min i D.n0)).filter fun l => !D.vec l).reverse).map D.B

def SPos (D : Letters) (u i : ℕ) : ℕ := ((D.latestV i).drop u).sum

def SNeg (D : Letters) (u i : ℕ) : ℕ := ((D.latestC i).drop u).sum

def Bo (D : Letters) (i : ℕ) : ℕ := (D.latestV (i - 1)).getD (D.r - 1 - (i - 1 - D.n0)) 0

def rankAA (D : Letters) : ℕ := ∏ i ∈ Icc 1 D.n0, (D.B i + D.k - 1).choose (D.k - 1)

abbrev Stages (D : Letters) : Type := Fin (D.Ns + 1) → Fin D.k → ℤ

def ent {D : Letters} (mu : D.Stages) (i m : ℕ) : ℤ :=
  if h : i < D.Ns + 1 ∧ m < D.k then mu ⟨i, h.1⟩ ⟨m, h.2⟩ else 0

def IsPATH (D : Letters) (mu : D.Stages) : Prop :=
  (∀ m, ent mu 0 m = 0) ∧ (∀ i, i ≤ D.Ns → Dom D.k (ent mu i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.Ns → D.vec i = true → HStrip D.k (ent mu (i - 1)) (ent mu i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.Ns → D.vec i = false → HStrip D.k (ent mu i) (ent mu (i - 1))) ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.vec i = true →
    wsize D.k (ent mu i) - wsize D.k (ent mu (i - 1)) = D.B i) ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.vec i = false →
    wsize D.k (ent mu (i - 1)) - wsize D.k (ent mu i) = D.B i) ∧
  ∀ i', 1 ≤ i' → i' ≤ D.r → ∀ m, m < i' → ent mu (D.n0 + i') m = D.be

def stLen (D : Letters) (i : ℕ) : ℕ := D.k - (i - D.n0)

def stage {D : Letters} (mu : D.Stages) (i : ℕ) : ℕ → ℤ := fun l => ent mu i (l + (i - D.n0))

def kaRows {D : Letters} (mu : D.Stages) (i : ℕ) : ℕ → ℤ := fun l => ent mu i (D.r + l)

def wt {D : Letters} (mu : D.Stages) : ℝ := weylDim D.K (kaRows mu D.Ns)

def Typical (D : Letters) (X : ℕ → ℝ) (mu : D.Stages) : Prop :=
  (∀ i, 1 ≤ i → i ≤ D.Ns → D.vec i = false →
    ((tailPos (D.stLen (i - 1)) (stage mu (i - 1)) 0 - tailPos (D.stLen i) (stage mu i) 0 : ℤ) : ℝ) ≤ X i) ∧
  (∀ i, D.r < i → i ≤ D.Ns → D.vec i = true →
    ((tailNeg (D.stLen (i - 1)) (stage mu (i - 1)) 0 - tailNeg (D.stLen i) (stage mu i) 0 : ℤ) : ℝ) ≤ X i) ∧
  ∀ i, D.r < i → i ≤ D.Ns → (2 / 3 : ℝ) * (D.Bo i : ℝ) ≤ (ent mu (i - 1) (D.r - 1) : ℝ)

def Hyp (D : Letters) (a : ℝ) (p : ℕ) : Prop :=
  3 ≤ a ∧ p.Prime ∧ 13 ≤ p ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.k ≤ D.B i ∧ (D.B i : ℝ) ≤ 2 * a) ∧
  (∀ l, l + 1 < (D.latestV D.n0).length →
    p ^ 2 * (D.latestV D.n0).getD (l + 1) 0 ≤ 5 * (D.latestV D.n0).getD l 0) ∧
  (∀ l, l + 1 < (D.latestC D.n0).length →
    p ^ 2 * (D.latestC D.n0).getD (l + 1) 0 ≤ 5 * (D.latestC D.n0).getD l 0) ∧
  (∀ i, D.n0 - D.r < i → i ≤ D.n0 → D.vec i = true) ∧ D.Ns + D.r ≤ D.K ∧ 2 * D.r ≤ D.Ns ∧
  D.k ≤ 2 * (D.K - 2 * D.Ns) ∧ (D.Ns : ℝ) ≤ a

def k' (D : Letters) : ℕ := D.K - 2 * D.Ns

end Letters

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

-- bundled from Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementL
section
noncomputable section

open scoped BigOperators TensorProduct
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def ResidueClassLowerBound : Prop :=
  ∀ (r Q be c : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
        (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card : ℝ)

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

-- bundled from Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementN
section
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def Consequences : Prop :=
  ∀ (r K Ns p E0 mS : ℕ) (a Y Q : ℝ), 2 ≤ r → 4 * r ≤ Ns → 13 ≤ p → 1 ≤ Y → 1 ≤ Q →
    1088 * (Ns : ℝ) ^ 2 * Real.log a ≤ ((r + K : ℕ) : ℝ) →
    32 * p * Y * ((r + K : ℕ) : ℝ) ^ 2 * Ns * Q ^ 2 * ((E0 : ℝ) + mS + 1) ≤ a →
    8 ≤ Ns ∧ 416 ≤ a ∧ 1 ≤ Real.log a ∧ 1088 * Ns ^ 2 ≤ r + K ∧
    160 * (Ns : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * Y ∧ 5 * Ns ≤ r + K ∧ 32 * Y ≤ a ∧ 8 * (Ns : ℝ) ≤ a ∧
    32 * (E0 : ℝ) ≤ a ∧ r + K ≤ 2 * (K - 2 * Ns) ∧ Ns + r ≤ K

def PowMulFloorDivLe : Prop :=
  ∀ (p k Dt Do ao : ℕ) (a Y : ℝ), 1 ≤ p → 1 ≤ k → 0 < Y → Dt ≤ Do → (ao : ℝ) ≤ 2 * a →
    (p : ℝ) ^ Dt * (⌊((ao : ℝ) / (p : ℝ) ^ Do) / ((k : ℝ) ^ 2 * Y)⌋₊ : ℝ) ≤ 2 * a / ((k : ℝ) ^ 2 * Y)

def ReducedDegree : Prop :=
  ∀ (k Ns : ℕ) (a Y at' E' E0 Et : ℝ), 0 < Y → 1 ≤ k → 0 ≤ a → E' ≤ E0 → 32 * E0 ≤ a →
    Et ≤ 4 * Ns * a / ((k : ℝ) ^ 2 * Y) → 160 * (Ns : ℝ) ≤ (k : ℝ) ^ 2 * Y → a ≤ at' →
    (9 / 10 : ℝ) * at' ≤ at' - E' - Et

def GeomDistinct : Prop :=
  ∀ (p m0 : ℕ) (s : Finset ℕ), 2 ≤ p → (∀ D ∈ s, m0 ≤ D) → ∑ D ∈ s, (1 / (p : ℝ) ^ D) ≤ 2 / (p : ℝ) ^ m0

def AdmissibleSmallRatio : Prop :=
  ∀ (p k Ns D1 L1 R R' : ℕ) (a Y Qn be : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → 0 < Qn → 1 ≤ L1 →
    be ≤ 4 * a / (p : ℝ) ^ (R + D1 + L1 + 1) →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * Qn)) < (p : ℝ) ^ R' →
    128 * (k : ℝ) ^ 2 * Ns * Y ^ 2 ≤ (p : ℝ) ^ (L1 - 1) →
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) < 32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ∧
    32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ≤ 1 / (4 * p * Y) ∧
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) ≤ 1 / (4 * Y)

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

