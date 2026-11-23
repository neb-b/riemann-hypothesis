module

public import Formalism.StatementFL

@[expose] public section

open Complex

noncomputable section

namespace Formalism.FX

open Classical

def triples (l : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 l ×ˢ Finset.Icc 1 l ×ˢ Finset.Icc 1 l).filter (fun S => S.1 + S.2.1 + S.2.2 = l)

def IsProb (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) : Prop :=
  (∀ S ∈ triples l, 0 ≤ ν S) ∧ ∑ S ∈ triples l, ν S = 1

def W (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (x : ℕ) : ℝ :=
  ∑ S ∈ triples l, ν S *
    ((if S.1 = x then 1 else 0) + (if S.2.1 = x then 1 else 0) + (if S.2.2 = x then 1 else 0))

def Snu (l : ℕ) (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  ∑ x ∈ Finset.Ioo 0 l, (W l ν x : ℂ) * (starRingEnd ℂ) (χ (x : ZMod l))

def cW (l : ℕ) [NeZero l] (ν : ℕ × ℕ × ℕ → ℝ) (χ : DirichletCharacter ℂ l) : ℂ :=
  DirichletCharacter.LFunction χ 0 * Snu l ν χ / ((((l : ℝ) - 1) / 2 : ℝ) : ℂ)

def oddChars (l : ℕ) [NeZero l] : Finset (DirichletCharacter ℂ l) :=
  @Finset.filter _ (fun χ => χ.Odd) (Classical.decPred _) (@Finset.univ _ (Fintype.ofFinite _))

def saw (y : ℝ) : ℝ := if Int.fract y = 0 then 0 else Int.fract y - 1 / 2

def gam (s : ℝ) : ℝ := Real.Gamma s / Real.Gamma (1 - s)

def logOm1 (l : ℕ) (S : ℕ × ℕ × ℕ) : ℝ :=
  -Real.log l + (Real.log (gam ((S.1 : ℝ) / (l : ℝ))) + Real.log (gam ((S.2.1 : ℝ) / (l : ℝ))) +
    Real.log (gam ((S.2.2 : ℝ) / (l : ℝ))))

def inCM (l : ℕ) (S : ℕ × ℕ × ℕ) (n : ℕ) : Prop :=
  Int.fract ((n * S.1 : ℝ) / l) + Int.fract ((n * S.2.1 : ℝ) / l) < 1


open ArithmeticFunction in
def AS (l : ℕ) (S : ℕ × ℕ × ℕ) (y : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
    if ¬ l ∣ n ∧ ¬ inCM l S n then Λ n * max 0 (y / (n : ℝ) - 1) else 0

def Al (l : ℕ) (y : ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 ⌊y⌋₊, Real.log l * max 0 (y / (l : ℝ) ^ i - 1)

def logPiV (l : ℕ) : ℝ := Real.log (2 * Real.pi / l) + Real.log l / ((l : ℝ) - 1)

def tripleMainTerm (l : ℕ) (S : ℕ × ℕ × ℕ) (y : ℝ) : ℝ :=
  y * (Real.log y - 1 - logOm1 l S + logPiV l)

end Formalism.FX
