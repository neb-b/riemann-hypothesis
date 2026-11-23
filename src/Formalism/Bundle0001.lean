module

public import Formalism.Statement

@[expose] public section

-- bundled from Formalism.StatementOC
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism


open ArithmeticFunction in
def Sz (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (x / n - 1)

def Gz (x : ℝ) : ℝ := Sz x - x * Real.log x + (1 + Real.eulerMascheroniConstant) * x


open ArithmeticFunction in
def Schi {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n * (χ n).re * (x / n - 1)

def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  Schi χ x + (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re * x

end Formalism
end
end

-- bundled from Formalism.ZetaRealNonvanish
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Pfun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  if s = 1 then DirichletCharacter.LFunction χ 1
  else (s - 1) * riemannZeta s * DirichletCharacter.LFunction χ s

def MellinS : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N),
    Measurable (S χ) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |S χ x| * x ^ (-σ - 1)) (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (S χ x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => (LamF χ n : ℂ)) s / (s * (s - 1))

def LSeriesLamF : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), (∀ n : ℕ, (χ n).im = 0) →
    ∀ s : ℂ, 1 < s.re →
      LSeries (fun n => (LamF χ n : ℂ)) s =
        -deriv riemannZeta s / riemannZeta s -
          deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s

def MellinElem : Prop :=
  (∀ a σ : ℝ, a < σ → IntegrableOn (fun x : ℝ => x ^ a * x ^ (-σ - 1)) (Ioi 1)) ∧
  (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |x * Real.log x| * x ^ (-σ - 1)) (Ioi 1)) ∧
  (∀ (a : ℝ) (s : ℂ), a < s.re →
      ∫ x in Ioi (1:ℝ), ((x ^ a : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - a)) ∧
  (∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), ((x * Real.log x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (s - 1) ^ 2)

def CharFacts : Prop :=
  quadraticCharFour ≠ 1 ∧ quadraticCharThree ≠ 1 ∧ quadraticCharacterMod7 ≠ 1 ∧ (∀ n : ℕ, (quadraticCharFour n).im = 0) ∧
    (∀ n : ℕ, (quadraticCharThree n).im = 0) ∧ (∀ n : ℕ, (quadraticCharacterMod7 n).im = 0)

end Formalism
end
end

