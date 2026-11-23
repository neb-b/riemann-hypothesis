module

public import Mathlib

@[expose] public section

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def sg (l i : ℕ) : ℝ := 3 / (8 * (l : ℝ) ^ i)

def del (l i : ℕ) : ℝ := 1 / (8 * (l : ℝ) ^ i)

def r1 (l i : ℕ) : ℝ := rho l + 1 / (2 * (l : ℝ) ^ i)

def Kn (i : ℕ) : ℕ := (i + 1) / 2

def s0 (i : ℕ) : ℕ := (i - 1) / 2

variable {k : Type*} [Field k] {Z : Type*} {C : Type*}

def OrdGE (n : ℕ) (f : MvPowerSeries Z k) : Prop :=
  ∀ A : Z →₀ ℕ, A.degree < n → coeff A f = 0

def NoConst (t : C → MvPowerSeries Z k) : Prop := ∀ c, OrdGE 1 (t c)

structure Data (k : Type*) [Field k] (Z : Type*) (C : Type*) where

  v : AddValuation k (WithTop ℝ)

  l : ℕ
  l_prime : l.Prime
  l_ge : 3 ≤ l
  v_l : v (l : k) = 1

  i : ℕ
  i_odd : Odd i

  good : C → Prop

  lev : C → ℕ
  pure_good : ∀ c, lev c < Kn i → good c

  ι : Z → C
  ι_inj : Function.Injective ι
  ι_lev : ∀ d, lev (ι d) = 0

  al : C → ℕ → C → k

  g : C → C → k

  lam : C → C → k
  al_all : ∀ (c : C) (j : ℕ) (b : C), ((-(j : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c j b)
  al_good : ∀ c, good c → ∀ (j : ℕ) (b : C), 1 ≤ j → ((-((j : ℝ) - 1) : ℝ) : WithTop ℝ) ≤ v (al c j b)
  al_one : ∀ c, good c → ∀ b, al c 1 b = 0
  al_two : ∀ c, lev c < Kn i → ∀ b, al c 2 b = (l : k)⁻¹ * (g c b + (l : k) * lam c b)
  g_int : ∀ c b, 0 ≤ v (g c b)
  lam_int : ∀ c b, 0 ≤ v (lam c b)

  g_supp : ∀ c, lev c + 1 < Kn i → ∀ b, lev b ≠ lev c + 1 → g c b = 0

namespace Data

variable [Fintype Z] [Fintype C] (D : Data k Z C)

end Data

end

end Formalism.BaseCaseIdentities
