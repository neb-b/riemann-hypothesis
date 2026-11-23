module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.Imports
section
open Finset

noncomputable section

namespace GlobalTheory.WigSh

def wP {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) (l : Fin (n + 1)) : ℝ :=
  (∏ j, ((M j : ℝ) - 1 - (L l : ℝ))) / ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))

def wM {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) (l : Fin (n + 1)) : ℝ :=
  (∏ j, ((M j : ℝ) - (L l : ℝ))) / ∏ j ∈ univ.erase l, ((L j : ℝ) - (L l : ℝ))

end GlobalTheory.WigSh
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
section
noncomputable section

namespace GlobalTheory.ConvSer

def Intg {σ K : Type*} [NormedField K] (S : MvPowerSeries σ K) : Prop :=
  ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ 1

def Bdd {σ K : Type*} [NormedField K] (S : MvPowerSeries σ K) : Prop :=
  ∃ C : ℝ, ∀ ν, ‖MvPowerSeries.coeff ν S‖ ≤ C

def Small {σ K : Type*} [NormedField K] (s : MvPowerSeries σ K) : Prop :=
  Intg s ∧ ‖MvPowerSeries.constantCoeff s‖ < 1

def HS {σ K : Type*} [Fintype σ] [NormedField K] (S : MvPowerSeries σ K) (x : σ → K) (a : K) : Prop :=
  HasSum (fun ν : σ →₀ ℕ => MvPowerSeries.coeff ν S * ∏ i, x i ^ ν i) a

def PowerSeriesHasSumAt {K : Type*} [NormedField K] (f : PowerSeries K) (t a : K) : Prop :=
  HasSum (fun n : ℕ => PowerSeries.coeff n f * t ^ n) a

def ev {σ K : Type*} [Fintype σ] [NormedField K] (S : MvPowerSeries σ K) (x : σ → K) : K :=
  ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * ∏ i, x i ^ ν i

def ev1 {K : Type*} [NormedField K] (f : PowerSeries K) (t : K) : K :=
  ∑' n : ℕ, PowerSeries.coeff n f * t ^ n

def csub {σ τ K : Type*} [Fintype σ] [NormedField K] (s : σ → MvPowerSeries τ K)
    (S : MvPowerSeries σ K) : MvPowerSeries τ K :=
  fun μ => ∑' ν : σ →₀ ℕ, MvPowerSeries.coeff ν S * MvPowerSeries.coeff μ (∏ i, s i ^ ν i)

def csub1 {τ K : Type*} [NormedField K] (s : MvPowerSeries τ K) (f : PowerSeries K) :
    MvPowerSeries τ K :=
  fun μ => ∑' n : ℕ, PowerSeries.coeff n f * MvPowerSeries.coeff μ (s ^ n)

def shift1 {K : Type*} [NormedField K] (F : MvPowerSeries (Fin 2) K) (y : K) : PowerSeries K :=
  PowerSeries.mk fun a => ∑' b : ℕ,
    MvPowerSeries.coeff (Finsupp.single 0 a + Finsupp.single 1 b) F * y ^ b

def nMul {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) : PowerSeries R :=
  Nat.rec (motive := fun _ => PowerSeries R) 0
    (fun _ g => MvPowerSeries.subst (![g, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries) n

theorem nMul_zero {R : Type*} [CommRing R] (F : FormalGroup R) : nMul F 0 = 0 := rfl

theorem nMul_succ {R : Type*} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    nMul F (n + 1) = MvPowerSeries.subst
      (![nMul F n, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries := rfl

end GlobalTheory.ConvSer
end
end

