module

public import Formalism.SizeWindowBrackets.Bundle0002
public import Formalism.SizeWindowBrackets.Bundle0004

@[expose] public section

namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr

noncomputable section

structure Par where

  x : ℝ

  ε : ℝ

  e₂ : ℕ

  nA : ℝ := 2 ^ e₂

  k : ℝ

  N : ℝ

  t : ℝ

  p₀ : ℕ

  La : ℝ

  rG : ℝ

  Sc : ℝ

  η : ℝ

  ρ : ℝ

  th : ℝ

  K₀ : ℝ

  d : ℕ

  C : ℝ

  β : ℝ

  Cord : ℝ

  Y : ℝ

  s₀ : ℝ

  bo : ℝ

namespace Par

variable (P : Par)

def n : ℝ := P.nA

def f : ℝ := 2 * P.n

def b : ℝ := bTx P.x P.ε

def a : ℝ := aTx P.x P.ε

def Xp : ℝ := XpTx P.x P.ε

def bp : ℝ := bpTx P.x P.ε

def wpp : ℝ := wppTx P.x P.ε P.n

def Xpp : ℝ := XppTx P.x P.ε P.n

def lx : ℝ := Real.log P.x

def δ₁ : ℝ := P.x ^ (-(P.ε / 8))

def θ : ℝ := P.x ^ (-P.ε)

def Sk : ℝ := P.Sc + P.k + P.η

def Q₁ : ℝ := P.C * P.rG * P.bp * P.lx

def Q₂ : ℝ := P.C * (P.bp / P.x + P.η + P.Sc + (P.wpp + P.t) * P.lx / P.δ₁) + P.bo

def Jo : ℕ := ⌊P.x ^ (P.ε / 4)⌋₊

def Ib : ℕ := ⌊P.x ^ (P.ε / 3)⌋₊

end Par

def Windows (P : Par) (e K : ℝ) : Prop :=
  0 < P.ε ∧ P.ε ≤ 1 ∧ 0 ≤ e ∧ 1 ≤ K ∧
  (P.x ^ 2 ≤ (2 : ℝ) ^ P.e₂ ∧ (2 : ℝ) ^ P.e₂ ≤ P.n) ∧ P.n ≤ P.x ^ e ∧
  P.x ^ 2 ≤ P.k ∧ P.k ≤ P.x ^ e ∧
  0 ≤ P.N ∧ P.N ≤ P.x ^ e ∧ 0 ≤ P.t ∧ P.t ≤ P.x ^ e ∧
  P.x ^ 4 + 1 ≤ (P.p₀ : ℝ) ∧ (P.p₀ : ℝ) ≤ P.x ^ e ∧
  0 ≤ P.La ∧ P.La ≤ P.x ^ (2 * P.ε) ∧
  0 ≤ P.rG ∧ P.rG ≤ P.x ^ e ∧
  0 ≤ P.Sc ∧ P.Sc ≤ Real.exp (P.x ^ (P.ε / 4)) ∧ 0 ≤ P.η ∧ P.η ≤ Real.exp (P.x ^ (P.ε / 4)) ∧
  0 ≤ P.ρ ∧ P.ρ ≤ (P.x ^ 2)⁻¹ ∧
  0 ≤ P.th ∧ P.th ≤ P.x⁻¹ ∧
  P.x ^ 2 ≤ P.K₀ ∧ P.x ^ 2 ≤ (P.d : ℝ) ∧
  0 ≤ P.C ∧ P.C ≤ K ∧ 0 ≤ P.β ∧ P.β ≤ K * (P.x ^ 2)⁻¹ ∧ 0 ≤ P.Cord ∧ P.Cord ≤ K ∧
  1 ≤ P.Y ∧ P.Y ≤ 2 * P.Xp ∧
  0 ≤ P.s₀ ∧ P.s₀ ≤ (P.x ^ 2)⁻¹ ∧
  0 ≤ P.bo ∧ P.bo ≤ Real.exp (P.x ^ P.ε / 2)

def LargeX (x ε e K : ℝ) : Prop :=
  1 ≤ x ∧ 100 * K * x ^ (4 * ε) ≤ x ∧
  100 * K * x ^ (4 * e + 4) ≤ Real.exp (x ^ (ε / 3)) ∧
  100 * K * x ^ (4 * e + 4) * Real.exp (x ^ (ε / 3) + x ^ (ε / 4)) ≤ Real.exp (x ^ ε / 2)

def LargeXEv : Prop :=
  ∀ ε e K : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → LargeX x ε e K

def unitU (P : Par) (m T : ℝ) : ℝ := T * m * P.b

def tFloors (P : Par) (m : ℝ) : ℝ :=
  m * (2 * P.C * P.f * P.Xpp * (P.N ^ 2 * Real.log P.a + 2 * Real.log P.a ^ 2))

def tCp (P : Par) (m T : ℝ) : ℝ := 2 * P.C * P.Sk * Real.log (2 * P.a) * (m * T) * P.Xpp

def tPrLow (P : Par) (m T : ℝ) : ℝ := m * T * (2 * Real.log 4 * (P.p₀ * P.Q₁))

def tPrHigh (P : Par) (m T : ℝ) : ℝ := m * T * (2 * Real.log 4 * (P.Xp * P.Q₂))

def tOr (P : Par) (m T : ℝ) : ℝ :=
  m * T * (2 * P.C * P.lx * P.a * ((P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
    2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1)))

def tOrders (P : Par) (m T : ℝ) : ℝ :=
  4 * m * T * P.a * (P.Cord * P.Jo * Real.log (2 ^ P.e₂ * max P.Y P.Xpp) ^ 2 / (2 : ℝ) ^ P.e₂)

def tBand (P : Par) (m T : ℝ) : ℝ :=
  4 * m * T * P.a * (P.Ib * ((4 * P.ρ + 1 / (P.p₀ : ℝ)) * Real.log (2 * P.Xp)))

def tHigh (P : Par) (m T : ℝ) : ℝ :=
  m * T * (2 * Real.log (2 * P.Xpp) * (P.a * P.th ^ 2 + P.wpp * P.th))

def tD (P : Par) (m T : ℝ) : ℝ := m * T * (2 * P.a * Real.log P.d / P.d)

def sg (P : Par) (K : ℝ) : ℝ := 100 * K * P.x ^ (4 * P.ε) / P.x

def SizeFloors : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tFloors P m ≤ sg P K * unitU P m T

def SizeCp : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tCp P m T ≤ sg P K * unitU P m T

def SizePrLow : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tPrLow P m T ≤ sg P K * unitU P m T

def SizePrHigh : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tPrHigh P m T ≤ (2 * Real.log 4 * P.C + 3 * sg P K) * unitU P m T

def SizeOr : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tOr P m T ≤ sg P K * unitU P m T

def SizeOrders : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tOrders P m T ≤ sg P K * unitU P m T

def SizeBand : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tBand P m T ≤ sg P K * unitU P m T

def SizeHigh : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tHigh P m T ≤ sg P K * unitU P m T

def SizeD : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tD P m T ≤ sg P K * unitU P m T

def SideConditionsOfWindows : Prop :=
  ∀ (P : Par) (e K : ℝ), Windows P e K → LargeX P.x P.ε e K →
    0 < P.wpp ∧ 0 ≤ P.th ∧ P.th ≤ 1 / 2 ∧ 2 ≤ P.Xpp ∧ P.Xpp * P.wpp = P.a ∧ 1 ≤ P.a ∧ 1 ≤ P.Xp ∧
    3 ≤ P.p₀ ∧ 4 ≤ P.d ∧ 0 ≤ P.C ∧ 0 ≤ P.f ∧ 0 ≤ P.Sk ∧ 0 ≤ P.Q₁ ∧ 0 ≤ P.Q₂ ∧ 0 ≤ P.lx ∧ 0 ≤ P.La ∧
    0 < P.k ∧ 0 < P.K₀ ∧ P.Xpp = P.x * P.n * P.Xp

structure LD (ι κ τ : Type) where

  W : Finset ι

  below : ι → ℕ

  l : ι → ℝ

  cl : ℕ → PClass

  TTp : ℕ → Finset τ

  Iex : κ → τ → ℕ → Finset ℕ

  at_ : τ → ℝ

  wz : κ → τ → ℕ → ℕ → ℝ

  Id : κ → τ → Finset ℕ

  wd : κ → τ → ℕ → ℝ

  gainW : κ → ι → ℝ

  tauW : ι → ℝ

  gain : κ → ℕ → ℝ

  tau : ℕ → ℝ

  lo : ℕ → ℝ

  fl : ℕ → ℝ

  L₁ : ℕ → ℝ

variable {ι κ τ : Type}

def LD.ASK (D : LD ι κ τ) (d : ℕ) (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ) : ℝ :=
  DeficitSplitLemmas.ASK Ps J TT (fun j t p => askAt (D.Iex j t p) (D.at_ t) p (D.wz j t p))
    (fun j t => Real.log d * askAt (D.Id j t) (D.at_ t) d (D.wd j t))

def LD.Ga (D : LD ι κ τ) (J : Finset κ) : ℝ := GaW D.W J D.l D.gainW D.tauW

def ParametersHyp (P : Par) (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ) (D : LD ι κ τ) : Prop :=
  UnitRule D.W D.below D.l Ps J D.gainW D.tauW D.gain D.tau ∧
  (∀ t ∈ TT, 0 ≤ D.at_ t ∧ D.at_ t ≤ P.a * (1 + P.th)) ∧
  (∀ j ∈ J, ∀ t ∈ TT, ∀ p ∈ Ps, ∀ i ∈ D.Iex j t p, Odd i ∧ P.wpp ≤ D.wz j t p i) ∧
  (∀ j ∈ J, ∀ t ∈ TT, ∀ i ∈ D.Id j t, 1 ≤ i ∧ 0 ≤ D.wd j t i) ∧
  (∀ p ∈ Ps, D.cl p = PClass.served → (p : ℝ) ≤ P.Xpp) ∧
  (∀ p ∈ Ps, D.cl p = PClass.high → P.Xpp < p) ∧
  (∀ p ∈ Ps, D.cl p = PClass.served →
    SizeData₂ J TT D.TTp (fun j t p => askAt (D.Iex j t p) (D.at_ t) p (D.wz j t p))
      D.gain D.tau D.lo D.fl p) ∧
  (∀ p ∈ Ps, D.cl p ≠ PClass.served → (∀ j ∈ J, D.gain j p = 0) ∧ D.tau p = 0) ∧
  (∀ p ∈ Ps, D.cl p = PClass.served → D.fl p ≤ flF P.C P.f P.N P.a p) ∧
  (∀ p ∈ Ps, D.cl p = PClass.served →
    D.lo p ≤ loF P.C P.Sk P.a P.Xp P.Q₁ P.Q₂ P.lx P.La P.k D.L₁ P.p₀ p) ∧
  (∀ p ∈ Ps, p < P.p₀ → P.K₀ ≤ (p : ℝ) ^ (D.L₁ p - 1))

def FirstHyp (P : Par) (Ps : Finset ℕ) (cl : ℕ → PClass) : Prop :=
  ∀ p ∈ Ps, cl p = PClass.first →
    (((p : ℝ) ≤ max P.Y P.Xpp ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ P.e₂),
        (orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf P.e₂ p hl) : ℝ) < P.x ^ (P.ε / 4)) ∨
      (P.p₀ ≤ p ∧ ∃ i : ℕ, 1 ≤ i ∧ P.Xp * (1 - P.ρ) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ P.Xp * (1 + P.ρ)))

def SecondLe : Prop :=
  ∀ (Ps s : Finset ℕ) (cl : ℕ → PClass) (Sg : ℕ → ℝ) (θ m T a : ℝ), 0 ≤ m → 0 ≤ T → 0 ≤ a →
    (∀ p ∈ Ps, cl p = PClass.second → p ∈ s ∧ θ < Sg p) →
    4 * m * T * a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.second), Real.log p / p) ≤
      ∑ p ∈ s, (if θ < Sg p then 4 * (m * T * a) * Real.log p / p else 0)

def FirstKind : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (Y X' ρ p₀ : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
    0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ → 2 ≤ X' →
    (∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧
      (((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) ∨
        (p₀ ≤ p ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X' * (1 + ρ)))) →
    ∑ p ∈ s, Real.log p / p ≤
      C * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e +
        (⌊Real.log X'⌋₊ : ℝ) * ((4 * ρ + 1 / p₀) * Real.log (2 * X'))



end

end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
