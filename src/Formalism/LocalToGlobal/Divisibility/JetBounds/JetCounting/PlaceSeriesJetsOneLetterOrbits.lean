module

public import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.CurveAt

@[expose] public section

open scoped BigOperators

noncomputable section

namespace Formalism.L2.DIV.C

open Formalism.L2.DIV Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds Formalism.IncomingBounds
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (phFF thetaS NormRel PV)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open Formalism.L2.Th1.Top (IsHypPair inHyp IsLTNorm IsLatH IsFrameH thetaH)
open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.L2.Th1.GD (LocNorm thetaLin frameM InMul IsPairFrame)

def PlaceSeriesJetsCyclicOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (ιr P : Type) (e : PV ιr N0 N1 → P) (S : OrbSys ℂ_[l]) (x : P → MvPowerSeries S.ι ℂ_[l])
    (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostA l Q σ (cob F (phFF l g2 g3 s2 ε)) N0 N1 ιr P e S x Ψ β → IsSysW l Q S β

def IntegralSeriesCyclicOrbits : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Q : OrbSys ℂ_[l] → ℝ → Prop) (g2 g3 s2 ε : MaximalUnramifiedExtension l) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), CurveAt l g2 g3 s2 ε σ F →
  ∀ (N0 N1 : ℕ) (ιr : Type) [Fintype ιr] [DecidableEq ιr] (P : Type) (e : PV ιr N0 N1 → P) (S : OrbSys ℂ_[l])
    (x : P → MvPowerSeries S.ι ℂ_[l]) (Ψ : MvPowerSeries P ℂ_[l]) (β : ℝ),
    IsHostA l Q σ (cob F (phFF l g2 g3 s2 ε)) N0 N1 ιr P e S x Ψ β →
  ∀ (n : Type) [Fintype n] (f f' : ιr × Fin N0 × Fin N1 → n → MaximalUnramifiedExtension l), IsHypPair σ f f' →
  ∀ Θ : MvPowerSeries n ℂ_[l], HostInt l g2 g3 s2 ε Θ →
    ∃ U : MvPowerSeries S.ι ℂ_[l], Integral U ∧
      MvPowerSeries.subst x (serAlong e (inHyp l f f' Θ)) = MvPowerSeries.subst S.g U * S.E

def HostIntFree : Prop :=
  ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK), CmOK a₀ b₀ c₀ dK →
  ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ¬ l ∣ dK → (¬ ∃ a : ZMod l, a ^ 2 = -(dK : ZMod l)) →
  ∀ ι : ℂ ≃+* ℂ_[l], ∀ g2 g3 ε : MaximalUnramifiedExtension l,
    Formalism.L2.Th1.CM.IsGoodModel l (Formalism.L2.Th1.F.cmPair a₀ b₀ dK ha hdK) ι g2 g3 → ‖ε‖ = 1 →
    (∀ n, ‖PowerSeries.coeff n (thetaS l g2 g3 ε)‖ ≤ 1) →
  ∃ (s2 : MaximalUnramifiedExtension l) (lam : ℂ) (hlam : lam ≠ 0), ‖s2‖ ≤ 1 ∧ IsLTNorm l (cmL a₀ b₀ dK ha hdK lam hlam) ι g2 g3 s2 ε ∧
  (∀ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)), UnrOK (MaximalUnramifiedExtension l) l σ → IsLawOfLog l F →
    CurveAt l g2 g3 s2 ε σ F) ∧
  ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (g₀ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)), IsLatH (cmL a₀ b₀ dK ha hdK lam hlam) b₀ dK h Λ g₀ →
  ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ' : ℂ ≃+* ℂ, ‖σ' κ‖ = 1) ∧
  ∀ θ ∈ Th (matH h) (alphaQ (Real.sqrt dK / 2) (matH h)) Λ,
    Formalism.L2.Th1.H.tens4 θ = κ • kernel4 (cmL a₀ b₀ dK ha hdK lam hlam) (lam * a₀) Λ
      (alphaQ (Real.sqrt dK / 2) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n))) g₀ →
  ∃ g₁ : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
    IsIsom (matH (blk4 h)) (stdH (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) ∧
    ¬ l ∣ relIdx (stdLat (cmL a₀ b₀ dK ha hdK lam hlam) (Fin 4 × n)) (imgLat (g₁ : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) ∧
  (∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ →
    ∃ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix (n) (n) ℂ_[l]), IsFrameH σ ι g₁ γ B') ∧
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
  ∀ σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l, UnrOK (MaximalUnramifiedExtension l) l σ → (∃ F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l), IsLawOfLog l F) →
  ∀ (γ : Matrix (Fin 4 × n) (Fin 4 × n) (MaximalUnramifiedExtension l)) (B' : Matrix n n ℂ_[l]), IsFrameH σ ι g₁ γ B' →
    HostInt l g2 g3 s2 ε (thetaH l ι B' h t θ)

end Formalism.L2.DIV.C
