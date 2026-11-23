module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle0001

@[expose] public section

noncomputable section

open PowerSeries

universe u v

namespace Formalism.G

section Hom

variable {R : Type u} [CommRing R]

abbrev atX (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (0 : Fin 2))

abbrev atY (f : PowerSeries R) : MvPowerSeries (Fin 2) R := f.subst (MvPowerSeries.X (1 : Fin 2))

def IsHom (F G : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ f.subst F.toPowerSeries = G.toPowerSeries.subst ![atX f, atY f]

def IsLog (F : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ coeff 1 f = 1 ∧ f.subst F.toPowerSeries = atX f + atY f

end Hom

def HomComp : Prop :=
  ∀ (R : Type u) [CommRing R] (F G H : FormalGroup R) (f g : PowerSeries R),
    IsHom F G f → IsHom G H g → IsHom F H (g.subst f)

def LogIffHomGa : Prop :=
  ∀ (R : Type u) [CommRing R] (F : FormalGroup R) (f : PowerSeries R),
    IsLog F f ↔ (IsHom F FormalGroup.𝔾ₐ f ∧ coeff 1 f = 1)

def LogExistsUnique : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra ℚ R] (F : FormalGroup R), ∃! f : PowerSeries R, IsLog F f

section FunEq

variable {K : Type u} [NormedField K]

def IntegralPS (f : PowerSeries K) : Prop := ∀ n : ℕ, ‖coeff n f‖ ≤ 1

def IntegralMv {ι : Type v} (F : MvPowerSeries ι K) : Prop :=
  ∀ d : ι →₀ ℕ, ‖MvPowerSeries.coeff d F‖ ≤ 1

def DivBy (x : K) (f : PowerSeries K) : Prop := ∀ n : ℕ, ‖coeff n f‖ ≤ ‖x‖

def IsFrobLift (p q : ℕ) (σ : K →+* K) : Prop := ∀ a : K, ‖a‖ ≤ 1 → ‖σ a - a ^ q‖ ≤ ‖(p : K)‖

def IsFunEqType (p q : ℕ) (σ : K →+* K) (f : PowerSeries K) : Prop :=
  IntegralPS (f - (p : K)⁻¹ • (PowerSeries.map σ f).subst ((PowerSeries.X : PowerSeries K) ^ q))

def IsFunEqTypeMv {ι : Type v} (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K) (φ : MvPowerSeries ι K) :
    Prop :=
  IntegralMv (φ - (p : K)⁻¹ • MvPowerSeries.expand q hq (MvPowerSeries.map σ φ))

end FunEq

def unitBall (K : Type u) [NormedField K] [IsUltrametricDist K] : Subring K := by
  first | exact @Bl.FirstLemmaM.goal1 K ‹_› ‹_› | exact @Bl.FirstLemmaM.goal1 K ‹_› | exact @Bl.FirstLemmaM.goal1 K | exact @Bl.FirstLemmaM.goal1

def FunctionalEquationSetting (K : Type u) [NormedField K] (p q : ℕ) (σ : K →+* K) : Prop :=
  p.Prime ∧ (∃ h : ℕ, 0 < h ∧ q = p ^ h) ∧ ‖(p : K)‖ < 1 ∧ IsFrobLift p q σ

def FunEqGroup : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → coeff 1 f = 1 → IsFunEqType p q σ f →
      ∃ F : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff F = 0 ∧ IntegralMv F ∧
        f.subst F = atX f + atY f

def FunEqHom : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (σ : K →+* K),
    FunctionalEquationSetting K p q σ →
    ∀ f g : PowerSeries K, constantCoeff f = 0 → coeff 1 f = 1 → IsFunEqType p q σ f →
      constantCoeff g = 0 → IsFunEqType p q σ g →
      ∃ h : PowerSeries K, constantCoeff h = 0 ∧ IntegralPS h ∧ f.subst h = g

def FunEqSubst : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ f : PowerSeries K, constantCoeff f = 0 → IsFunEqType p q σ f →
    ∀ (ι : Type v) (α : MvPowerSeries ι K), MvPowerSeries.constantCoeff α = 0 → IntegralMv α →
      IsFunEqTypeMv p q hq σ (f.subst α)

def SubstInjective : Prop :=
  ∀ (R : Type u) [CommRing R] (ι : Type v) (f : PowerSeries R) (a b : MvPowerSeries ι R),
    constantCoeff f = 0 → coeff 1 f = 1 →
    MvPowerSeries.constantCoeff a = 0 → MvPowerSeries.constantCoeff b = 0 →
    f.subst a = f.subst b → a = b

def ltLog (p : ℕ) [Fact p.Prime] : PowerSeries ℚ_[p] :=
  PowerSeries.mk fun n => by
    classical exact if ∃ k : ℕ, p ^ k = n then ((n : ℚ_[p]))⁻¹ else 0

end Formalism.G
