module

public import Formalism.SizeWindowBrackets.FirstPrimeNeSecondPrime
public import Formalism.FrobeniusOrbits.Statement
public import Formalism.SizeWindowBrackets.Bundle0002
public import Formalism.Bundle0001
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.SizeWindowBrackets.Bundle0001

@[expose] public section

-- bundled from Formalism.SizeWindowBrackets.GaloisToProductIsIso
section
open Finset

noncomputable section

namespace Formalism.LFunctionChainParameters.LHost

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

def localUnits (N p : ℕ) : Subgroup (ZMod N)ˣ := (ZMod.unitsMap (Nat.ordCompl_dvd N p)).ker

def IsFrobUnit (N p : ℕ) (w : (ZMod N)ˣ) : Prop :=
  ((w : ZMod N).cast : ZMod (ordCompl[p] N)) = (p : ZMod (ordCompl[p] N)) ∧
    ((w : ZMod N).cast : ZMod (ordProj[p] N)) = 1

def frobUnit (N p : ℕ) : (ZMod N)ˣ := by
  classical
  exact if h : ∃ w, IsFrobUnit N p w then h.choose else 1

section
variable {N : ℕ} {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def cftData (q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) : ArithData H where
  q1 := q1
  d := d
  inertia p := Subgroup.toAddSubgroup' ((localUnits N p).map r)
  frob p := Multiplicative.toAdd (r (frobUnit N p))

def dirChar (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) : DirichletCharacter ℂ N :=
  MulChar.ofUnitHom (ψ.toMonoidHom.comp r).toHomUnits

end

def sgn2 : ℤˣ →* Multiplicative (ZMod 2) where
  toFun s := Multiplicative.ofAdd (if s = 1 then 0 else 1)
  map_one' := by simp
  map_mul' := by decide

def FrobUnitSpec : Prop :=
  ∀ N p : ℕ, N ≠ 0 → p.Prime → IsFrobUnit N p (frobUnit N p) ∧ ∀ w, IsFrobUnit N p w → w = frobUnit N p

def UnramSpec : Prop :=
  ∀ N p : ℕ, N ≠ 0 → p.Prime → ¬ p ∣ N → localUnits N p = ⊥ ∧ ((frobUnit N p : (ZMod N)ˣ) : ZMod N) = (p : ZMod N)

section
variable (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H]

def DirCharSpec : Prop :=
  ∀ (N : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ),
    (∀ u : (ZMod N)ˣ, dirChar r ψ (u : ZMod N) = ψ (Multiplicative.toAdd (r u))) ∧
    ∀ x : ZMod N, ¬ IsUnit x → dirChar r ψ x = 0

def InertiaConductor : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (p : ℕ), N ≠ 0 → p.Prime →
    ((∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) ↔ ¬ p ∣ (dirChar r ψ).conductor)

def PrimValRamified : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (p i : ℕ), p.Prime → 1 ≤ i →
    ((∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) →
      primVal (cftData q1 d r) ψ (p ^ i) = ψ ((cftData q1 d r).frob p) ^ i) ∧
    ((¬ ∀ x ∈ (cftData q1 d r).inertia p, ψ x = 1) → primVal (cftData q1 d r) ψ (p ^ i) = 0)

def PrimValPrimitive : Prop :=
  ∀ (N q1 d : ℕ) (r : (ZMod N)ˣ →* Multiplicative (E0 × H)) (ψ : AddChar (E0 × H) ℂ) (n : ℕ), N ≠ 0 → n ≠ 0 →
    primVal (cftData q1 d r) ψ n = (dirChar r ψ).primitiveCharacter (n : ZMod (dirChar r ψ).conductor)

end


end Formalism.LFunctionChainParameters.LHost
end
end

-- bundled from Formalism.SizeWindowBrackets.GrowthBoundGivesRiemannHypothesis
section
open Finset ArithmeticFunction

noncomputable section

namespace Formalism.LFunctionChainParameters.ThickSetMeanBounds

open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

def psC : AddChar (E0 × H) ℂ where
  toFun g := if g.1.2 = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rcases a with ⟨⟨a1, a2⟩, ah⟩
    rcases b with ⟨⟨b1, b2⟩, bh⟩
    have key : ∀ x y : ZMod 2, (if x + y = 0 then (1 : ℂ) else -1)
        = (if x = 0 then 1 else -1) * (if y = 0 then 1 else -1) := by
      intro x y
      have h2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
      have h11 : (1 : ZMod 2) + 1 = 0 := rfl
      have h10 : (1 : ZMod 2) ≠ 0 := by decide
      rcases h2 x with rfl | rfl <;> rcases h2 y with rfl | rfl <;> simp [h11, h10]
    exact key a2 b2

def chpsC : AddChar (E0 × H) ℂ := chC * psC

def Gsig (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (y : ℝ) : ℂ :=
  GPsi D ell 0 y + GPsi D ell psC y - GPsi D ell chC y - GPsi D ell chpsC y

def fPl (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] : ℝ := ((PhiSet (H := H)).card : ℝ)

def delta2 (T2 : Finset H) : ℝ := (T2.card : ℝ) / (Fintype.card H : ℝ)

def ThickPartTranslateMean : Prop :=
  ∀ (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H) (t : H) (A b : ℝ), 0 < A → 0 < b →
    (1 / (Fintype.card H : ℂ)) * ∑ u0 : H, (1 / ((PhiSet (H := H)).card : ℂ)) *
        ∑ g ∈ univ.filter (fun g : E0 × H => ¬ InPhi g ∧ IsThickAt T2 u0 (partner t g)),
          ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * (b : ℂ) * GPsi D ell ψ (A / b)
      = ((delta2 T2 * b / 2 : ℝ) : ℂ) * Gsig D ell (A / b)

def topExcess (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ) {m : ℕ} (TT : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) : ℝ :=
  (1 / (Fintype.card H : ℝ)) * ∑ u0 : H, ∑ t ∈ TT, ∑ j : Fin m,
    (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re)

def ThinScales (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (X' θ : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, ∀ y : ℝ, X' / 3 ≤ y → ‖GPsi D ell ψ y‖ ≤ y * θ

def LipW (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) : Prop :=
  ∀ (ψ : AddChar (E0 × H) ℂ) (A w w' : ℝ), 0 < A → 0 < w → 0 < w' →
    ‖(w : ℂ) * GPsi D ell ψ (A / w) - (w' : ℂ) * GPsi D ell ψ (A / w')‖ ≤ 3 * A / min w w' * |w - w'|

def DerivInt (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (Cd : ℝ) : Prop :=
  (∀ ψ : AddChar (E0 × H) ℂ, ψ ≠ 0 → ∀ y z : ℝ, 1 ≤ y → 1 ≤ z →
      ‖GPsi D ell ψ y - GPsi D ell ψ z‖ ≤ |y - z| * (Real.log (max y z) + Cd + ‖ell ψ‖)) ∧
  (∀ y z : ℝ, 1 ≤ y → 1 ≤ z → |Gz y - Gz z| ≤ Cd * |y - z|)

def ValuesAtX (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (x ε CL : ℝ) : Prop :=
  ∀ ψ : AddChar (E0 × H) ℂ, (ψ = psC ∨ ψ = chC ∨ ψ = chpsC) →
    ‖GPsi D ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ ‖ell ψ‖ ≤ CL * Real.log x

def NodeSizes {m : ℕ} (T2 : Finset H) (b b' η : ℝ) (w : H → Fin m → E0 × H → ℝ) : Prop :=
  (∀ u0 j ρ, InPhi ρ → 0 < w u0 j ρ) ∧
  (∀ u0 j ρ, IsThickAt T2 u0 ρ → b ≤ w u0 j ρ ∧ w u0 j ρ ≤ b + η + 1) ∧
  (∀ u0 j ρ, InPhi ρ → ¬ IsThickAt T2 u0 ρ → w u0 j ρ ≤ 2 * b')

def moveCost (x Cd CL : ℝ) : ℝ := Cd + 3 * (Real.log (x + 1) + Cd + CL * Real.log x)

def GrowthInequalityHypotheses (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (N : ℕ) {m : ℕ} (TT T2 : Finset H) (a : H → ℝ)
    (w : H → Fin m → E0 × H → ℝ) (x ε b b' η X' θ Cd CL Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < b ∧ 0 ≤ η ∧ 0 < X' ∧ 0 < b' ∧ b' * X' ≤ x * b ∧ 0 ≤ θ ∧ 0 ≤ Cd ∧
  (∀ t ∈ TT, |a t / b - x| ≤ 1) ∧
  NodeSizes T2 b b' η w ∧
  (∀ u0 j t ρ, t ∈ TT → InPhi ρ → a t / w u0 j ρ ≤ N) ∧
  topExcess D N ell TT a w ≤ Err ∧
  ThinScales D ell X' θ ∧ LipW D ell ∧ DerivInt D ell Cd ∧ ValuesAtX D ell x ε CL

def GrowthInequalityExplicit : Prop :=
  AskMainBalance (H := H) → ∀ (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err →
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 3 * x ^ ((1 : ℝ) / 2 + ε) - moveCost x Cd CL)
      ≤ Err + (TT.card : ℝ) * m * (2 * fPl H * (x + 1) * b * θ)
        + (TT.card : ℝ) * m * (6 * fPl H * (x + 1) * (η + 1))

def SmallCosts (x ε f b η θ Cd CL : ℝ) : Prop :=
  moveCost x Cd CL ≤ x ^ ((1 : ℝ) / 2 + ε) ∧ 2 * f * (x + 1) * θ ≤ 1 / x ∧ 6 * f * (x + 1) * (η + 1) ≤ b / x

def GrowthInequalityForm : Prop :=
  AskMainBalance (H := H) → ∀ (D : ArithData H), HostFacts D →
  ∀ (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ) (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    (x ε b b' η X' θ Cd CL Err : ℝ),
    GrowthInequalityHypotheses D ell N TT T2 a w x ε b b' η X' θ Cd CL Err → SmallCosts x ε (fPl H) b η θ Cd CL →
    (TT.card : ℝ) * m * b * (delta2 T2 / 2) * (Gz x - 4 * x ^ ((1 : ℝ) / 2 + ε))
      ≤ Err + 2 * (TT.card : ℝ) * m * b / x

end

def SizeWindows (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err : ℝ) : Prop :=
  3 ≤ x ∧ 0 < ε ∧ 0 ≤ C ∧ 0 < n ∧ 0 < b ∧ 0 ≤ aE ∧ aE ≤ 2 * x * b ∧
  x ^ (-(ε / 8)) * n / 2 ≤ nT ∧
  x ^ (-ε) ≤ (nT2 : ℝ) / n ∧ nT2 ≤ n ∧
  x ^ ((1 : ℝ) / 2 - ε) ≤ m ∧ (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2) ∧
  x * m ≤ k ∧ k ≤ (n : ℝ) ^ 2 * x ^ ((1 : ℝ) / 2 - ε) ∧
  Err ≤ x ^ (C * ε) * ((nT : ℝ) * aE * (1 + (m : ℝ) ^ 2 / k)
    + m * ((2 * n) * m * b * x ^ ε + nT2 * k * b * x ^ ε / (n * (n * x ^ (-ε))))) ∧
  26 ≤ x ^ (3 * ε / 8)

def GrowthSizeBound : Prop :=
  ∀ (C ε x : ℝ) (n nT nT2 m : ℕ) (b k aE Err Gx : ℝ), SizeWindows C ε x n nT nT2 m b k aE Err →
    (nT : ℝ) * m * b * (((nT2 : ℝ) / n) / 2) * (Gx - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤ Err + 2 * (nT : ℝ) * m * b / x →
    Gx ≤ x ^ ((1 : ℝ) / 2 + (C + 3) * ε)

section
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]

end

def LipWAll : Prop :=
  ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ),
    LipW D ell

def DerivIntAll : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ (H : Type) [AddCommGroup H] [Fintype H] [DecidableEq H] (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ), DerivInt D ell Cd

end Formalism.LFunctionChainParameters.ThickSetMeanBounds
end
end

-- bundled from Formalism.SizeWindowBrackets.SlopesHypothesisFinitePlaces
section
open Module NumberField

noncomputable section

namespace Formalism.LFunctionChainParameters.slopeLatticeData

open Formalism.HN

abbrev FinPl (K : Type) [Field K] [NumberField K] := {p : Ideal (𝓞 K) // p.IsMaximal}

def idealPow {K : Type} [Field K] [NumberField K] (n : FinPl K →₀ ℤ) :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  n.prod fun w k => ((w.1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) ^ k


def modLat {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (σ : FinPl K →₀ ℤ) (N : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Formalism.HermitianLatticesTheory.idealSmul ((idealPow (-σ) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) N

def lenAt {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (w : FinPl K) (A B : Submodule (𝓞 K) V) : ℕ∞ :=
  haveI := w.2.isPrime
  Module.length (Localization.AtPrime w.1)
    (LocalizedModule w.1.primeCompl (A ⧸ B.comap A.subtype))

end Formalism.LFunctionChainParameters.slopeLatticeData
end
end

