module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007

@[expose] public section

noncomputable section

namespace GlobalTheory.UCls

open NumberField Matrix GlobalTheory.AdLat ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Inst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def SelfDualLat (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) : Prop :=
  (∀ a b, cc (G a b) = G b a) ∧ G.det ≠ 0 ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin r → E)) = ⊤ ∧
    ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm G x y)) ↔ x ∈ Λ

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)

def massBd (E : Type) [Field E] [NumberField E] (r M h : ℕ) : ℝ :=
  2 * h * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2)

def TorusBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → 1 ≤ M → Unr E → SelfDualLat G Λ →
    torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M ≤ (classNumber E * M ^ (2 * fdeg E) : ℕ)

def MassBound : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M h m : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (X : Fin m → Data E r)
    (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E))
    (x0 : ∀ i, Frame (X i).Ψ r) (FF : ∀ i, Set (V (nd (X i)))),
    2 ≤ r → 3 ≤ M → Unr E → SelfDualLat G Λ →
    torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M ≤ h →
    (∀ i, IsUA (IsCMField.complexConj E) G (g i)) →
    (∀ i j, UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) → i = j) →
    (∀ i, (X i).Gm = G ∧ (X i).Ψ = Ψ ∧
      ((X i).Λ : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧
      (∀ γ, γ ∈ (X i).Γ ↔ IsUStab G (X i).Λ γ ∧
        ∀ x ∈ (X i).Λ, ∃ y ∈ (X i).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) ∧
      IsOrth (X i) (x0 i) ∧ IsFundSet (X i) (x0 i) (FF i)) →
    ∑ i, muF (X i) (x0 i) (FF i) ≤ ENNReal.ofReal (massBd E r M h)

end GlobalTheory.UCls
