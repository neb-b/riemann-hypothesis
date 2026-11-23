module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.IsHerm

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace UpperTheory.ConvolutionTheory.G3

def Tw {G : Type} [Group G] (θ : G →* G) (x y : G) : Prop := ∃ g, y = g⁻¹ * x * θ g

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def gpol (δ : GL (Fin n) E) : E[X] := (δ * thE E n δ).val.charpoly

def lpol (w : Pl E) (y : GLw n w) : (w.adicCompletion E)[X] := (nrmL n w y).val.charpoly

def IntUniq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (gpol δ).Separable → ∀ᶠ w : Pl E in cofinite,
    locEl n w δ ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ y ∈ GlobalTheory.LFun.KGL w (n := n), lpol w y = atPl w (gpol δ) →
      ∃ k ∈ GlobalTheory.LFun.KGL w (n := n), y = k⁻¹ * locEl n w δ * thL n w k

def CptInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (δ : GL (Fin n) E), (gpol δ).Separable → ∀ᶠ w : Pl E in cofinite,
    cptPart (twCent (thL n w) (locEl n w δ)) = twCent (thL n w) (locEl n w δ) ⊓ GlobalTheory.LFun.KGL w (n := n)

def OrbUnit : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K : Subgroup G) (δ : G), (∀ k ∈ K, θ k ∈ K) → δ ∈ K →
    (∀ y ∈ K, Tw θ δ y → ∃ k ∈ K, y = k⁻¹ * δ * θ k) → cptPart (twCent θ δ) = twCent θ δ ⊓ K →
    twOrb θ K δ ((K : Set G).indicator 1) = 1

def OrbZero : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ),
    (∀ y, Tw θ δ y → f y = 0) → twOrb θ K δ f = 0

def UnitAe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (a b : ℕ) (δ₁ : GL (Fin a) E) (δ₂ : GL (Fin b) E), (gpol δ₁).Separable → (gpol δ₂).Separable → ∀ᶠ w : Pl E in cofinite,
    ∀ (y₁ : GLw a w) (y₂ : GLw b w), lpol w y₁ = atPl w (gpol δ₁) → lpol w y₂ = atPl w (gpol δ₂) →
      twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) (y₁, y₂)
        ((((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b)) : Subgroup _) : Set _).indicator 1) =
        if Tw (thL a w) (locEl a w δ₁) y₁ ∧ Tw (thL b w) (locEl b w δ₂) y₂ then 1 else 0

def Transl : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∃ u : GL (Fin n) E, (∀ g, thE E n g = u * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) g * u⁻¹) ∧
    u * UpperTheory.ConvolutionTheory.D.th (IsCMField.complexConj E) u = 1 ∧ ∀ w : Pl E, ¬ IsSplitAt w → ∀ g : GLw n w,
      (thL n w g).val = u.val.map (algebraMap E _) * ((g⁻¹ : GLw n w).val.map (cj w))ᵀ * (u⁻¹ : GL (Fin n) E).val.map (algebraMap E _)

def PolFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) →
    (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w (n := n)) → {P | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ y ∈ C w, lpol w y = atPl w P}.Finite

end UpperTheory.ConvolutionTheory.G3
