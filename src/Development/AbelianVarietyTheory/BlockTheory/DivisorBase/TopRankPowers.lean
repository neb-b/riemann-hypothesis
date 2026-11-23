module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers

def CplxEq {K V : Type} [Field K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ) {m m' : ℕ}
    (c : Fin m → ℂ) (v : Fin m → V) (c' : Fin m' → ℂ) (v' : Fin m' → V) : Prop :=
  letI := σ.toAlgebra
  (∑ i, c i ⊗ₜ[K] v i : ℂ ⊗[K] V) = ∑ k, c' k ⊗ₜ[K] v' k

def cD (D : ℕ) : ℝ := 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial

section OneField

variable {K : Type} [Field K] [NumberField K]

section Geo

variable (G : Geo K) (s : Fin G.D → Fin G.N → K) (σ : K →+* ℂ)

def mulPow {a j l : ℕ} (h : j + a = l) (α : MonoDeg (Fin G.D) a) : G.Sec j →ₗ[K] G.Sec l :=
  mulMono (isLB_tens G.K.isLB G.isLBA) G.isLB (G.sec s) α ((Nat.cast_add j a).symm.trans (congrArg _ h))

variable {G s} (hs : G.IsGood s)

end Geo

section Data

variable (X : Data K) (s : Fin X.D → Fin X.N → K) (σ : K →+* ℂ)

theorem add_sub_D : X.D + (X.T - X.D) = X.T := Nat.add_sub_cancel' ((Nat.le_succ _).trans X.le_T)

def spaceP : Submodule K (X.Sec X.T) :=
  ⨆ α : MonoDeg (Fin X.D) (X.T - X.D), (X.V X.D).map (mulPow X.toGeo s (add_sub_D X) α)

def spaceV : Submodule K (X.Sec X.T) := X.global X.T ⊔ spaceP X s

variable {X s} (hs : X.IsGood s)

end Data

end OneField

variable {F : Type} [Field F] [NumberField F] (X : Data F)


variable (E : Type) [Field E] [NumberField E] [Algebra F E]

variable {E}

def Complexify : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (β : (F →+* ℂ) → ℝ), IsTotallyComplex F → (∀ σ, 0 < β σ) →
    X.MulStable → X.MulBound β →
      (∀ σ, X.MulBoundAt σ (β σ)) ∧
        ∀ (E : Type) [Field E] [NumberField E] [Algebra F E], (X.baseChange E).MulStable

end GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
