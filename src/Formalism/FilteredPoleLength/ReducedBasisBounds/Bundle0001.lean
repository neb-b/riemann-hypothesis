module

public import Mathlib

@[expose] public section

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.AlternatingBinomial
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Real

def TieBoundN : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) →
    ∀ (Γ : AddSubgroup V) (x : V),
      (∀ y ∈ Γ, B x x / 2 ≤ B (x + y) (x + y) / 2) →
      ∀ g ∈ Γ, ∀ N : ℕ, 2 ≤ N →
        B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 =
            (N : ℝ) * B x g + (N : ℝ) ^ 2 * (B g g / 2) ∧
        (N : ℝ) * ((N : ℝ) - 1) * (B g g / 2) ≤
            B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2 - B x x / 2 ∧
        (0 < B g g → B x x / 2 < B (x + (N : ℝ) • g) (x + (N : ℝ) • g) / 2)

def DetProductRest : Prop :=
  ∀ (i c : ℕ) (ε : ℝ), 0 ≤ ε → ε ≤ 1 →
    ((2 : ℝ) ^ c + ε) ^ i - (2 : ℝ) ^ (c * i) ≤ (i : ℝ) * ε * ((2 : ℝ) ^ c + 1) ^ i

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.FourTermSumBoundOfParameters
section
namespace Formalism.LatticeBaseChangeAlt

def FourTermSumBound : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ : ℝ), 0 ≤ d → 0 < T → 0 < ga → 0 ≤ PP → 0 ≤ D →
    0 ≤ RR ^ 2 * c + 1 / T → κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4 →
    PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

def FourTermSumBoundOfParameters : Prop :=
  ∀ (d PP D κ T c RR ga C k f b m δ₂ q DF g₀ : ℝ), 0 ≤ d → 0 < T → T ≤ ga → 0 < PP → 1 ≤ D →
    1 ≤ RR → 0 < q → 0 ≤ C → 0 ≤ k → 0 ≤ f → 0 ≤ b → 0 < m → 0 < δ₂ →
    κ ≤ C * k * f * b →
    PP ^ 3 * T ≤ f * m * b * δ₂ / 4 →
    4 * C * PP ^ 2 * D ^ 3 * k / (m * δ₂) ≤ T →
    c = RR * PP * DF ^ 2 / q → 1 ≤ g₀ → T * c * g₀ ≤ 1 →
    RR ^ 4 * PP ^ 3 * DF ^ 2 ≤ q → PP ^ 2 ≤ T → 2 ≤ PP ^ 2 →
      d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T ≤
        d * f * m * b * δ₂

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.GFiniteOrderUnipotent
section
open scoped BigOperators
open Polynomial Finset

namespace Formalism.LatticeBaseChangeAlt

def GHadamard : Prop :=
  ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ),
    |M.det| ≤ ∏ j, Real.sqrt (∑ i, M i j ^ 2)

end Formalism.LatticeBaseChangeAlt
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.ParameterInequalities
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset Matrix
open scoped RealInnerProductSpace BigOperators

def CompletingSquare : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (B : LinearMap.BilinForm ℝ V),
    (∀ x y, B x y = B y x) → (∀ x, 0 ≤ B x x) →
    ∀ (q : ℝ), 0 < q → ∀ χ : V,
      (∀ u : V, -(B χ χ / 2) / q ≤ B χ u + q * (B u u / 2)) ∧
      B χ ((-(1 / q)) • χ) + q * (B ((-(1 / q)) • χ) ((-(1 / q)) • χ) / 2) = -(B χ χ / 2) / q

def PackingCount : Prop :=
  ∀ (n : ℕ) (P : Finset (EuclideanSpace ℝ (Fin n))) (δ R : ℝ), 0 < δ → δ ≤ R →
    (∀ x ∈ P, ‖x‖ ≤ R) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → δ ≤ dist x y) →
    (P.card : ℝ) ≤ (3 * R / δ) ^ n

def DetPerturbation : Prop :=
  ∀ (𝕜 : Type) [NormedField 𝕜] (i : ℕ) (κ : Type) [Fintype κ] (w : κ → Fin i → 𝕜)
    (σ₀ : Fin i → κ) (ε : Fin i → κ → 𝕜) (Δmax : ℝ),
    (∀ σ : Fin i → κ, ‖(Matrix.of fun a j => w (σ j) a).det‖ ≤ Δmax) →
    ‖(Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det -
        (Matrix.of fun a j => w (σ₀ j) a).det‖ ≤
      ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax

def DetPerturbNumeric : Prop :=
  ∀ ρ : ℕ, 1 ≤ ρ → (1 + (ρ : ℝ) ^ (-(3 : ℝ) / 2) / 10) ^ ρ - 1 ≤ 1 / 2

def CauchyBinetMax : Prop :=
  ∀ (i N r : ℕ) (M : Matrix (Fin i) (Fin N) ℂ), M * Mᴴ = 1 → N ≤ r →
    ∃ s : Fin i → Fin N, StrictMono s ∧ (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(M.submatrix id s).det‖

end Formalism.LatticeBaseChangeAlt
end
end

-- bundled from Formalism.FilteredPoleLength.ReducedBasisBounds.TransvectionIsometry
section
noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset

def GammaL : Prop :=
  ∀ (T D r nW n' ap am : ℝ), 0 ≤ D → 0 ≤ r → r ≤ nW → 0 ≤ n' → n' ≤ nW →
    (D + 2) * nW + 2 * r ≤ T → 40 * (D + 2) ≤ T → 1.9 * T ≤ ap → 1.9 * T ≤ am →
      max T (2 * r + n' + 2 * (T + D + 2)) ≤ ap + am + nW - r + 1

def OrderSharp : Prop :=
  ∀ (lamQ lamQs lam1 lB d' rd f : ℝ), 0 < f → 0 < rd → 0 ≤ d' → 0 ≤ lB → 0 ≤ lamQs → 0 < lam1 →
    lamQ ^ 2 ≤ (1 / 2) * lB * lamQs ^ 2 → lamQs * lam1 ≤ d' → 2 * f / rd ^ 2 ≤ lam1 ^ 2 →
      lamQ ^ 2 ≤ lB * d' ^ 2 * rd ^ 2 / (4 * f)

def NearestPlane : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (n : ℕ) (v : Fin n → V),
    LinearIndependent ℝ v → ∀ x ∈ Submodule.span ℝ (Set.range v),
      ∃ c : Fin n → ℤ, ‖x - ∑ i, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖v i‖ ^ 2

def GaussianTailBound : Prop :=
  ∀ (ι : Type) (h : ι → ℝ) (g : ℕ) (R0 : ℝ), 0 < R0 → 16 * (2 * (g : ℝ) + 1) ≤ R0 ^ 2 →
    (∀ i, R0 ≤ h i) →
    (∀ R : ℝ, R0 ≤ R → ∀ S : Finset ι, (∀ i ∈ S, h i ≤ R) → (S.card : ℝ) ≤ (3 * R / R0) ^ (2 * g)) →
      Summable (fun i => Real.exp (-(h i) ^ 2 / 16)) ∧
        ∑' i, Real.exp (-(h i) ^ 2 / 16) ≤ 2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)

def BallVolume : Prop :=
  ∀ (D : ℕ) (rr : ℝ), 0 < rr →
    MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (2 * D))) rr) =
      ENNReal.ofReal (Real.pi ^ D * rr ^ (2 * D) / (D.factorial : ℝ))

end Formalism.LatticeBaseChangeAlt
end
end

