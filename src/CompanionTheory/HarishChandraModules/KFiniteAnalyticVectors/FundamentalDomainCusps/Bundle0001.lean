module

public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.CompactIntegralBoundedByQuotientNorm
section
open MeasureTheory Topology Filter
open scoped ENNReal

noncomputable section

namespace CompanionTheory.D.gk.RF

section Defs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]

def LInv {α : Type} (Γ : Subgroup G) (f : G → α) : Prop := ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x

def Disc (Γ : Subgroup G) : Prop := ∀ C : Set G, IsCompact C → (C ∩ (Γ : Set G)).Finite

def BC (h : G → ℂ) : Prop := Continuous h ∧ ∃ M : ℝ, ∀ x, ‖h x‖ ≤ M

def IsRep (μ : Measure G) (φ : G → ℂ) (Γ : Subgroup G) (h : G → ℂ) : Prop :=
  BC h ∧ LInv Γ h ∧ ∀ x, h x = ∫ y, φ y * h (x * y) ∂μ

def CuspAt (μ : Measure G) (φ : G → ℂ) (Γ : Subgroup G) (O U : Set G) (x : G) : Prop :=
  ∃ ν : Measure G, IsProbabilityMeasure ν ∧ (∀ᵐ m ∂ν, x⁻¹ * m * x ∈ U) ∧
    ∀ h, IsRep μ φ Γ h → ∀ z ∈ O, ∫ m, h (m * x * z) ∂ν = 0

def sq (μ : Measure G) (D : Set G) (h : G → ℂ) : ℝ≥0∞ := ∫⁻ x in D, ‖h x‖ₑ ^ 2 ∂μ

def Detects (μ : Measure G) (φ : G → ℂ) (Γ : Subgroup G) (D : Set G) : Prop :=
  ∃ (m : ℕ) (α : G → ℂ) (p : Fin m → G), Continuous α ∧ HasCompactSupport α ∧
    ∀ h, IsRep μ φ Γ h → sq μ D h ≠ ∞ → (∀ i, ∫ y, α y * h (p i * y) ∂μ = 0) → sq μ D h = 0

structure ParData (N : Subgroup G) (a : ℝ → G) (Ht : G → ℝ) : Prop where
  cont : Continuous a
  add : ∀ s t, a (s + t) = a s * a t
  norm : ∀ t, ∀ m ∈ N, a t * m * (a t)⁻¹ ∈ N
  hcont : Continuous Ht
  hN : ∀ m ∈ N, ∀ g, Ht (m * g) = Ht g
  ha : ∀ t g, Ht (a t * g) = t + Ht g
  bd : ∃ c : G → ℝ, Continuous c ∧ ∀ x y, |Ht (x * y) - Ht x| ≤ c y
  small : ∀ U ∈ 𝓝 (1 : G), ∃ τ : ℝ, 0 < τ ∧ ∀ t, |t| < τ → ∀ x, ∃ m ∈ N, x⁻¹ * (m * a t) * x ∈ U

end Defs

def Young : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ →
    ∀ f θ : G → ℝ≥0∞, Measurable f → AEMeasurable θ μ → LInv Γ f →
      ∫⁻ x in D, (∫⁻ y, θ y * f (x * y) ∂μ) ^ 2 ∂μ ≤ (∫⁻ y, θ y ∂μ) ^ 2 * ∫⁻ x in D, f x ^ 2 ∂μ

def CompactIntegralBoundedByQuotientNorm : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ → Disc Γ →
    ∀ B : Set G, IsCompact B → ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ f : G → ℝ≥0∞, Measurable f → LInv Γ f →
      (∫⁻ y in B, f y ∂μ) ^ 2 ≤ M * ∫⁻ x in D, f x ^ 2 ∂μ

def NearMeas : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ →
    ∀ C : Set G, IsCompact C → MeasurableSet {x | ∃ γ ∈ Γ, γ * x ∈ C} ∧ μ (D ∩ {x | ∃ γ ∈ Γ, γ * x ∈ C}) ≤ μ C

def UnifC : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (α : G → ℂ), Continuous α → HasCompactSupport α → ∃ B : Set G, IsCompact B ∧ ∀ e : ℝ, 0 < e →
      ∃ U ∈ 𝓝 (1 : G), ∀ u ∈ U, ∀ y, ‖α (u⁻¹ * y) - α y‖ ≤ e ∧ (y ∉ B → α (u⁻¹ * y) = 0 ∧ α y = 0)

def Approx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G → ℂ) (O : Set G), Integrable φ μ → IsClopen O → (∀ y, y ∉ O → φ y = 0) → ∀ e : ℝ, 0 < e →
      ∃ α : G → ℂ, Continuous α ∧ HasCompactSupport α ∧ (∀ y, y ∉ O → α y = 0) ∧ ∫ y, ‖φ y - α y‖ ∂μ ≤ e

def FarEst : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (φ α : G → ℂ) (Γ : Subgroup G) (O U B : Set G) (e : ℝ), Continuous α → HasCompactSupport α →
    (∀ y, y ∉ O → α y = 0) → IsCompact B →
    (∀ u ∈ U, ∀ y, ‖α (u⁻¹ * y) - α y‖ ≤ e ∧ (y ∉ B → α (u⁻¹ * y) = 0 ∧ α y = 0)) →
    ∀ x, CuspAt μ φ Γ O U x → ∀ h, IsRep μ φ Γ h →
      ‖∫ y, α y * h (x * y) ∂μ‖ₑ ≤ ENNReal.ofReal e * ∫⁻ y in B, ‖h (x * y)‖ₑ ∂μ

def NearEst : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ → Disc Γ →
    ∀ α : G → ℂ, Continuous α → HasCompactSupport α → ∀ C : Set G, IsCompact C → ∀ e : ℝ≥0∞, 0 < e →
    ∃ (m : ℕ) (p : Fin m → G), ∀ h : G → ℂ, BC h → LInv Γ h → (∀ i, ∫ y, α y * h (p i * y) ∂μ = 0) →
      ∀ x ∈ C, ‖∫ y, α y * h (x * y) ∂μ‖ₑ ^ 2 ≤ e * sq μ D h

def Core : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Γ : Subgroup G) [Countable Γ] (D : Set G), IsFundamentalDomain Γ D μ → Disc Γ →
    ∀ (φ : G → ℂ) (O : Set G), Integrable φ μ → IsClopen O → (∀ y, y ∉ O → φ y = 0) →
    (∀ U ∈ 𝓝 (1 : G), ∃ C : Set G, IsCompact C ∧ ∀ x, (∃ γ ∈ Γ, γ * x ∈ C) ∨ CuspAt μ φ Γ O U x) →
    Detects μ φ Γ D

def FiniteDimensionalFromLinearForms : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) (D : Set G) (φ : G → ℂ), Integrable φ μ → Detects μ φ Γ D →
    ∀ S : Submodule ℂ (Lp ℂ 2 (μ.restrict D)),
      (∀ F ∈ S, F ∈ closure {F' : Lp ℂ 2 (μ.restrict D) | ∃ h, IsRep μ φ Γ h ∧ (F' : G → ℂ) =ᵐ[μ.restrict D] h}) →
      FiniteDimensional ℂ S

def IdemZero : Prop :=
  ∀ (A : Type) [NormedRing A] (Q : ℝ → A), Continuous Q → (∀ s, Q s * Q s = Q s) → Tendsto Q atTop (𝓝 0) →
    ∀ s, Q s = 0

def SelTw : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G → ℂ), Integrable φ μ → (∀ w, ∫ y, φ y * φ (y⁻¹ * w) ∂μ = φ w) →
    ∀ (N : Subgroup G) (a : ℝ → G) (Ht : G → ℝ), ParData N a Ht →
    ∀ (s : ℝ) (F : G → ℂ), BC F → LInv N F → (∀ t x, F (a t * x) = F x) →
      ∀ x, ∫ y, φ y * (F (x * y) * Complex.exp (((s * Ht (x * y) : ℝ) : ℂ) * Complex.I)) ∂μ = 0

def Sel : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    (φ : G → ℂ), Integrable φ μ → (∀ w, ∫ y, φ y * φ (y⁻¹ * w) ∂μ = φ w) →
    ∀ (N : Subgroup G) (a : ℝ → G) (Ht : G → ℝ), ParData N a Ht →
    ∀ F : G → ℂ, BC F → LInv N F → ∀ x, ∫ y, φ y * F (x * y) ∂μ = 0

def FundIn : Prop :=
  ∀ (N : Type) [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] (Λ : Subgroup N), Disc Λ →
    ∀ V : Set N, IsOpen V → (∀ m, ∃ l ∈ Λ, l * m ∈ V) →
    ∃ D : Set N, MeasurableSet D ∧ D ⊆ V ∧ ∀ m, ∃! l : Λ, (l : N) * m ∈ D

def Avg : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G),
    IsClosed (N : Set G) → Λ ≤ N → Disc Λ → ∀ V : Set G, IsOpen V → IsCompact (closure V) →
    (∀ m ∈ N, ∃ l ∈ Λ, l * m ∈ V) →
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ (∀ᵐ m ∂ν, m ∈ V) ∧
      ∀ u : G → ℂ, BC u → LInv Λ u → ∀ m₀ ∈ N, ∀ y, ∫ m, u (m * (m₀ * y)) ∂ν = ∫ m, u (m * y) ∂ν

end CompanionTheory.D.gk.RF
end
end

-- bundled from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.FundamentalDomainCusps.NilpAlg
section
open Matrix

noncomputable section

namespace CompanionTheory.D.gk.RF

variable {K : Type} [Field K] [StarRing K] {n : ℕ}

def hf (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : K := star x ⬝ᵥ (J *ᵥ y)

def perp (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) where
  carrier := {z | ∀ w ∈ W, hf J w z = 0}
  add_mem' := fun ha hb w hw => by
    have h1 := ha w hw
    have h2 := hb w hw
    simp only [hf] at h1 h2 ⊢
    rw [mulVec_add, dotProduct_add, h1, h2, add_zero]
  zero_mem' := fun w _ => by simp [hf]
  smul_mem' := fun c z hz w hw => by
    have h1 := hz w hw
    simp only [hf] at h1 ⊢
    rw [mulVec_smul, dotProduct_smul, h1, smul_zero]

def Isot (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) : Prop := W ≤ perp J W

def Lowers (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) (A : Matrix (Fin n) (Fin n) K) : Prop :=
  (∀ w ∈ W, A *ᵥ w = 0) ∧ (∀ z ∈ perp J W, A *ᵥ z ∈ W) ∧ ∀ z, A *ᵥ z ∈ perp J W

def InL (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) (X : Matrix (Fin n) (Fin n) K) : Prop :=
  Xᴴ * J + J * X = 0 ∧ Lowers J W X

def InZ (J : Matrix (Fin n) (Fin n) K) (W : Submodule K (Fin n → K)) (X : Matrix (Fin n) (Fin n) K) : Prop :=
  Xᴴ * J + J * X = 0 ∧ (∀ z ∈ perp J W, X *ᵥ z = 0) ∧ ∀ z, X *ᵥ z ∈ W

def xw (J : Matrix (Fin n) (Fin n) K) (w b : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  vecMulVec w (star b ᵥ* J) - vecMulVec b (star w ᵥ* J)

def ex2 (X : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := 1 + X + (2 : K)⁻¹ • (X * X)

def NilpAlg : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)), Jᴴ = J → IsUnit J.det → Isot J W →
    (∀ X, InL J W X → (ex2 X)ᴴ * J * ex2 X = J ∧ Lowers J W (ex2 X - 1) ∧ ex2 X * ex2 (-X) = 1 ∧ InL J W (-X)) ∧
    (∀ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J → Lowers J W (g - 1) → ∃ X, InL J W X ∧ g = ex2 X) ∧
    (∀ X Y, InL J W X → InL J W Y → InL J W (X + Y) ∧ InZ J W ((2 : K)⁻¹ • (X * Y - Y * X)) ∧
      ex2 X * ex2 Y = ex2 (X + Y + (2 : K)⁻¹ • (X * Y - Y * X))) ∧
    (∀ Z, InZ J W Z → InL J W Z ∧ InZ J W (-Z) ∧ ∀ X, InL J W X → Z * X = 0 ∧ X * Z = 0)

def NilpRep : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] [CharZero K] (n : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (W : Submodule K (Fin n → K)), Jᴴ = J → IsUnit J.det → Isot J W →
    ∀ (d : ℕ) (w : Fin d → Fin n → K), Submodule.span K (Set.range w) = W →
    (∀ b : Fin d → Fin n → K, (∀ i, b i ∈ perp J W) → InL J W (∑ i, xw J (w i) (b i))) ∧
    (∀ b : Fin d → Fin n → K, (∀ i, b i ∈ W) → InZ J W (∑ i, xw J (w i) (b i))) ∧
    (∀ X, InL J W X → ∃ b : Fin d → Fin n → K, (∀ i, b i ∈ perp J W) ∧ X = ∑ i, xw J (w i) (b i)) ∧
    (∀ X, InZ J W X → ∃ b : Fin d → Fin n → K, (∀ i, b i ∈ W) ∧ X = ∑ i, xw J (w i) (b i))

def Gap : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (A : Set (Fin n → K)) (ν : (Fin n → K) → ℝ) (s₀ η : ℝ), 0 < s₀ → 0 < η → η < 1 →
    (∃ u ∈ A, u ≠ 0 ∧ ν u ≤ s₀ * η ^ (n + 1)) →
    ∃ t : ℝ, 0 < t ∧ t ≤ s₀ ∧ ∃ (d : ℕ) (w : Fin d → Fin n → K), d ≤ n ∧ (∀ i, w i ∈ A ∧ ν (w i) ≤ η * t) ∧
      Submodule.span K (Set.range w) ≠ ⊥ ∧ ∀ u ∈ A, ν u ≤ t → u ∈ Submodule.span K (Set.range w)

end CompanionTheory.D.gk.RF
end
end

