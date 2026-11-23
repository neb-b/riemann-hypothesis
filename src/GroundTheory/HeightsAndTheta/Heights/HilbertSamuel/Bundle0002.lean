module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeComplexRadical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def PrimeComplexRadical.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    (P.map (MvPolynomial.map (Int.castRingHom ℂ))).IsRadical

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatPrimeDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def RatPrimeDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)) (f : MvPolynomial σ ℚ), P.IsPrime → f ∉ P →
    {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ⊆
      closure {z : σ → ℂ | (∀ g ∈ P, aeval z g = 0) ∧ aeval z f ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootGridLower
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def RootGridLower.Statement : Prop :=
  ∀ (e m : ℕ) (Q : MvPolynomial (Fin e) ℤ), Q ≠ 0 → (∀ i, Q.degreeOf i < m) →
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ m = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsBounded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def RootsBounded.Statement : Prop :=
  ∀ (e : ℕ) (G : Polynomial (MvPolynomial (Fin e) ℚ)), G.Monic → ∀ y₀ : Fin e → ℂ,
    ∃ R : ℝ, ∀ᶠ y in 𝓝 y₀, ∀ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 → ‖t‖ ≤ R

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsLiftToZeros
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def RootsLiftToZeros.Statement : Prop :=
  ∀ (σ : Type) (P : Ideal (MvPolynomial σ ℚ)) (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ)
    (u : MvPolynomial σ ℚ) (G : Polynomial (MvPolynomial (Fin e) ℚ)),
    (∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
      p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P) →
    (∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Q.eval₂ (aeval ℓ).toRingHom u ∈ P → G ∣ Q) →
    ∀ (y : Fin e → ℂ) (t : ℂ), G.eval₂ (aeval y).toRingHom t = 0 →
      ∃ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) ∧ (fun j => aeval z (ℓ j)) = y ∧ aeval z u = t

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def RootsNear.Statement : Prop :=
  ∀ (e : ℕ) (G : Polynomial (MvPolynomial (Fin e) ℚ)), G.Monic →
    ∀ (y₀ : Fin e → ℂ) (t₀ : ℂ), G.eval₂ (aeval y₀).toRingHom t₀ = 0 →
      ∀ ε > 0, ∀ᶠ y in 𝓝 y₀, ∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧ dist t t₀ < ε

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSerreGraded
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def gradedSpan {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω) (n : ℕ) :
    AddSubgroup Ω :=
  AddSubgroup.closure {x | ∃ (l : Fin r) (μ : Fin q → ℕ), d l + ∑ j, μ j = n ∧ x = t l * ∏ j, w j ^ μ j}

def SerreGraded.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (q r : ℕ) (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω),
    (∃ j, w j ≠ 0) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s : Ω,
      (∀ j, w j ≠ 0 → ∃ D : ℕ, s * w j ^ D ∈ gradedSpan w d t (n + D)) → s ∈ gradedSpan w d t n

theorem gradedSpan_gen_mem {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
    (l : Fin r) (μ : Fin q → ℕ) : t l * ∏ j, w j ^ μ j ∈ gradedSpan w d t (d l + ∑ j, μ j) :=
  AddSubgroup.subset_closure ⟨l, μ, rfl, rfl⟩

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUnitApprox
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField

def UnitApprox.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (u : (F →+* ℂ) → ℝ),
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ C : ℝ, ∀ n : ℕ, ∃ ε : (𝓞 F)ˣ, ∀ sg : F →+* ℂ,
      |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ C

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

