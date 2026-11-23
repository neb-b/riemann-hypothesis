module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.AffChar

@[expose] public section

noncomputable section

open MvPolynomial Filter Topology

namespace PositivityTheory.Rg.Fx

def Subst : Prop :=
  ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (Λ₀ : ι → ℂ) (M : Matrix ι ι' ℝ) (f : EP ι),
    (∀ lam : ι' → ℂ, ev lam (aff Λ₀ M f) = ev (fun i => Λ₀ i + ∑ j, (M i j : ℂ) * lam j) f) ∧
    ∀ (ι'' : Type) [Fintype ι''] (Λ₁ : ι' → ℂ) (N : Matrix ι' ι'' ℝ),
      aff Λ₁ N (aff Λ₀ M f) = aff (fun i => Λ₀ i + ∑ j, (M i j : ℂ) * Λ₁ j) (M * N) f

def Generators : Prop :=
  ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), ∃ K : ℝ, ∀ (k : ℕ) (P : MvPolynomial (τ × Fin n) ℂ),
    P.totalDegree ≤ k → (∀ w : τ → Equiv.Perm (Fin n), rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) P = P) →
    ∃ G : MvPolynomial (τ × Fin n) ℂ, aeval blockE G = P ∧ G.totalDegree ≤ k ∧ l1 G ≤ K ^ (k + 1) * l1 P

def Rearrange : Prop :=
  ∀ (ι κ : Type) [Fintype ι] (b : Fam ι κ) (A M : Type) [CommRing A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M]
    [Module A M] [IsScalarTower ℂ A M] (D : Fin b.r → A) (τ : Multiplicative (Fin b.r → ℝ) →* A) (φ : M →ₗ[ℂ] ℂ),
    (∀ (v : Fin b.r → ℝ) (m : M), HasSum
      (fun k : ℕ => (k.factorial : ℂ)⁻¹ * φ ((∑ j, (v j : ℂ) • D j) ^ k • m)) (φ (τ (Multiplicative.ofAdd v) • m))) →
    ∀ (F : KF ι κ) (m : M), HasSum
      (fun k => φ (eval₂ (aeval fun i => algebraMap ℂ A (b.Λ i) + ∑ j, (b.emb i j : ℂ) • D j).toRingHom
        (fun k' => lift D τ (b.h k')) (pieceK k F) • m))
      (φ (lift D τ (b.sub F) • m))

end PositivityTheory.Rg.Fx
