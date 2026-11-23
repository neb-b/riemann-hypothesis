module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.ThetaGL

namespace GlobalTheory.Published

def HoweDualityGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r n : ℕ)
    (μ : kˣ →* ℂˣ), IsSmoothChar μ →
    (∀ (V W W' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
      (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W)
      (τ' : Representation ℂ (GL (Fin n) k) W'), IsSmooth σ → σ.IsIrreducible → IsSmooth τ → τ.IsIrreducible →
      IsSmooth τ' → τ'.IsIrreducible → OmQuot μ σ τ → OmQuot μ σ τ' → Nonempty (τ.Equiv τ')) ∧
    (∀ (V V' W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ (GL (Fin r) k) V) (σ' : Representation ℂ (GL (Fin r) k) V')
      (τ : Representation ℂ (GL (Fin n) k) W), IsSmooth σ → σ.IsIrreducible → IsSmooth σ' → σ'.IsIrreducible →
      IsSmooth τ → τ.IsIrreducible → OmQuot μ σ τ → OmQuot μ σ' τ → Nonempty (σ.Equiv σ'))

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.Published

def MinguezThetaGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n m : ℕ), 1 ≤ n → 1 ≤ m →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) W), IsSmooth π → π.IsIrreducible →
    (∃ f : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] W, f ≠ 0 ∧ ∀ (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)),
      (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 (1 : GL (Fin m) k) h Φ → f Φ' = π h (f Φ)) →
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π' : Representation ℂ (GL (Fin m) k) V),
      IsSmooth π' ∧ π'.IsIrreducible ∧ OmQuot 1 π' π ∧
      (∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π'' : Representation ℂ (GL (Fin m) k) V'),
        IsSmooth π'' → π''.IsIrreducible → OmQuot 1 π'' π → Nonempty (π''.Equiv π')) ∧
      ∀ f f' : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] W,
        (∀ F ∈ ({f, f'} : Set (SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] W)),
          ∀ (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)),
            (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 g h Φ → F Φ' = TensorProduct.map (π' g) (π h) (F Φ)) →
        f ≠ 0 → ∃ c : ℂ, f' = c • f

namespace MinguezThetaGL

end MinguezThetaGL

end GlobalTheory.Published
end
end

