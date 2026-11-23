module

public import Formalism.CoboundaryTransfers.Statement

@[expose] public section

noncomputable section

namespace Formalism.CoboundaryTransfers

def DiagramChase₂ : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (e : ℕ) (c : O),
    CokerKilled S e → RatSurj S → W₀.TorsKilled c → Lifts S ((B.p : O) ^ e * c)

def CoboundaryTransfer : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (δ : D →ₗ[O] D) (R : Polynomial O) (a k : ℕ) (cΓ : O),
    B.PhiX k → M ≤ k * (a + 1) →
    (∀ y, B.X • δ y = W.γ y - y) →
    (∀ y, W.QInv y → Polynomial.aeval δ (Polynomial.X * R) y ∈ W.N) →
    (∀ y, W.QInv y → (B.p : O) • y ∈ W.N → y ∈ W.N) →
    (∀ y, W.QInv y → cΓ • y ∈ W.N → y ∈ W.N) →
    (∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      cΓ • (B.X • n) = (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z') →
    (∀ n ∈ W.N, ∃ z ∈ W.N, B.X ^ (a + 1) • n = B.X ^ (a + 1) • z - W.φ (B.X ^ (a + 1) • z)) →
    W.TorsKilled (R.eval 0 * cΓ)

def GradedStep : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (u : O), B.GammaX u → ∀ i : ℕ, ∀ n ∈ W.N, ∃ n' ∈ W.N,
      W.γ (B.X ^ i • n) - (u ^ i) • (B.X ^ i • n) = B.X ^ (i + 1) • n'

def GammaOnto : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
    (W : WachMod B M D) (u : O) (a : ℕ),
    (∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W.N, ∃ n' ∈ W.N,
      W.γ (B.X ^ i • n) = u ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n') →
    ∀ n ∈ W.N, ∃ x ∈ W.N, ∃ z' ∈ W.N,
      (∏ i ∈ Finset.Icc 1 a, (1 - u ^ i)) • (B.X • n) =
        (W.γ (B.X • x) - B.X • x) + B.X ^ (a + 1) • z'

def LiftHf : Prop :=
  ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (B : Base O A) (M : ℕ)
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (H₁ H₂ : Type) [AddCommGroup H₁] [Module O H₁] [AddCommGroup H₂] [Module O H₂]
    (cl₁ : W₁.Z1 →ₗ[O] H₁) (cl₂ : W₂.Z1 →ₗ[O] H₂) (Hf₁ : Submodule O H₁)
    (Hf₂ : Submodule O H₂) (g : H₁ →ₗ[O] H₂) (eW : ℕ) (c : O),
    ClNat S.π cl₁ cl₂ g →
    (∀ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 → cl₁ pr ∈ Hf₁) →
    HfInt W₂ cl₂ Hf₂ eW → Lifts S c →
    ∀ κ ∈ Hf₂, ∃ κ₁ ∈ Hf₁, g κ₁ = ((B.p : O) ^ eW * c) • κ

end Formalism.CoboundaryTransfers
