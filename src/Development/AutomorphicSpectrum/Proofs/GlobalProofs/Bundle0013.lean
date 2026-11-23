module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0002
public import GroundTheory.AutomorphicForms.GL2.GJUnramifiedCosets
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SphericalZetaCosets

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

def TotPos (F : Type) [Field F] (x : F) : Prop := ∀ σ : F →+* ℝ, 0 < σ x

def congUnits {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) : Set (𝓞 F)ˣ :=
  {u | ((u : 𝓞 F) - 1 ∈ 𝔣) ∧ TotPos F ((u : 𝓞 F) : F)}

def openCone {F : Type} [Field F] {r : ℕ} (v : Fin r → F) : Set F :=
  {x | ∃ t : Fin r → ℚ, (∀ i, 0 < t i) ∧ x = ∑ i, (t i : F) * v i}

def IsConeDomain {F : Type} [Field F] [NumberField F] (𝔣 : Ideal (𝓞 F)) {ι : Type} (r : ι → ℕ) (v : ∀ c, Fin (r c) → F) : Prop :=
  (∀ c, 0 < r c) ∧ (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, TotPos F (v c i)) ∧
    ∀ x : F, TotPos F x → ∃! p : congUnits 𝔣 × ι, (((p.1 : (𝓞 F)ˣ) : 𝓞 F) : F) * x ∈ openCone (v p.2)

def ClassParam {F : Type} [Field F] [NumberField F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) {J : Type} (r : J → ℕ) (y : J → 𝓞 F)
    (v : ∀ j, Fin (r j) → 𝓞 F) : Prop :=
  𝔟 ≠ ⊥ ∧ (∀ j, y j ∈ 𝔟 ∧ TotPos F (y j : F)) ∧ (∀ j i, v j i ∈ 𝔟 ∧ TotPos F (v j i : F)) ∧
    (∀ j, r j ≤ Module.finrank ℚ F) ∧
    ∃ e : (Σ j, (Fin (r j) → ℕ)) ≃ {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞},
      ∀ p, (e p).1 * 𝔟 = Ideal.span {y p.1 + ∑ i, (p.2 i : 𝓞 F) * v p.1 i}


open Classical in
def classWeight {F : Type} [Field F] [NumberField F] (l : ℕ) (𝔠 I : Ideal (𝓞 F)) : ℚ := if I ≤ 𝔠 then (l : ℚ) - 1 else -1

def GoodWeight (l : ℕ) {r : ℕ} (w : (Fin r → ℕ) → ℚ) : Prop :=
  (∀ m i, w (m + (Pi.single i l : Fin r → ℕ)) = w m) ∧ ∀ m i, ∑ e ∈ Finset.range l, w (m + (Pi.single i e : Fin r → ℕ)) = 0

def coneTerm {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (m : Fin r → ℕ) : ℂ :=
  ∏ j, (((b j + ∑ i, a j i * (m i : ℝ) : ℝ) : ℂ) ^ (-s))

def AbelContinuation : Prop :=
  ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ),
    r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w →
      ∃ T : ℂ → ℂ, Differentiable ℂ T ∧
        (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) ∧
        ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ q : ℚ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (q : ℝ)) →
          ∃ q : ℚ, T (-(p : ℂ)) = (q : ℂ)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegrandEqOnPiece
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.ZetaSph

theorem zeta_spherical : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ), UnrChar nrm q χ α → ∀ (φ : GL (Fin c) F → ℂ), IsSphFn O nrm χ φ → ∀ (κ : Measure (GL (Fin c) F)), κ.IsMulLeftInvariant → κ (GLint O c : Set (GL (Fin c) F)) = 1 → ∀ σ : ℝ, (∀ i, ‖α i‖ * (q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) < 1) → IntegrableOn (fun g => φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ (σ) : ℝ) : ℂ)) (Mint O c) κ ∧ ∫ g in Mint O c, φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ (σ) : ℝ) : ℂ) ∂κ = ∏ i : Fin c, (1 - α i * (((q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) : ℝ) : ℂ))⁻¹ :=
  _root_.UpperTheory.Reformulated.B.SphericalZetaCosets.zeta_spherical

end GlobalTheory.CompanionTheory.ZetaSph
end

