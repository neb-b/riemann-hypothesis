module

public import Mathlib
public import Formalism.MirabolicMackeyTheory.Bundle0001

@[expose] public section

-- bundled from Formalism.MirabolicMackeyTheory.LocalConditionsWeighted
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

def OnLocalJ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (V₀ : Submodule K Z) (e : Z →ₗ[K] Z), e ∘ₗ e = e → LinearMap.range e = V₀ →
    ∀ (M Th ThK Th0 ThJ X₃ X₄ : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th ≤ M → Th0.FG →
    Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K) →
    (∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M) →
    (∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K))) → Th0 ≤ ThJ →
    IsLatIn (eig ρ U ψ ⊓ V₀) X₃ → IsLatIn (eig ρ U ψ ⊓ V₀) X₄ → X₃ ≤ X₄ →
    ∀ (ε : ℝ),
    (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    LinearMap.range φ = eig ρ U ψ ⊓ V₀ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M →
    Tj.map (φ.restrictScalars (𝓞 K)) = X₄ →
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε


open Classical in
def TwistSetDouble : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (J : Type) [Fintype J]
    (ε0 : HeightOneSpectrum (𝓞 K) → J → ℝ) (w : HeightOneSpectrum (𝓞 K)),
    ∑ j, (ε0 w j + (if conjPl w = w then 0 else ε0 (conjPl w) j)) ≤ 1 / (plc w : ℝ) ^ 2 →
      ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2


open Classical in
def OnExportSet : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ), 0 < D →
  ∀ (Tup : Type) (μ : HeightOneSpectrum (𝓞 K) → Tup) (J : Type) [Fintype J] (d : J → ℕ),
    (∀ j, d j = D) →
  ∀ (M : ∀ j, Submodule (𝓞 K) (Fin (d j) → K))
    (T : ∀ j, Tup → Submodule (𝓞 K) (Fin (d j) → K))
    (θ : ∀ j, Tup → Matrix (Fin (d j)) (Fin (d j)) K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (e0 r0 ε0 F0 errl Jx : HeightOneSpectrum (𝓞 K) → J → ℝ)
    (vU0 gq : HeightOneSpectrum (𝓞 K) → ℝ) (dK EA Rb EJ : J → ℝ) (δq E3 : ℝ), 0 < δq →
    (∀ w ∈ S, ∀ j, (idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) ≤
      (ramw w : ℝ) * ((e0 w j + vU0 w) * (d j : ℝ) + (r0 w j + dK j * vU0 w) / δq + ε0 w j)) →
    (∀ w ∈ S, ∀ j, (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) ≤
      (ramw (conjPl w) : ℝ) * ((e0 (conjPl w) j + vU0 (conjPl w)) * (d j : ℝ) +
        (r0 (conjPl w) j + dK j * vU0 (conjPl w)) / δq + ε0 (conjPl w) j)) →
    (∀ j, dK j / δq ≤ 3 * (D : ℝ)) →
    (∀ w ∈ S, 0 ≤ vU0 w ∧ vU0 (conjPl w) = vU0 w ∧ 4 * vU0 w ≤ gq w) →
    (∀ w ∈ S, ∀ j, e0 w j + e0 (conjPl w) j - 2 * F0 w j + 2 * gq w ≤ errl w j) →
    (∀ w ∈ S, ∑ j, (ε0 w j + (if conjPl w = w then 0 else ε0 (conjPl w) j)) ≤ 1 / (plc w : ℝ) ^ 2) →
    (∀ j, ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w j) ≤ EA j) →
    (∀ j, ∀ S' : Finset (HeightOneSpectrum (𝓞 K)), ∑ w ∈ S', lw w * ((ramw w : ℝ) * r0 w j) ≤ Rb j) →
    (∀ j, ∑ w ∈ S, lw w * Jx w j ≤ EJ j) →
    ∑ w ∈ S, lw w * ((ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) ≤ E3 →
      (∀ w ∈ S, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
        (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))))) * D +
          2 / ellw w ^ 2) ∧
      (∀ w ∈ S, ∑ j, ((idx w (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ) +
          (idx (conjPl w) (M j) (matLat (θ j (μ w)) (T j (μ w))) : ℝ)) ≤
        (∑ j, (2 * ((ramw w : ℝ) * F0 w j) +
            (ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ)))) +
          2 / ellw w ^ 2) * D) ∧
      (∀ j, ∑ w ∈ S, lw w * ((ramw w : ℝ) * (errl w j + (r0 w j + r0 (conjPl w) j) / (δq * (D : ℝ))) +
          Jx w j) ≤ EA j + 2 * Rb j / (δq * (D : ℝ)) + EJ j) ∧
      ∑ w ∈ S, lw w * (2 / ellw w ^ 2) ≤ E3

def ThetaIdentity : Prop :=
  ∀ (R X Y : Type) [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (θ : X →ₗ[R] Y) (eX pr : X →ₗ[R] X) (e : Y →ₗ[R] Y),
    θ ∘ₗ eX = e ∘ₗ θ → (∀ x ∈ LinearMap.range eX, x - pr x ∈ LinearMap.ker θ) →
    ∀ Mt : Submodule R X, ((Mt.map eX).map pr).map θ = (Mt.map θ).map e

def ThetaIdentityOrth : Prop :=
  ∀ (R X Y A : Type) [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Zero A]
    (θ : X →ₗ[R] Y) (eX p : X →ₗ[R] X) (e : Y →ₗ[R] Y) (h : X → X → A),
    θ ∘ₗ eX = e ∘ₗ θ → (∀ x y, h (eX x) y = h x (eX y)) →
    p ∘ₗ p = p → LinearMap.ker p = LinearMap.ker θ →
    (∀ x, x ∈ LinearMap.range p ↔ ∀ k ∈ LinearMap.ker θ, h k x = 0) →
      p ∘ₗ eX = eX ∘ₗ p ∧
      (∀ x ∈ LinearMap.range eX, p x ∈ LinearMap.range eX ∧ x - p x ∈ LinearMap.ker θ ∧
        ∀ k ∈ LinearMap.ker θ, h k (p x) = 0) ∧
      ∀ Mt : Submodule R X, ((Mt.map p).map eX).map θ = (Mt.map θ).map e

def EnlargeInitialLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M Th1 Th : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th1 → IsLatIn ⊤ Th → Th1 ≤ Th → Th ≤ M →
    ∀ (E r : ℝ),
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th1) : ℝ) ≤ E * (finrank K W : ℝ) + r) →
    ∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ E * (finrank K W : ℝ) + r

def TwChain : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (W : Submodule K Z) (e : Z →ₗ[K] Z) (A Th0 ThJ X₃ : Submodule (𝓞 K) Z),
    IsLatIn W A → IsLatIn W (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn W (ThJ.map (e.restrictScalars (𝓞 K))) → Th0 ≤ ThJ →
    ∀ ε : ℝ, (lix w A X₃ : ℝ) ≤ (lix w A (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
      (lix w A X₃ : ℝ) ≤ (lix w A (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) + ε

def ConstB : Prop :=
  ∀ (RR PP DF d' n1 nW g' qmin : ℝ), 0 ≤ RR → 1 ≤ DF → 0 ≤ d' → 0 ≤ n1 → n1 ≤ nW → 0 < qmin → qmin ≤ g' →
    d' ^ 4 * nW + 2 * d' ^ 3 ≤ PP →
      n1 * d' * (RR * d' ^ 3) / (4 * g') + 2 * (RR * d' ^ 3) * DF ^ 2 / g' ≤ RR * PP * DF ^ 2 / qmin

def LocalConditionsWeighted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (V₀ : Submodule K Z) (e : Z →ₗ[K] Z), e ∘ₗ e = e → LinearMap.range e = V₀ →
    ∀ (M Th1 Th ThK Th0 ThJ X₃ : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th1 → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th1 ≤ Th → Th ≤ M → Th0.FG →
    Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K) →
    (∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M) →
    (∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th1) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K))) → Th0 ≤ ThJ →
    IsLatIn (eig ρ U ψ ⊓ V₀) X₃ →
    ∀ (X : Type) [AddCommGroup X] [Module K X] [Module (𝓞 K) X] [IsScalarTower (𝓞 K) K X]
      (θ' : X →ₗ[K] Z) (eX pr : X →ₗ[K] X) (Mt : Submodule (𝓞 K) X),
    θ' ∘ₗ eX = e ∘ₗ θ' → (∀ x ∈ LinearMap.range eX, x - pr x ∈ LinearMap.ker θ') →
    IsLatIn (eig ρ U ψ ⊓ V₀) ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) →
    X₃ ≤ (Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K)) →
    ∀ (ε : ℝ),
    (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    LinearMap.range φ = eig ρ U ψ ⊓ V₀ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M →
    Tj.map (φ.restrictScalars (𝓞 K)) =
      ((Mt.map (eX.restrictScalars (𝓞 K))).map (pr.restrictScalars (𝓞 K))).map (θ'.restrictScalars (𝓞 K)) →
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε

def GapNum : Prop :=
  ∀ (T D nW r t h0 c : ℝ), 0 ≤ D → 0 ≤ r → 0 ≤ t → 2 ≤ nW → (D + 2) * nW + 2 * r ≤ T →
    (T + D + 2) * (T + D + 2 + 2 * r) ≤ 3.75 * T ^ 2 ∧
      (4 * T ^ 2 + 2 * t ≤ h0 → h0 ≤ c + 1 → (T + D + 2) * (T + D + 2 + 2 * r) ≤ c + 2)

end Formalism.EigenvalueLevelCeiling
end
end

-- bundled from Formalism.MirabolicMackeyTheory.StatementC
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

def AbsorbOnC : Prop :=
  ∀ (c C Cb L xe f m b k ws Se Y X2 bad : ℝ), 0 ≤ c → 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m →
    0 < b → 1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2 * c * (C * k * ws) / X2 + c * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + (14 + 10 * c) * C + Cb + 12) * xe * (f * m * b * L)

def ThetaLog4 : Prop :=
  ∀ (Y : ℝ), 0 ≤ Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) ≤ Real.log 4 * Y

def DepthSums (T Cth Cadd : ℝ) (th add : ℕ → ℝ) : Prop :=
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, th p * Real.log (p : ℝ) ≤ Cth) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → T * ∑ p ∈ Q, add p * Real.log (p : ℝ) ≤ Cadd)

end Formalism.EigenvalueLevelCeiling
end
end

