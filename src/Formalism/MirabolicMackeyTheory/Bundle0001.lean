module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Statement

@[expose] public section

-- bundled from Formalism.MirabolicMackeyTheory.StatementL
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]

def lix (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z) : ℤ :=
  Formalism.HermitianLatticesTheory.lidx w.asIdeal A B

def sc [IsScalarTower (𝓞 K) K Z] (a : K) (A : Submodule (𝓞 K) Z) : Submodule (𝓞 K) Z :=
  A.map ((a • (LinearMap.id : Z →ₗ[K] Z)).restrictScalars (𝓞 K))

def cut [IsScalarTower (𝓞 K) K Z] (W : Submodule K Z) (A : Submodule (𝓞 K) Z) :
    Submodule (𝓞 K) Z :=
  A ⊓ W.restrictScalars (𝓞 K)

def IsLatIn (W : Submodule K Z) (A : Submodule (𝓞 K) Z) : Prop :=
  A.FG ∧ Submodule.span K (A : Set Z) = W

def eig {P : Type} [Group P] (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) :
    Submodule K Z :=
  ⨅ u : U, LinearMap.ker (ρ (u : P) - ((ψ (u : P) : 𝓞 K) : K) • (LinearMap.id : Z →ₗ[K] Z))

def IsMackey {P A : Type} [Group P] [Monoid A] (U : Subgroup P) (ψ : P → A) : Prop :=
  ψ 1 = 1 ∧ (∀ u ∈ U, ∀ u' ∈ U, ψ (u * u') = ψ u * ψ u') ∧
    ∀ h : P, h ∉ U → ∃ u ∈ U, h⁻¹ * u * h ∈ U ∧ ψ (h⁻¹ * u * h) ≠ ψ u

end Defs

def IdxMono : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (W : Submodule K Z) (A B B' : Submodule (𝓞 K) Z),
    IsLatIn W A → IsLatIn W B → IsLatIn W B' → B ≤ B' → lix w A B' ≤ lix w A B

def IdxScaleIn : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (W : Submodule K Z) (A B : Submodule (𝓞 K) Z),
    IsLatIn W A → IsLatIn W B → ∀ a : K, a ≠ 0 →
      IsLatIn W (sc a B) ∧ lix w A (sc a B) = lix w A B + (finrank K W : ℤ) * vw w a

def IdxCutLe : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (W W' : Submodule K Z) (A B : Submodule (𝓞 K) Z),
    IsLatIn W A → IsLatIn W B → B ≤ A → W' ≤ W →
      IsLatIn W' (cut W' A) ∧ 0 ≤ lix w (cut W' A) (cut W' B) ∧
        lix w (cut W' A) (cut W' B) ≤ lix w A B

def IdxTransport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
    (w : HeightOneSpectrum (𝓞 K)) (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    ∀ A B : Submodule (𝓞 K) (Fin d → K),
      lix w (A.map (φ.restrictScalars (𝓞 K))) (B.map (φ.restrictScalars (𝓞 K))) = idx w A B

def LatInter : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (A B : Submodule (𝓞 K) Z), IsLatIn ⊤ A → IsLatIn ⊤ B → ∀ a : K, a ≠ 0 → IsLatIn ⊤ (A ⊓ sc a B)

def ThreeForms : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) Z),
    IsLatIn ⊤ A → IsLatIn ⊤ B → B ≤ A →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
      ((∀ W : Submodule K Z, (lix w (cut W A) (cut W B) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) ↔
        (lix w A (A ⊓ sc a⁻¹ B) : ℝ) ≤ r)

def IdxPsiGood : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (Zψ V₀ : Submodule K Z) (M Th ThK Th0 : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th ≤ M → Th0.FG →
    Th0 ≤ Zψ.restrictScalars (𝓞 K) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    ∀ (u : ℕ), u ≠ 0 → sc (u : K) (cut Zψ ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (lix w M (M ⊓ sc a⁻¹ Th) : ℝ) ≤ r →
    ∀ (δ : ℕ), 0 < δ →
    (δ : ℤ) * lix w (cut Zψ M) (cut Zψ (M ⊓ sc a⁻¹ Th)) ≤
      lix w M (M ⊓ sc a⁻¹ Th) + (finrank K Z : ℤ) * vw w (u : K) →
      IsLatIn (Zψ ⊓ V₀) (cut V₀ Th0) ∧
      (lix w (cut (Zψ ⊓ V₀) M) (cut V₀ Th0) : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w (u : K) : ℝ)) * (finrank K (Zψ ⊓ V₀ : Submodule K Z) : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w (u : K) : ℝ)) / (δ : ℝ)

def OrthOfMackey : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    (P : Type) [Group P] [Fintype P] (ρ : Representation K P Z) (U : Subgroup P) [Fintype U]
    (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ h : P, h ∉ U → ∀ z ∈ eig ρ U ψ,
      ∑ u : U, ((ψ ((u : P)⁻¹) : 𝓞 K) : K) • ρ (u : P) (ρ h z) = 0

def LemmaGG : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (B B' : Submodule (𝓞 K) Z), IsLatIn ⊤ B → IsLatIn ⊤ B' → B' ≤ B →
    (∀ g : P, B.map ((ρ g).restrictScalars (𝓞 K)) ≤ B) →
    (∀ g : P, B'.map ((ρ g).restrictScalars (𝓞 K)) ≤ B') →
      (U.index : ℤ) * lix w (cut (eig ρ U ψ) B) (cut (eig ρ U ψ) B') ≤
        lix w B B' + (finrank K Z : ℤ) * vw w ((Nat.card U : ℕ) : K)

def MackeyProd : Prop :=
  ∀ (ι A : Type) [Fintype ι] [DecidableEq ι] [CommMonoid A] (P : ι → Type) [∀ v, Group (P v)]
    (U : ∀ v, Subgroup (P v)) (ψ : ∀ v, P v → A), (∀ v, IsMackey (U v) (ψ v)) →
      IsMackey (Subgroup.pi Set.univ U) (fun h : (∀ v, P v) => ∏ v, ψ v (h v))

def IsMirab {k : Type} [Field k] {n : ℕ} (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Prop :=
  ∀ j, h (Fin.last n) j = if j = Fin.last n then 1 else 0

def IsUniU {k : Type} [Field k] {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : Prop :=
  (∀ i, u i i = 1) ∧ ∀ i j, j < i → u i j = 0

def supd {k : Type} [Field k] {n : ℕ} (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) : k :=
  ∑ i : Fin n, u i.castSucc i.succ

def MirabolicMackey : Prop :=
  ∀ (k A : Type) [Field k] [Finite k] [CommMonoid A] (n : ℕ) (ψ : AddChar k A), ψ ≠ 1 →
    ∀ h : GL (Fin (n + 1)) k, IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) →
      ¬ IsUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) →
      ∃ u : GL (Fin (n + 1)) k, IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
        IsUniU ((h⁻¹ * u * h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∧
        ψ (supd ((h⁻¹ * u * h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ≠
          ψ (supd (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k))

def MirabolicIsMackey : Prop :=
  ∀ (k A : Type) [Field k] [Finite k] [CommMonoid A] (n : ℕ) (ψ : AddChar k A), ψ ≠ 1 →
    ∀ (P : Subgroup (GL (Fin (n + 1)) k)) (U : Subgroup P),
      (∀ h : GL (Fin (n + 1)) k, h ∈ P ↔ IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) →
      (∀ h : P, h ∈ U ↔ IsUniU ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) →
      IsMackey U (fun h : P => ψ (supd ((h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)))

def OnLocal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (V₀ : Submodule K Z) (e : Z →ₗ[K] Z), e ∘ₗ e = e → LinearMap.range e = V₀ →
    ∀ (M Th ThK Th0 X₃ X₄ : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th ≤ M → Th0.FG →
    Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K) →
    (∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M) →
    (∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn (eig ρ U ψ ⊓ V₀) X₃ → IsLatIn (eig ρ U ψ ⊓ V₀) X₄ → X₃ ≤ X₄ →
    ∀ (ε : ℝ),
    (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    LinearMap.range φ = eig ρ U ψ ⊓ V₀ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M →
    Tj.map (φ.restrictScalars (𝓞 K)) = X₄ →
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε

end Formalism.EigenvalueLevelCeiling
end
end

-- bundled from Formalism.MirabolicMackeyTheory.StatementT
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

section Defs

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def plc (w : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)

def ramw (w : HeightOneSpectrum (𝓞 K)) : ℤ := vw w ((plc w : ℕ) : K)

def ellw (w : HeightOneSpectrum (𝓞 K)) : ℝ := (plc w : ℝ) / Real.sqrt (ramw w : ℝ)

end Defs

def RamBasic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K)),
    (plc w).Prime ∧ 1 ≤ ramw w ∧ plc (conjPl w) = plc w ∧ ramw (conjPl w) = ramw w ∧
      2 / ellw w ^ 2 = (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)

def PlaceSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (X : ℕ → ℝ), (∀ p, 0 ≤ X p) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * X (plc w)) ≤ ∑ p ∈ S.image plc, Real.log (p : ℝ) * X p

def DepthCases : Prop :=
  ∀ (e ec F : ℝ),
    (∀ a : ℝ, e ≤ F + a + 1 → ec ≤ F + a + 1 → e + ec - 2 * F ≤ 2 * a + 2) ∧
    (e = 0 → ec = 0 → 0 ≤ F → e + ec - 2 * F ≤ 0) ∧
    (∀ s T β : ℝ, e ≤ s + T + 1 → ec ≤ s + T + 1 → -(2 * β) ≤ F → F ≤ 0 →
      e + ec - 2 * F ≤ 2 * (s + T + 1) + 4 * β) ∧
    (∀ s T : ℝ, e ≤ s + T + 1 → ec ≤ s + T + 1 → F = 0 → e + ec - 2 * F ≤ 2 * s + 2 * T + 2) ∧
    (∀ T nn nnc g2 : ℝ, e ≤ 2 * T - nn → ec ≤ 2 * T - nnc → nn + nnc = -(2 * F) →
      e + ec - 2 * F + 2 * g2 ≤ 4 * T + 2 * g2)

def ShareNum : Prop :=
  ∀ (dK d0 d U δq ep y del : ℝ), 0 < U → 0 < δq → 0 ≤ dK → 0 ≤ d0 → 0 ≤ ep → ep ≤ y → y ≤ 1 / 8 →
    0 ≤ del → del ≤ 1 / 4 → (1 - ep) * dK ≤ U * d0 → (1 - y) * U ≤ δq → (1 - del) * d0 ≤ d →
      dK / δq ≤ 2 * d

def UnipNum : Prop :=
  ∀ (f r d dK δq : ℝ), 0 ≤ f → 1 ≤ r → 0 ≤ d → dK / δq ≤ 3 * d →
    f * r * (r - 1) / 2 * (d + dK / δq) ≤ 2 * f * r ^ 2 * d

def BudgetNum : Prop :=
  ∀ (dK δq D B : ℝ), 0 < δq → 0 < D → 0 ≤ B → dK / δq ≤ 3 * D →
    2 * (2 * (dK * B)) / (δq * D) ≤ 12 * B

def errGood (Y X2 A1 A2 kw T : ℝ) (th add : ℕ → ℝ) (p : ℕ) : ℝ :=
  if (p : ℝ) ≤ Y then
    2 * (A1 / (p : ℝ) + kw * th p + T * add p + (if X2 < (p : ℝ) then A2 / (p : ℝ) ^ 2 else 0)) + 2
  else 0

end Formalism.EigenvalueLevelCeiling
end
end

