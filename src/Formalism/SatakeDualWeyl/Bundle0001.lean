module

public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.StatementC
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG

section Defs

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def latS (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {O : Type} [CommRing O]
    [Algebra O E] (Λ : Submodule O (n → E)) : Submodule S (n → E ⊗[F] R) :=
  Submodule.span S ((fun x : n → E => fun i => inclE (F := F) R (x i)) '' (Λ : Set (n → E)))

def levelVL [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix n n E) (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) :
    Subgroup (GL n (E ⊗[F] v.adicCompletion F)) :=
  level (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
    (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ)

def levelAfL [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) :
    Subgroup (GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  level (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)))
    (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)

def evalV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

def prV [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* E ⊗[F] v.adicCompletion F :=
  (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v)).toRingHom

end Defs

def LevelAfLStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    levelAfL σ J (stdLat (n := n) (A := E) (𝓞 E)) = levelAf σ J

def ClassSetFiniteL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    IsHerm (σ : E →+* E) J → IsUnit J.det → IsTotDef σ J →
    ∀ Λ : Submodule (𝓞 E) (n → E), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    Finite (ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))))

def AdelicStabFiniteL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    IsHerm (σ : E →+* E) J → IsUnit J.det → IsTotDef σ J →
    ∀ Λ : Submodule (𝓞 E) (n → E), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    ∀ g : UPts σ J (FiniteAdeleRing (𝓞 F) F),
      Finite (stabAt ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g)

def DefSig : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (n : Type) [Fintype n] [DecidableEq n]
    (σ : E →ₐ[F] E) (J : Matrix n n E) (ι : F →+* ℝ) (τ : E →+* ℂ),
    τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ →
    τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) →
    IsHerm (σ : E →+* E) J → IsUnit J.det →
    (IsDefiniteAt σ J ι ↔
      (HasSignature (J.map τ) (Fintype.card n) 0 ∨ HasSignature (J.map τ) 0 (Fintype.card n)))

def StdFormDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) → NumberField.IsTotallyReal F →
    IsHerm (σ : E →+* E) (1 : Matrix n n E) ∧ IsTotDef σ (1 : Matrix n n E) ∧ IsTotDef σ (-1 : Matrix n n E)

end Formalism.UG
end
end

-- bundled from Formalism.SatakeDualWeyl.StatementE
section
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.UG

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev Ov : Subring (v.adicCompletion F) := (v.adicCompletionIntegers F).toSubring

def qV : ℕ := Ideal.absNorm v.asIdeal

def IsUnifV (ϖ : v.adicCompletion F) : Prop :=
  Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

def ordV (x : v.adicCompletion F) : ℤ :=
  if h : Valued.v x = 0 then 0 else -Multiplicative.toAdd (WithZero.unzero h)

def diagPow {n : ℕ} (ϖ : v.adicCompletion F) (a : Fin n → ℤ) : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
  Matrix.diagonal (fun i => ϖ ^ (a i))

def IsUpperB {n : ℕ} (b : GL (Fin n) (v.adicCompletion F)) : Prop :=
  ∀ i j : Fin n, j < i → (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j = 0

def chiDelta {n : ℕ} (α : Fin n → ℂ) (b : GL (Fin n) (v.adicCompletion F)) : ℂ :=
  ∏ i : Fin n, α i ^ (ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i)) *
    ((qV F v : ℂ) ^ (-(ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) *
      (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)))

def IsSpherical {n : ℕ} (α : Fin n → ℂ) (φ : GL (Fin n) (v.adicCompletion F) → ℂ) : Prop :=
  ∀ b g k : GL (Fin n) (v.adicCompletion F), IsUpperB F v b → k ∈ GLint (Fin n) (Ov F v) →
    φ (b * g * k) = chiDelta F v α b * φ g

def CartanDecomp : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F),
    ϖ ∈ Ov F v → IsUnifV F v ϖ →
    ∀ g : GL (Fin n) (v.adicCompletion F), ∃ a : Fin n → ℤ, Antitone a ∧
      ∃ k₁ ∈ GLint (Fin n) (Ov F v), ∃ k₂ ∈ GLint (Fin n) (Ov F v),
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) _) * diagPow F v ϖ a * (k₂ : Matrix (Fin n) (Fin n) _)

def CartanUnique : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F),
    ϖ ∈ Ov F v → IsUnifV F v ϖ → ∀ a a' : Fin n → ℤ, Antitone a → Antitone a' →
    ∀ k₁ ∈ GLint (Fin n) (Ov F v), ∀ k₂ ∈ GLint (Fin n) (Ov F v),
      (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * diagPow F v ϖ a * (k₂ : Matrix (Fin n) (Fin n) _) =
        diagPow F v ϖ a' → a = a'

def HeckeCommGL : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (k : Type) [CommRing k],
    ∀ f₁ ∈ Hecke k (GLint (Fin n) (Ov F v)), ∀ f₂ ∈ Hecke k (GLint (Fin n) (Ov F v)),
      conv (GLint (Fin n) (Ov F v)) f₁ f₂ = conv (GLint (Fin n) (Ov F v)) f₂ f₁

def SphericalExists : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (α : Fin n → ℂ),
    (∀ i, α i ≠ 0) → ∃ φ : GL (Fin n) (v.adicCompletion F) → ℂ, IsSpherical F v α φ ∧ φ 1 = 1 ∧
      ∀ ψ, IsSpherical F v α ψ → ψ = fun g => ψ 1 * φ g

def SatakeTj : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F),
    ϖ ∈ Ov F v → IsUnifV F v ϖ → ∀ (α : Fin n → ℂ), (∀ i, α i ≠ 0) →
    ∀ φ : GL (Fin n) (v.adicCompletion F) → ℂ, IsSpherical F v α φ → ∀ j : ℕ, j ≤ n →
      hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ =
        ((qV F v : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) * Multiset.esymm (Multiset.map α Finset.univ.val) j) • φ

def TjCosets : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (ϖ : v.adicCompletion F),
    ϖ ∈ Ov F v → IsUnifV F v ϖ → ∀ j : ℕ, j ≤ n →
      (Nat.card {x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) |
          Tj ℤ n (Ov F v) ϖ j x.out ≠ 0} : ℤ) * ∏ i ∈ Finset.range j, ((qV F v : ℤ) ^ (i + 1) - 1) =
        ∏ i ∈ Finset.range j, ((qV F v : ℤ) ^ (n - i) - 1)

end Formalism.UG
end
end

-- bundled from Formalism.SatakeDualWeyl.StatementF
section
noncomputable section

namespace Formalism.UG

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ordL (x : L) : ℤ := if h : Valued.v x = 0 then 0 else -Multiplicative.toAdd (WithZero.unzero h)

def intL (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] : Subring L :=
  (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer

def IsUnramInv (ϖ : L) (σ : L →+* L) (q : ℕ) : Prop :=
  (∀ x, σ (σ x) = x) ∧ (∀ x, Valued.v (σ x) = Valued.v x) ∧ σ ϖ = ϖ ∧
  Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
  (∃ x ∈ intL L, Valued.v (σ x - x) = 1) ∧ 2 ≤ q ∧
  Nat.card ((Valued.v : Valuation L (WithZero (Multiplicative ℤ))).integer ⧸
    IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring) = q ^ 2

def antiJ (L : Type) [Field L] (n : ℕ) : Matrix (Fin n) (Fin n) L :=
  fun i j => if i.val + j.val + 1 = n then 1 else 0

abbrev GU (σ : L →+* L) (n : ℕ) : Subgroup (GL (Fin n) L) := UJ σ (antiJ L n)

def KU (σ : L →+* L) (n : ℕ) : Subgroup (GU σ n) :=
  (intPts (intL L).subtype (GU σ n)).subgroupOf (GU σ n)

def IsBorelU {σ : L →+* L} {n : ℕ} (b : GU σ n) : Prop :=
  ∀ i j : Fin n, j < i → ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0

def IsUnipU {σ : L →+* L} {n : ℕ} (u : GU σ n) : Prop :=
  IsBorelU u ∧ ∀ i : Fin n, ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1

def tMat (ϖ : L) (n m : ℕ) (a : Fin m → ℤ) : Matrix (Fin n) (Fin n) L :=
  Matrix.diagonal fun i =>
    if h : i.val < m then ϖ ^ (a ⟨i.val, h⟩)
    else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then ϖ ^ (-(a ⟨n - 1 - i.val, h'.2⟩)) else 1

def chiDeltaU {σ : L →+* L} {n m : ℕ} (q : ℕ) (α : Fin m → ℂ) (b : GU σ n) : ℂ :=
  ∏ i : Fin m,
    if h : i.val < n then
      α i ^ (ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)) *
        (q : ℂ) ^ (-(ordL (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ⟨i.val, h⟩ ⟨i.val, h⟩)) *
          ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
    else 1


open Classical in
def SatU {σ : L →+* L} {n m : ℕ} (ϖ : L) (q : ℕ) (h : GU σ n → ℂ) (α : Fin m → ℂ) : ℂ := by
  classical
  exact ∑ᶠ a : Fin m → ℤ, (∏ i : Fin m, α i ^ (a i) * (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
    ∑ᶠ x : GU σ n ⧸ KU σ n,
      if ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
          (((x.out : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
            tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
              (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
      then h x.out else 0

def IsSphericalU {σ : L →+* L} {n m : ℕ} (q : ℕ) (α : Fin m → ℂ) (φ : GU σ n → ℂ) : Prop :=
  ∀ b g k : GU σ n, IsBorelU b → k ∈ KU σ n → φ (b * g * k) = chiDeltaU q α b * φ g

def SphericalExistsU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ),
    IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) →
    ∃ φ : GU σ n → ℂ, IsSphericalU q α φ ∧ φ 1 = 1 ∧ ∀ ψ, IsSphericalU q α ψ → ψ = fun g => ψ 1 * φ g

def HeckeCommU : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (k : Type) [CommRing k], IsUnramInv ϖ σ q →
    ∀ f₁ ∈ Hecke k (KU σ n), ∀ f₂ ∈ Hecke k (KU σ n), conv (KU σ n) f₁ f₂ = conv (KU σ n) f₂ f₁

def SatakeInert : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ),
    IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) →
    ∀ h ∈ Hecke ℂ (KU σ n), ∀ φ : GU σ n → ℂ, IsSphericalU q α φ →
      hAct (KU σ n) h φ = SatU ϖ q h α • φ

def SatWeyl : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ),
    IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) →
    ∀ h ∈ Hecke ℂ (KU σ n),
      (∀ π : Equiv.Perm (Fin m), SatU ϖ q h (α ∘ π) = SatU ϖ q h α) ∧
      (∀ i : Fin m, SatU ϖ q h (Function.update α i (α i)⁻¹) = SatU ϖ q h α)

def SatMul : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ),
    IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ α : Fin m → ℂ, (∀ i, α i ≠ 0) →
    ∀ h₁ ∈ Hecke ℂ (KU σ n), ∀ h₂ ∈ Hecke ℂ (KU σ n),
      SatU ϖ q (conv (KU σ n) h₁ h₂) α = SatU ϖ q h₁ α * SatU ϖ q h₂ α

end Formalism.UG
end
end

