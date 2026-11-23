module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def wtSize (lam : (E →+* ℂ) → DomWeight a) : ℕ :=
  ∑ τ : E →+* ℂ, ∑ k : Fin a, ((lam τ).w k).natAbs

def IntMat (u : HeightOneSpectrum (𝓞 E)) (x : Matrix (Fin a) (Fin a) (u.adicCompletion E)) : Prop :=
  ∀ i j, x i j ∈ u.adicCompletionIntegers E

def IsIntegralOpW (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (w₀ : HeightOneSpectrum (𝓞 E))
    (f : UA E a →₀ ℂ) : Prop :=
  ∀ g ∈ f.support, g ∈ finU (E := E) (n := a) ∧ (∀ u, ¬ Apart u w₀ → cLoc u g = 1) ∧
    ∃ d : ℕ, (∀ u : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ u.asIdeal →
        IntMat u (((l : u.adicCompletion E) ^ d) • ((cLoc u g : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E))) ∧
        IntMat u (((l : u.adicCompletion E) ^ d) • (((cLoc u g)⁻¹ : GL (Fin a) (u.adicCompletion E)) :
          Matrix (Fin a) (Fin a) (u.adicCompletion E)))) ∧
      ‖ι.symm (f g)‖ ≤ ((l : ℝ)⁻¹) ^ (a * d * wtSize lam)

def HasTypeVec (w₀ : HeightOneSpectrum (𝓞 E)) (K : Subgroup (UA E a)) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E)))
    {A : Type} [Group A] (θ : J →* A) (χ : A →* ℂˣ) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ φ ∈ U, φ ≠ 0 ∧ (∀ x ∈ K, RU E a x φ = φ) ∧
    ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

end GlobalTheory.CongW
