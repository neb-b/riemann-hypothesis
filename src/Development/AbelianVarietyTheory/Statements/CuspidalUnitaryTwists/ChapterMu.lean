module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform

@[expose] public section

noncomputable section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup
open scoped MatrixGroups Real ComplexConjugate

namespace GlobalTheory.EisM

open UpperTheory.V.Af

def Zm {R : Type*} [CommRing R] (k l : ℕ) (u v : ℤ → R) (F : ℕ → ℕ → R) : ℕ → R := fun n =>
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ x ∈ p.1.divisorsAntidiagonal, ∑ y ∈ p.2.divisorsAntidiagonal,
    if l ∣ p.1 ∨ l ∣ p.2 then 0 else (x.1 : R) ^ (k - 2) * u x.1 * v y.1 * F x.1 y.2

def tw2 (N : ℕ) (s : ℂ) : ℤ → ℂ := fun B => (if (B : ZMod N) = 1 then 1 else 0) - s * (if (B : ZMod N) = -1 then 1 else 0)

def mesMu (k l : ℕ) (u v : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (f : ZMod (l ^ m) → ℂ) : ℂ :=
  val B c l α m (Zm k l u v (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)))

structure EigAll (k N l : ℕ) (χ : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) : Prop extends
    EigF k N l χ t α B c where
  kill : ∀ (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), ε ≠ χ → MF k (N * l) (ch ε) a → lam B c a = 0

structure MeasMu {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (ψ : DirichletCharacter ℂ l) (α : ℂ)
    (B : ℕ) (c : ℕ → ℂ) (v : ℂ) : Prop where
  compat : ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (f' : ZMod (l ^ (m + 1)) → ℂ), (∀ y, f (-y) = s * f y) →
    (∀ y : ℕ, f' y = f y) → mesMu (2 * e + 1) l u w α B c (m + 1) f' = mesMu (2 * e + 1) l u w α B c m f
  bound : ∃ C : ℝ, ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ y, ‖ι.symm (f y)‖ ≤ δ) →
    ‖ι.symm (mesMu (2 * e + 1) l u w α B c m f)‖ ≤ C * δ
  field : ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ (m : ℕ) (f : ZMod (l ^ m) → ℂ)
    (E' : IntermediateField ℚ_[l] (PadicAlgCl l)), E ≤ E' → (∀ y, ι.symm (f y) ∈ E') → ι.symm (mesMu (2 * e + 1) l u w α B c m f) ∈ E'
  interp : ∃ C : ℝ, ∀ m : ℕ, 1 ≤ m → ∀ (f : ZMod (l ^ m) → ℂ) (δ : ℝ), 0 ≤ δ → (∀ y, f (-y) = s * f y) →
    (∀ a d : ℕ, ¬ l ∣ a → ¬ l ∣ d → ‖ι.symm (f ((a : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹) - ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)‖ ≤ δ) →
    ‖ι.symm (mesMu (2 * e + 1) l u w α B c m f - v)‖ ≤ C * δ

end GlobalTheory.EisM

end
