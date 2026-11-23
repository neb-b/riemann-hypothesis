module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

def dInv (E : Type) [Field E] [NumberField E] (j : ℕ) : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹) ^ j

def SelfDual (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Λ.FG ∧ ∀ v, v ∈ Λ ↔ ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range

def frameLat {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin (r + 1)) (a : E), a ∈ dInv E (r - (b : ℕ)) ∧ v = a • fun i => P i b}

def PrimIn {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  M ≤ Λ ∧ ∀ v ∈ Λ, v ∈ Submodule.span E (M : Set (Fin n → E)) → v ∈ M

def pairLat {n r : ℕ} (g : ℕ) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  frameLat P ⊔ frameLat (((g : E)⁻¹) • (P' - P))

def latMap {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ.map (γ.mulVecLin.restrictScalars (𝓞 E))

abbrev Tri (E : Type) [Field E] [NumberField E] (n r : ℕ) : Type :=
  Submodule (𝓞 E) (Fin n → E) × Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E

def GenConf (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Set (Tri E n r) :=
  {x | SelfDual σ J x.1 ∧ (x.2.1, x.2.2) ∈ XZ σ J T T' Z ∧ PrimIn (pairLat g x.2.1 x.2.2) x.1}

def FrameLats (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {Λ | SelfDual σ J Λ ∧ PrimIn (frameLat P) Λ}

end GlobalTheory.SgGlob
