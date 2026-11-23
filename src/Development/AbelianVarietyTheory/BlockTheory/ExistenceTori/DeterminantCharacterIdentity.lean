module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight MvPolynomial
open scoped nonZeroDivisors Classical

section Minors

variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (R : Type) [CommRing R]

def leadMinor (col : ∀ σ : T, Fin (r σ) → Fin n) (σ : T) (i : Fin (r σ)) : MvPolynomial (Letter T r n) R :=
  Matrix.det (Matrix.of fun s t : Fin (i.val + 1) =>
    (X ⟨σ, Fin.castLE (Nat.succ_le_of_lt i.isLt) s, col σ (Fin.castLE (Nat.succ_le_of_lt i.isLt) t)⟩ :
      MvPolynomial (Letter T r n) R))

def gap (a : T × ℕ → ℕ) (σ : T) (i : Fin (r σ)) : ℕ :=
  a (σ, i.val) - if i.val + 1 < r σ then a (σ, i.val + 1) else 0

def minorProd (col : ∀ σ : T, Fin (r σ) → Fin n) (a : T × ℕ → ℕ) : MvPolynomial (Letter T r n) R :=
  ∏ σ : T, ∏ i : Fin (r σ), leadMinor r n R col σ i ^ gap r a σ i

end Minors

section Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}


def conjId (H : Host E) (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 E) := 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)

end Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def push {n : ℕ} (g : Matrix (Fin n) (Fin n) E) :
    MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  aeval fun ℓ => letB c ℓ.1 ℓ.2.1 (fun k => g k ℓ.2.2)

section Coeff

variable {n : ℕ} {T : Type} [AddCommGroup T] [Module c.F T] [Module (𝓞 c.F) T] [IsScalarTower (𝓞 c.F) c.F T]

end Coeff

def MovesDatum {n : ℕ} (J : Subgroup (UA E n)) (ψ : J →* c.Fˣ) (ph : (Fin n → ConjQ Dw l) → c.F) : Prop :=
  ∀ (k : J) (κ : Fin n → Fin n → 𝓞 E),
    (∀ a b, ∃ u ∈ intAd E, star (k.1.1 a b) - diagE E (κ a b : E) = (l.M : AdE E) * u) →
      ∀ x, ph (fun a => ∑ b, κ a b • x b) = ((ψ k : c.Fˣ) : c.F) * ph x

end GlobalTheory.IndefiniteRowSideFullHecke.DeterminantCharacterIdentity
