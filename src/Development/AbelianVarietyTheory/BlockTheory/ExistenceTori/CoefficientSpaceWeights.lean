module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Formalism.LocalToGlobal.Divisibility.CoefMod

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial Formalism.BasicNotions Formalism.L2.Pj Formalism.L2.DIV

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev Psi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Type := {τ : E →+* ℂ // InPsi H τ}

instance instFintypePsi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : Fintype (Psi H) := Fintype.ofFinite _

def IsPartFam (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : Prop :=
  ∀ (σ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult σ → a (σ, j) ≤ a (σ, i)

def part (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (σ : E →+* ℂ) (i : ℕ) : ℕ :=
  if i < Dw.mult σ then a (σ, i) else 0

theorem part_anti {Dw : Datum H} {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (σ : E →+* ℂ) :
    Antitone (part Dw a σ) := by
  intro i j hij
  unfold part
  by_cases hj : j < Dw.mult σ
  · rw [if_pos hj, if_pos (lt_of_le_of_lt hij hj)]
    exact ha σ i j hij hj
  · rw [if_neg hj]
    exact Nat.zero_le _

def lamP (Dw : Datum H) (n : ℕ) {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (d : Psi H → ℤ) (τ : Psi H) :
    DomWeight n where
  w i := (part Dw a τ.1 i.val : ℤ) - (part Dw a (ComplexEmbedding.conjugate τ.1) (Fin.rev i).val : ℤ) + d τ
  anti := by
    intro i j hij
    have h1 := part_anti ha τ.1 (show i.val ≤ j.val from hij)
    have h2 := part_anti ha (ComplexEmbedding.conjugate τ.1)
      (show (Fin.rev j).val ≤ (Fin.rev i).val from Fin.rev_le_rev.mpr hij)
    simp only
    omega

variable {l : Level H} (Dw : Datum H) (c : Coeff l) (n : ℕ)

def embPsi : Psi H → E →+* c.F := fun τ => embF c τ.1

variable {a : (E →+* ℂ) × ℕ → ℕ} (ha : IsPartFam Dw a) (d : Psi H → ℤ)

abbrev CoefSp : Type := VV c.F (lamP Dw n ha d)

def coefRep : GL (Fin n) E →* Module.End c.F (CoefSp Dw c n ha d) :=
  rhoVr (embPsi c) (lamP Dw n ha d)


open Classical in
def coefAct (γ : Matrix (Fin n) (Fin n) E) : CoefSp Dw c n ha d →ₗ[c.F] CoefSp Dw c n ha d :=
  if h : IsUnit γ then coefRep Dw c n ha d h.unit else 0

theorem coefAct_coe (g : GL (Fin n) E) :
    coefAct Dw c n ha d (g : Matrix (Fin n) (Fin n) E) = coefRep Dw c n ha d g := by
  unfold coefAct
  rw [dite_eq_left g.isUnit, IsUnit.unit_of_val_units]

def vacChar (γ : Matrix (Fin n) (Fin n) E) : c.F := ∏ τ : Psi H, embPsi c τ γ.det ^ (-(d τ))

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  have := lam.anti hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)


end GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights

namespace GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField

end GlobalTheory.IndefiniteRowSideFullHecke.CoefficientSpaceWeights
