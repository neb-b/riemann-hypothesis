module

public import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DefsMod
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.Bundle0001
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.InducedSectionsSpanStatement
public import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.RationalBitableauLatticeStatement
public import Mathlib
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.PathBasisTheorem
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Bundle0003
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.CorA3primeB
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.Bundle0002
public import Formalism.ThetaLogCoordinates.JacobiPathWeights.JacobiMinorProofs.LeIffLtColHeight

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.BrCore
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

section B1
end B1

section B2
end B2

section B9
theorem global_sections_schur (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.GlobalSectionsSchur D := fun n _ mu R _ _ hR =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_one n mu R hR
end B9

section lowerOffDiagonalCoeff
theorem bracket_polynomial_span (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.BracketPolynomialSpan D := fun n _ mu hmu =>
  Formalism.InvariantFactorPaths.ColumnFamilies.highest_weight_corollary_two n mu hmu
end lowerOffDiagonalCoeff

section Mod

end Mod

section B6
end B6

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestPathFrom
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def isV {N : ℕ} (LL : Letters (Fin N)) : ℕ → Bool := fun i => if h : i < N then LL.vec ⟨i, h⟩ else true

def Bn {N : ℕ} (B : Fin N → ℕ) : ℕ → ℕ := fun i => if h : i < N then B ⟨i, h⟩ else 0

def ext {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ℕ → Fin n → ℤ := fun i => if h : i < N + 1 then mu ⟨i, h⟩ else 0

def res (N : ℕ) {n : ℕ} (μ : ℕ → Fin n → ℤ) : Fin (N + 1) → Fin n → ℤ := fun i => μ i.val

def iv (N n : ℕ) : Fin N × Fin n → ℕ × Fin n := fun x => (x.1.val, x.2)

def RestPathTo : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) (ext P.mu) N

def RestPathFrom : Prop :=
  ∀ (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : ℕ → Fin n → ℤ),
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsPath n (isV LL) (Bn B) μ N → ∃ P : PPath n N LL B, P.mu = res N μ

def RestStd : Prop :=
  ∀ (n N : ℕ) (mu : Fin (N + 1) → Fin n → ℤ) (I : ℤ → Finset (Fin n)),
    IsSt mu I ↔ Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd (pEnd mu) I

def RestPsi : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (P : PPath n N LL B)
    (I : ℤ → Finset (Fin n)), Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsIndex (pEnd P.mu) I →
    rename (iv N n) (Psi R P.mu I) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) (ext P.mu) N I

def RestPol : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (B : Fin N → ℕ),
    (Pol R n B).map (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.polB R n N (Bn B)

end Formalism.MainNotions.G.ColumnFamilies
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ToralGalois
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem weight_projector_mem_weight_space {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (htop : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (mu : Fin n → ℤ) (e : Module.End K V) (he : IsWtProj E mu e)
    (x : V) : e x ∈ weightSp E mu := by
  have hx : x ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by rw [htop]; trivial
  refine Submodule.iSup_induction (fun nu => weightSp E nu) (motive := fun y => e y ∈ weightSp E mu) hx ?_ ?_ ?_
  · intro nu y hy
    by_cases h : nu = mu
    · subst h
      rw [he.1 y hy]
      exact hy
    · rw [he.2 nu h y hy]
      exact zero_mem _
  · rw [map_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [map_add (f := _)]
    exact add_mem ha hb

theorem adm_eleven (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := by
  intro p _ O _ _ _ _ _S n V _ _ _ _ E mu La hrep _hdom _hiso hlat hproj

  have hstab : ∀ u ∈ UZmon E, ∀ x ∈ La, u x ∈ La := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu => exact hlat.1 u hu
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, y, hy, -, rfl⟩
    exact hstab u hu y hy
  · intro y hy u hu e he
    exact ⟨hproj _ (hstab u hu y hy) mu e he, weight_projector_mem_weight_space E hrep.2.2 mu e he _⟩

end Formalism.MainNotions.G.ColumnFamilies
end
end

