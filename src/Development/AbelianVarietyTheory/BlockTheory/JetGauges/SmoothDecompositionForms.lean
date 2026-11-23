module

public import Mathlib
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply

@[expose] public section

open Matrix Finset
open scoped InnerProductSpace
open PI.UpqRep

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms

abbrev Ix (k r : ℕ) := Fin (2 * r + k + 1)

abbrev Mx (k r : ℕ) := Matrix (Ix k r) (Ix k r) ℂ

def Kmax (k r : ℕ) : Set (Mx k r) := UH (Hpk k r) ∩ (Matrix.unitaryGroup (Ix k r) ℂ : Set _)

structure HRep (k r : ℕ) : Type 1 where

  H : Type
  [instNorm : NormedAddCommGroup H]
  [instInner : InnerProductSpace ℂ H]
  [instComplete : CompleteSpace H]

  σ : Mx k r → (H →L[ℂ] H)
  isURep : IsURepOn (UH (Hpk k r)) σ

attribute [instance] HRep.instNorm HRep.instInner HRep.instComplete

variable {k r : ℕ}

def HRep.smooth (R : HRep k r) : Set R.H := smoothVecs (k := k) (r := r) R.σ

def LieWord (k r : ℕ) (w : List (Mx k r)) : Prop := ∀ X ∈ w, InLieHpk k r X

def HRep.semi (R : HRep k r) (Ws : List (List (Mx k r))) (v : R.H) : ℝ :=
  (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

structure IsSmoothMap (R₁ R₂ : HRep k r) (A : R₁.H → R₂.H) : Prop where
  maps : ∀ v ∈ R₁.smooth, A v ∈ R₂.smooth
  map_add : ∀ v ∈ R₁.smooth, ∀ w ∈ R₁.smooth, A (v + w) = A v + A w
  map_smul : ∀ (a : ℂ), ∀ v ∈ R₁.smooth, A (a • v) = a • A v
  cont : ∀ w, LieWord k r w → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w' ∈ Ws, LieWord k r w') ∧
    ∀ v ∈ R₁.smooth, ‖dsigW (k := k) (r := r) R₂.σ w (A v)‖ ≤ C * R₁.semi Ws v

section Tensor

variable {ι : Type} [Fintype ι]

def tensSmooth (ι : Type) (R : HRep k r) : Set (ι → R.H) := {x | ∀ c, x c ∈ R.smooth}

def tensAct (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) (g : Mx k r) (x : ι → R.H) : ι → R.H :=
  fun c => ∑ d, ρ g c d • R.σ g (x d)

def pureT {E : Type} [AddCommGroup E] [Module ℂ E] (a : ι → ℂ) (v : E) : ι → E := fun c => a c • v

def tensForm (A : Matrix ι ι ℂ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : ι → H) : ℂ :=
  ∑ c, ∑ d, A c d * ⟪y c, x d⟫_ℂ

def flat (A : Matrix ι ι ℂ) (y : ι → ℂ) : ι → ℂ := star y ᵥ* A

def contr (A : Matrix ι ι ℂ) (ω : ι → ℂ) {E : Type} [AddCommGroup E] [Module ℂ E] (x : ι → E) : E :=
  ∑ d, flat A ω d • x d

def IsSmoothMapInto (R₁ R : HRep k r) (A : R₁.H → ι → R.H) : Prop :=
  ∀ c, IsSmoothMap R₁ R fun v => A v c

structure IsSmoothMapFrom (R R₂ : HRep k r) (A : (ι → R.H) → R₂.H) : Prop where
  maps : ∀ x ∈ tensSmooth ι R, A x ∈ R₂.smooth
  map_add : ∀ x ∈ tensSmooth ι R, ∀ y ∈ tensSmooth ι R, A (x + y) = A x + A y
  map_smul : ∀ (a : ℂ), ∀ x ∈ tensSmooth ι R, A (a • x) = a • A x
  cont : ∀ w, LieWord k r w → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ w' ∈ Ws, LieWord k r w') ∧
    ∀ x ∈ tensSmooth ι R, ‖dsigW (k := k) (r := r) R₂.σ w (A x)‖ ≤ C * ∑ c, R.semi Ws (x c)

structure IsSmoothDecomp (ρ : Mx k r → Matrix ι ι ℂ) (R : HRep k r) {J : Type} [Fintype J] (Rs : J → HRep k r)
    (io : ∀ j, (Rs j).H → ι → R.H) (p : ∀ j, (ι → R.H) → (Rs j).H) : Prop where
  io_cont : ∀ j, IsSmoothMapInto (Rs j) R (io j)
  p_cont : ∀ j, IsSmoothMapFrom R (Rs j) (p j)
  io_equiv : ∀ j, ∀ g ∈ UH (Hpk k r), ∀ v ∈ (Rs j).smooth, io j ((Rs j).σ g v) = tensAct ρ R g (io j v)
  p_equiv : ∀ j, ∀ g ∈ UH (Hpk k r), ∀ x ∈ tensSmooth ι R, p j (tensAct ρ R g x) = (Rs j).σ g (p j x)
  p_io : ∀ j, ∀ v ∈ (Rs j).smooth, p j (io j v) = v
  p_io_ne : ∀ i j, i ≠ j → ∀ v ∈ (Rs j).smooth, p i (io j v) = 0
  sum_io_p : ∀ x ∈ tensSmooth ι R, ∑ j, io j (p j x) = x

structure IsSignedDecomp (ρ : Mx k r → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (R : HRep k r) {J : Type} [Fintype J]
    (Rs : J → HRep k r) (io : ∀ j, (Rs j).H → ι → R.H) (p : ∀ j, (ι → R.H) → (Rs j).H) (ep : J → ℝ) : Prop
    extends IsSmoothDecomp ρ R Rs io p where
  sign : ∀ j, ep j = 1 ∨ ep j = -1
  form_eq : ∀ j, ∀ x ∈ (Rs j).smooth, ∀ y ∈ (Rs j).smooth, tensForm A (io j x) (io j y) = (ep j : ℂ) * ⟪y, x⟫_ℂ
  orth : ∀ i j, i ≠ j → ∀ x ∈ (Rs i).smooth, ∀ y ∈ (Rs j).smooth, tensForm A (io i x) (io j y) = 0

variable [DecidableEq ι]

structure IsFormRep (k r : ℕ) (ρ : Mx k r → Matrix ι ι ℂ) (A : Matrix ι ι ℂ) (l : ℕ) : Prop where
  map_one : ρ 1 = 1
  map_mul : ∀ g ∈ UH (Hpk k r), ∀ g' ∈ UH (Hpk k r), ρ (g * g') = ρ g * ρ g'
  smooth : ∀ c d, SmoothOnH (Hpk k r) fun g => ρ g c d
  herm : Aᴴ = A
  sq : A * A = 1
  inv : ∀ g ∈ UH (Hpk k r), (ρ g)ᴴ * A * ρ g = A
  unitK : ∀ g ∈ Kmax k r, ρ g ∈ Matrix.unitaryGroup ι ℂ
  growth : ∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ∀ c d, ‖ρ g c d‖ ≤ C * Real.sqrt (hs g) ^ l

end Tensor

section Checks

variable {ι : Type} [Fintype ι]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms

end
