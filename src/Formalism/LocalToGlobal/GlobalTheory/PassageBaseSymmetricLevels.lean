module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.DivPassage
public import Formalism.LocalToGlobal.GlobalTheory.DivPassageP
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

@[expose] public section

set_option linter.style.haveILetI false

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage2

open Formalism.L2.Indef Formalism.L2.GlobalTheoryTheory.DivPassage

section Chars

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ]

end Chars

section TP

variable {K : Type} [Field K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}

variable [NumberField K]

end TP

section Norms

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

end Norms

section Adj

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ}
  (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)

end Adj

section Lat

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

end Lat

section Gen

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K] [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

theorem rows_gen (hL : A.LatG) {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (P : Matrix (Fin A.Dg) (Fin A.Dg) K)
    (hD : 0 < D) (hinj : Function.Injective ι.mulVec) (hr : LinearMap.range ι.mulVecLin = LinearMap.range P.mulVecLin) :
    A.partLat P ≠ ⊥ := by
  intro hb
  have hspan := A.span_partLat hL P
  rw [hb, Submodule.bot_coe, Submodule.span_zero_singleton] at hspan
  obtain ⟨x, hx⟩ : ∃ x : Fin D → K, x ≠ 0 := ⟨fun _ => 1, fun h => one_ne_zero (congrFun h ⟨0, hD⟩)⟩
  have hmem : ι *ᵥ x ∈ LinearMap.range P.mulVecLin := by
    rw [← hr]
    exact ⟨_, rfl⟩
  rw [← hspan, Submodule.mem_bot] at hmem
  exact hx (hinj (by rw [hmem, Matrix.mulVec_zero]))

end Gen

section Triv

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Triv

end Formalism.L2.GlobalTheoryTheory.DivPassage2
