module

public import Mathlib

@[expose] public section

noncomputable section

open Finset Polynomial

namespace Formalism.CohomologicalDescent

theorem lw_det_block {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (s : m) (hs : ∀ j, b j = b s → j = s) :
    (M.toSquareBlock b (b s)).det = M s s := by
  let _ : Unique {a // b a = b s} :=
    { default := ⟨s, rfl⟩
      uniq := fun j => Subtype.ext (hs j.1 j.2) }
  rw [Matrix.det_unique]
  rfl

theorem lw_det_inj {R m : Type*} [CommRing R] [DecidableEq m] [Fintype m]
    (M : Matrix m m R) (b : m → ℕ) (hM : M.BlockTriangular b) (hb : Function.Injective b) :
    M.det = ∏ i, M i i := by
  rw [Matrix.BlockTriangular.det hM, Finset.prod_image]
  · exact Finset.prod_congr rfl (fun i _ => lw_det_block M b i (fun j hj => hb hj))
  · intro x _ y _ hxy
    exact hb hxy

end Formalism.CohomologicalDescent
