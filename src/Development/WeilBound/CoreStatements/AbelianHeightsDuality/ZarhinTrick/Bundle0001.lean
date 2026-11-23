module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.ExistsQuat
section
namespace PositivityTheory.PrwZar

theorem exists_quat (n : ℕ) : ∃ α : Matrix (Fin 4) (Fin 4) ℤ,
    α.transpose * α = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
    α * α.transpose = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  have hn : (n : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]
    push_cast
    ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩ <;>
  · rw [hn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

end PositivityTheory.PrwZar
end

-- bundled from Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs
section
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace PositivityTheory.PrwZar.Qi

variable {K H : Type} [Field K] [CommRing H] [Algebra K H]

def pw (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : ℕ → (H →ₐ[K] H)
  | 0 => (Algebra.ofId K H).comp ε
  | n + 1 => (Algebra.TensorProduct.lmul' K).comp ((Algebra.TensorProduct.map (pw Δ ε n) (AlgHom.id K H)).comp Δ)

def CounitL (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map ((Algebra.ofId K H).comp ε) (AlgHom.id K H)).comp Δ) = AlgHom.id K H

def CounitR (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K) : Prop :=
  (Algebra.TensorProduct.lmul' K).comp
    ((Algebra.TensorProduct.map (AlgHom.id K H) ((Algebra.ofId K H).comp ε)).comp Δ) = AlgHom.id K H

def KilledCore : Prop :=
  ∀ (K H : Type) [Field K] [IsAlgClosed K] [CommRing H] [Algebra K H] [FiniteDimensional K H]
    (Δ : H →ₐ[K] H ⊗[K] H) (ε : H →ₐ[K] K), CounitL Δ ε → CounitR Δ ε →
    (∀ a b : ℕ, pw Δ ε (a * b) = (pw Δ ε a).comp (pw Δ ε b)) →
    (∃ m : ℕ, 0 < m ∧ ∀ x : H →ₐ[K] K, x.comp (pw Δ ε m) = ε) →
    ∃ N : ℕ, 0 < N ∧ pw Δ ε N = pw Δ ε 0

end PositivityTheory.PrwZar.Qi
end
end

