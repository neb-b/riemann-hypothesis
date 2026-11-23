module

public import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

@[expose] public section

open Matrix
open scoped ComplexConjugate Nat

noncomputable section

namespace CCRuleCW

open Formalism.FourierDecayAlt

section expo

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
theorem exp_intertwine (Y Z H : Matrix (Fin n) (Fin n) ℂ) (h : Y * H = H * Z) :
    NormedSpace.exp Y * H = H * NormedSpace.exp Z := by
  have hp : ∀ m : ℕ, Y ^ m * H = H * Z ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) (NormedSpace.exp Y * H) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y).mul_right H
  have h2 : HasSum (fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m)) (H * NormedSpace.exp Z) := by
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Z).mul_left H
  have e : (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) * H) = fun m : ℕ => H * ((m ! : ℂ)⁻¹ • Z ^ m) := by
    funext m
    rw [Matrix.smul_mul, hp, Matrix.mul_smul]
  rw [e] at h1
  exact h1.unique h2

set_option backward.isDefEq.respectTransparency false in
theorem exp_mem_UH (H Y : Matrix (Fin n) (Fin n) ℂ) (hY : Yᴴ * H + H * Y = 0) :
    NormedSpace.exp Y ∈ Formalism.QuantumDeterminants.UH H := by
  show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
  have h1 : Yᴴ * H = H * (-Y) := by
    rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hY
  rw [← Matrix.exp_conjTranspose, exp_intertwine _ _ _ h1, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

theorem UH_mul (H a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  calc (a * b)ᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem lie_smul (H X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ * H + H * X = 0) (c : ℝ) :
    ((c : ℂ) • X)ᴴ * H + H * ((c : ℂ) • X) = 0 := by
  rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, ← smul_add, hX, smul_zero]

end expo


end CCRuleCW
