module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConvAlg

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.StabPairsOf
section
open Matrix

noncomputable section

namespace PI.StabPairsW

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

theorem stabPairs_of (h1 : MapsStep) (h2 : PairFormula) (h3 : ConverseStep) (h4 : CompDet) :
    Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree := by
  intro k r z z' γ hs hp
  have hinj : ∀ ρ1 ∈ Rst k r z z' γ, ∀ ρ2 ∈ Rst k r z z' γ,
      pairMap k r z z' γ ρ1 = pairMap k r z z' γ ρ2 → ρ1 = ρ2 := by
    intro ρ1 h1' ρ2 h2' heq
    calc ρ1 = rhoOf k r z z' γ (pairMap k r z z' γ ρ1).1 (pairMap k r z z' γ ρ1).2 :=
          h2 k r z z' γ hs hp ρ1 h1'
      _ = rhoOf k r z z' γ (pairMap k r z z' γ ρ2).1 (pairMap k r z z' γ ρ2).2 := by rw [heq]
      _ = ρ2 := (h2 k r z z' γ hs hp ρ2 h2').symm
  refine ⟨⟨fun ρ hρ => h1 k r z z' γ hs hp ρ hρ, fun ρ1 h1' ρ2 h2' heq => hinj ρ1 h1' ρ2 h2' heq,
    fun p hp' => ⟨rhoOf k r z z' γ p.1 p.2, (h3 k r z z' γ hs hp p hp').1,
      (h3 k r z z' γ hs hp p hp').2⟩⟩, ?_, ?_⟩
  · intro ρ1 h1' ρ2 h2' heq
    apply hinj ρ1 h1' ρ2 h2'
    exact ((h4 k r z z' γ hs hp _ (h1 k r z z' γ hs hp ρ1 h1') _
      (h1 k r z z' γ hs hp ρ2 h2')).1 heq)
  · intro ρ1 h1' ρ2 h2' heq
    apply hinj ρ1 h1' ρ2 h2'
    exact ((h4 k r z z' γ hs hp _ (h1 k r z z' γ hs hp ρ1 h1') _
      (h1 k r z z' γ hs hp ρ2 h2')).2 heq)

end PI.StabPairsW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.UtSubOneLast
section
open Matrix

noncomputable section

namespace PI.StabPairs.Conv

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2 PI.StabPairsW

theorem ut_last {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) (j : Fin (r + 1)) :
    u (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  split_ifs with h
  · subst h; exact hu.2 _
  · exact hu.1 _ _ (lt_of_le_of_ne (Fin.le_last j) h)

theorem ut_det {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1)) : u.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hu.1 i j hij)]
  simp [hu.2]

theorem ut_sub_one_last {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (x : Fin (r + 1) → ℂ) : ((u - 1) *ᵥ x) (Fin.last r) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.sub_apply, ut_last hu, Matrix.one_apply]
  by_cases h : j = Fin.last r
  · subst h; simp
  · simp [h, Ne.symm h]

theorem ut_conj_fix {r : ℕ} {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (v : Fin (r + 1) → ℂ) (hv : ∀ a : Fin (r + 1), a.val < r → v a = 0) : uᴴ *ᵥ v = v := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu]
    by_cases ha : a = Fin.last r
    · subst ha; simp
    · simp only [ha, if_false, star_zero, zero_mul]
      exact (hv a (lt_of_le_of_ne (Nat.lt_succ_iff.mp a.isLt) (fun e => ha (Fin.ext e)))).symm
  · intro b _ hb
    rw [hv b (lt_of_le_of_ne (Nat.lt_succ_iff.mp b.isLt) (fun e => hb (Fin.ext e))), mul_zero]
  · simp

theorem cancel_of_pair {r : ℕ} {u u' Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hu : u ∈ UTset (r + 1))
    (hZ : IsUnit Z.det) (hp : uᴴ * Z * u' = Z) (c : Fin (r + 1) → ℂ)
    (hc : ∀ a : Fin (r + 1), a.val < r → (Z *ᵥ c) a = 0) : (u' - 1) *ᵥ c = 0 := by
  have hA : IsUnit (uᴴ * Z).det := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, ut_det hu, star_one, one_mul]; exact hZ
  have h0 : (uᴴ * Z) *ᵥ ((u' - 1) *ᵥ c) = 0 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, hp, Matrix.sub_mulVec,
      ← Matrix.mulVec_mulVec, ut_conj_fix hu _ hc, sub_self]
  calc (u' - 1) *ᵥ c = ((uᴴ * Z)⁻¹ * (uᴴ * Z)) *ᵥ ((u' - 1) *ᵥ c) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem ut_adiag (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ}
    (hu : u ∈ UTset (r + 1)) : uᴴ * Adiag k r z * u = Adiag k r z := by
  ext a b
  rw [Adiag, Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [ut_last hu a, ut_last hu b, Matrix.diagonal_apply]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r
    · subst ha; subst hb; simp
    · subst ha; simp [hb, Ne.symm hb]
    · subst hb; simp [ha]
    · simp [ha, hb]
  · intro c _ hc; simp [hc]
  · simp

end PI.StabPairs.Conv
end
end

