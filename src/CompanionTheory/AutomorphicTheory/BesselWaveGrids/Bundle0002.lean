module

public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.ZuckDualTOfZuckDual
public import Formalism.HermitianCurvature.StatementU
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0003
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.Bundle0001
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.PstMul

@[expose] public section

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.LettersPoly
section
noncomputable section

namespace CompanionTheory.WaveGrid.LimSh

open Formalism.FourierDecayAlt Matrix CompanionTheory.LimBd.Main

section letters

variable {k r : ℕ}

theorem one_mem_letters : (1 : B.Mat k r → ℂ) ∈ Letters k r := Submodule.subset_span (Or.inl rfl)

theorem letters_pow_succ (a : ℕ) : Letters k r ^ a ≤ Letters k r ^ (a + 1) := by
  intro x hx
  rw [pow_succ, ← mul_one x]
  exact Submodule.mul_mem_mul hx one_mem_letters

theorem letters_pow_mono {a d : ℕ} (h : a ≤ d) : Letters k r ^ a ≤ Letters k r ^ d := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (letters_pow_succ _)

theorem mul_mem_letters_pow {a d : ℕ} {x y : B.Mat k r → ℂ} (hx : x ∈ Letters k r ^ a) (hy : y ∈ Letters k r ^ d) :
    x * y ∈ Letters k r ^ (a + d) := by
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy

theorem entry_mem (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => g i j) ∈ Letters k r :=
  Submodule.subset_span (Or.inr ⟨Pi.single j 1, Pi.single i 1, Or.inl fun g _ => by simp⟩)

theorem star_entry_mem (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => star (g i j)) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨fun a => Formalism.QuantumDeterminants.Hpk k r a i, star (Formalism.QuantumDeterminants.Hpk k r j), Or.inr ?_⟩)
  intro g hg
  have hH : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hinv : g⁻¹ = Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), hg', hH]
  have e : Formalism.QuantumDeterminants.Hpk k r * (g⁻¹ * Formalism.QuantumDeterminants.Hpk k r) = gᴴ := by
    rw [hinv, Matrix.mul_assoc _ (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.Hpk k r), hH, Matrix.mul_one, ← Matrix.mul_assoc, hH,
      Matrix.one_mul]
  have e2 := congrFun (congrFun e j) i
  rw [conjTranspose_apply] at e2
  rw [star_star]
  exact e2.symm

theorem polyDeg_mem {e : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg e c) : c ∈ Letters k r ^ e := by
  classical
  obtain ⟨q, hq, hcq⟩ := hc
  let X : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) →
      B.Mat k r → ℂ := Sum.elim (fun x g => g x.1 x.2) (fun x g => star (g x.1 x.2))
  have hX : ∀ v, X v ∈ Letters k r := by
    rintro (x | x)
    · exact entry_mem x.1 x.2
    · exact star_entry_mem x.1 x.2
  have hpow : ∀ v (n : ℕ), X v ^ n ∈ Letters k r ^ n := fun v n => Submodule.pow_mem_pow _ (hX v) n
  have hprod : ∀ (m : _ →₀ ℕ) (s : Finset _), (∏ v ∈ s, X v ^ m v) ∈ Letters k r ^ (∑ v ∈ s, m v) := by
    intro m s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mul_mem_letters_pow (hpow a _) ih
  have e1 : c = ∑ m ∈ q.support, q.coeff m • ∏ v ∈ m.support, X v ^ m v := by
    funext g
    rw [hcq g, MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rcases v with x | x <;> rfl
  rw [e1]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (letters_pow_mono ?_ (hprod m m.support))
  exact (MvPolynomial.le_totalDegree hm).trans hq

end letters

end CompanionTheory.WaveGrid.LimSh
end
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.NQText
section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Finset

theorem interlaces_of_OK (P : M.Par) (hOK : P.OK) : I.Interlaces P.k P.u P.u' P.lo := by
  intro i hi
  have hg := hOK.gap i hi
  unfold M.Par.lo M.Par.hi at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := min_le_left (P.u i) (P.u' i); linarith
  · have := min_le_right (P.u i) (P.u' i); linarith
  · have := le_max_left (P.u (i + 1)) (P.u' (i + 1)); linarith
  · have := le_max_right (P.u (i + 1)) (P.u' (i + 1)); linarith

theorem den_core (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : I.Interlaces k u u' ρ) (hA : u l + 2 ≤ -Y ∧ -Y ≤ u' l - 2) :
    ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i| ∧ 1 ≤ |Y + 1 / 2 + u' i| := by
  have hu := Formalism.FourierDecayAlt.P.Interlace.antitone_on (Formalism.FourierDecayAlt.P.Interlace.u_step h)
  have hu' := Formalism.FourierDecayAlt.P.Interlace.antitone_on
    (Formalism.FourierDecayAlt.P.Interlace.u_step (Formalism.FourierDecayAlt.P.Interlace.interlaces_swap h))
  intro i hi1 hik
  rcases lt_trichotomy i l with hil | rfl | hil
  · obtain ⟨a, b, c, d⟩ := h i (mem_Icc.2 ⟨hi1, by omega⟩)
    have h1 := hu' (i + 1) l (by omega) (by omega) hlk
    exact ⟨le_abs.2 (Or.inl (by linarith)), le_abs.2 (Or.inl (by linarith))⟩
  · exact ⟨le_abs.2 (Or.inr (by linarith)), le_abs.2 (Or.inl (by linarith))⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    obtain ⟨a, b, c, d⟩ := h j (mem_Icc.2 ⟨by omega, by omega⟩)
    have h1 := hu l j hl1 (by omega) (by omega)
    exact ⟨le_abs.2 (Or.inr (by linarith)), le_abs.2 (Or.inr (by linarith))⟩

theorem den_onCut (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ) (hl1 : 1 ≤ l) (hlk : l ≤ k)
    (h : I.Interlaces k u u' ρ) (hc : I.OnCut u u' l Y) :
    ∀ i, 1 ≤ i → i ≤ k → 1 ≤ |Y + 1 / 2 + u i| ∧ 1 ≤ |Y + 1 / 2 + u' i| := by
  rcases hc with hA | hB
  · exact den_core k u u' ρ l Y hl1 hlk h hA
  · intro i hi1 hik
    exact (den_core k u' u ρ l Y hl1 hlk (Formalism.FourierDecayAlt.P.Interlace.interlaces_swap h) hB i hi1 hik).symm

theorem abs_le_of_onCut (u u' : ℕ → ℝ) (l : ℕ) (Y b : ℝ) (hc : I.OnCut u u' l Y) (hu : |u l| ≤ b)
    (hu' : |u' l| ≤ b) : |Y| ≤ b := by
  rw [abs_le] at hu hu' ⊢
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith

theorem qpoly_eq_of_pos (k : ℕ) (T T' : ℝ) (u u' : ℕ → ℝ) (Y : ℝ) (hT : 0 < T) (hT' : 0 < T')
    (hq : 0 < I.qpoly k T T' u u' Y) :
    I.qpoly k T T' u u' Y = T * T' * ∏ i ∈ Icc 1 k, (|Y + 1 / 2 + u i| * |Y + 1 / 2 + u' i|) := by
  rw [← abs_of_pos hq]
  unfold I.qpoly
  rw [abs_mul, abs_neg, abs_of_pos (mul_pos hT hT'), Finset.abs_prod]
  simp only [abs_mul]

structure LamData (P : M.Par) (lam : ℕ → ℝ) (c g b : ℝ) : Prop where
  c_pos : 0 < c
  g_ge : 1 + c ≤ g
  b_ge_three : 3 ≤ b
  b_ge_k : (P.k : ℝ) ≤ b
  b_ge_c : c + 2 ≤ b
  lam_le : ∀ s, 1 ≤ s → s ≤ P.k + 2 * P.r + 1 → |lam s| ≤ b
  gap : ∀ s, 1 ≤ s → s + 1 ≤ P.k - 1 → lam (s + 1) + g ≤ lam s
  inter : ∀ s, 1 ≤ s → s ≤ P.k - 1 →
    (lam s + 1 / 2 ≤ P.u s ∧ P.u (s + 1) ≤ lam s - 1 / 2) ∧ (lam s + 1 / 2 ≤ P.u' s ∧ P.u' (s + 1) ≤ lam s - 1 / 2)
  u_le : ∀ i, 1 ≤ i → i ≤ P.k → |P.u i| ≤ b ∧ |P.u' i| ≤ b

end CompanionTheory.WaveGrid
end

