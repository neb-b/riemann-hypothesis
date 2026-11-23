module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Decomp
section
open Matrix
open scoped ComplexOrder

namespace PI.UD

lemma herm_decomp {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
  refine ⟨(hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ), ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  · rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.2
  · have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
    have e : (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ) =
        fun i => ((hA.eigenvalues i : ℝ) : ℂ) := by
      funext i; rfl
    rw [e] at h
    exact h

lemma det_ne_zero_of_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ} (hU : Uᴴ * U = 1) :
    Uᴴ.det ≠ 0 := by
  have h := congrArg det hU
  rw [det_mul, det_one] at h
  exact left_ne_zero_of_mul_eq_one h

private theorem exists_diagonal_unitary_gram_of_posDef {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) :
    ∃ (s : Fin n → ℂ) (V : Matrix (Fin n) (Fin n) ℂ), (∀ i, s i ≠ 0) ∧ Vᴴ * V = 1 ∧
      V * Vᴴ = 1 ∧ G = (diagonal s * Vᴴ)ᴴ * (diagonal s * Vᴴ) := by
  obtain ⟨V, h1, h2, hV⟩ := herm_decomp hG.1
  refine ⟨fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ), V, ?_, h1, h2, ?_⟩
  · intro i
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hG.eigenvalues_pos i)).ne'
  · have hd : (diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ *
        diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)) =
        diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ)) := by
      rw [diagonal_conjTranspose, diagonal_mul_diagonal]
      refine congrArg diagonal (funext fun i => ?_)
      change star (↑(Real.sqrt (hG.1.eigenvalues i)) : ℂ) *
        ↑(Real.sqrt (hG.1.eigenvalues i)) = ↑(hG.1.eigenvalues i)
      simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Real.mul_self_sqrt (hG.eigenvalues_pos i).le]
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    calc G = V * diagonal (fun i => ((hG.1.eigenvalues i : ℝ) : ℂ)) * Vᴴ := hV
      _ = V * ((diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ)))ᴴ *
          diagonal (fun i => ((Real.sqrt (hG.1.eigenvalues i) : ℝ) : ℂ))) * Vᴴ := by rw [hd]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem gramStep : GramStep := by
  intro n G hG
  obtain ⟨s, V, hs, hV1, -, hGe⟩ := exists_diagonal_unitary_gram_of_posDef hG
  refine ⟨diagonal s * Vᴴ, hGe.symm, ?_⟩
  rw [det_mul, det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i)
    (det_ne_zero_of_unitary hV1)

theorem svdStep : SVDStep := by
  intro n g hg
  have hinj : Function.Injective g.mulVec :=
    mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hg))
  have hP : (gᴴ * g).PosDef := PosDef.conjTranspose_mul_self g hinj
  obtain ⟨s, V, hs, hV1, hV2, hG⟩ := exists_diagonal_unitary_gram_of_posDef hP
  set C := diagonal s * Vᴴ with hC
  have hCdet : IsUnit C.det := by
    refine isUnit_iff_ne_zero.2 ?_
    rw [hC, det_mul, det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hs i)
      (det_ne_zero_of_unitary hV1)
  have hCH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact hCdet.star
  refine ⟨g * C⁻¹, Vᴴ, s, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc (Cᴴ)⁻¹ * gᴴ * (g * C⁻¹) = (Cᴴ)⁻¹ * (gᴴ * g) * C⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (Cᴴ)⁻¹ * (Cᴴ * C) * C⁻¹ := by rw [hG]
      _ = ((Cᴴ)⁻¹ * Cᴴ) * (C * C⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hCH, mul_nonsing_inv _ hCdet, Matrix.one_mul]
  · rw [conjTranspose_conjTranspose]
    exact hV2
  · rw [Matrix.mul_assoc (g * C⁻¹) (diagonal s) Vᴴ, ← hC, nonsing_inv_mul_cancel_right C g hCdet]

end PI.UD
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.EvalBindTorusSubst
section
open Matrix MvPolynomial
open scoped ComplexOrder

namespace PI.UD

theorem circle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  refine Set.Infinite.of_image Complex.re
    ((Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).mono ?_)
  intro x hx
  have h1 : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  refine ⟨⟨x, Real.sqrt (1 - x ^ 2)⟩, ?_, rfl⟩
  show ‖(⟨x, Real.sqrt (1 - x ^ 2)⟩ : ℂ)‖ = 1
  rw [Complex.norm_def, Complex.normSq_mk, Real.mul_self_sqrt h1]
  simp [sq]

theorem eq_zero_of_torus {σ : Type*} (R : MvPolynomial σ ℂ)
    (h : ∀ t : σ → ℂ, (∀ i, ‖t i‖ = 1) → eval t R = 0) : R = 0 :=
  MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => circle_infinite)
    fun t ht => by simpa using h t fun i => ht i (Set.mem_univ i)

noncomputable def torusSubst {ι : Type} {n : ℕ} (w v : ι → Matrix (Fin n) (Fin n) ℂ) :
    ι × Fin n × Fin n → MvPolynomial (ι × Fin n) ℂ :=
  fun x => ∑ k, C (w x.1 x.2.1 k) * X (x.1, k) * C (v x.1 k x.2.2)

theorem eval_bind_torusSubst {ι : Type} {n : ℕ} (w v : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (t : ι × Fin n → ℂ) :
    eval t (bind₁ (torusSubst w v) P) =
      eval (fun x : ι × Fin n × Fin n =>
        (w x.1 * diagonal (fun k => t (x.1, k)) * v x.1) x.2.1 x.2.2) P := by
  refine (eval₂Hom_bind₁ (RingHom.id ℂ) t (torusSubst w v) P).trans
    (congrArg (fun f => eval f P) (funext fun x => ?_))
  rw [Matrix.mul_apply]
  simp [torusSubst, Matrix.mul_diagonal]

noncomputable def leftSubst {ι : Type} {n : ℕ} (A : ι → Matrix (Fin n) (Fin n) ℂ) :
    ι × Fin n × Fin n → MvPolynomial (ι × Fin n × Fin n) ℂ :=
  fun x => ∑ k, C (A x.1 x.2.1 k) * X (x.1, k, x.2.2)

theorem eval_bind_leftSubst {ι : Type} {n : ℕ} (A : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (u : ι → Matrix (Fin n) (Fin n) ℂ) :
    eval (fun x : ι × Fin n × Fin n => u x.1 x.2.1 x.2.2) (bind₁ (leftSubst A) P) =
      eval (fun x : ι × Fin n × Fin n => (A x.1 * u x.1) x.2.1 x.2.2) P := by
  refine (eval₂Hom_bind₁ (RingHom.id ℂ) _ (leftSubst A) P).trans
    (congrArg (fun f => eval f P) (funext fun x => ?_))
  simp [leftSubst, Matrix.mul_apply]

theorem unitary_of_torus {n : ℕ} (w v : Matrix (Fin n) (Fin n) ℂ) (hw : wᴴ * w = 1)
    (hv : vᴴ * v = 1) (t : Fin n → ℂ) (ht : ∀ k, ‖t k‖ = 1) :
    (w * diagonal t * v)ᴴ * (w * diagonal t * v) = 1 := by
  have hd : (diagonal t)ᴴ * diagonal t = 1 := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    rw [Pi.star_apply, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ht k]
    norm_num
  simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc wᴴ, hw, Matrix.one_mul, ← Matrix.mul_assoc (diagonal t)ᴴ, hd,
    Matrix.one_mul, hv]

end PI.UD
end

