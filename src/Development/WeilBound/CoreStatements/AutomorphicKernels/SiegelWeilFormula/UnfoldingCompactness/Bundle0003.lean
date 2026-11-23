module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.IncMTranspose

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.EvIRealAdKs
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem at_realAd_ks {F : Type} [Field F] [NumberField F] (t : ℝ) : At (evI F) (realAd F t) := by
  intro u hu
  have hu1 : u.1 = 0 := (RingEquiv.map_eq_zero_iff _).mp hu
  obtain ⟨a, b⟩ := u
  simp only at hu1
  subst hu1
  show ((0 : Ainf F) * _, b * 0) = ((0 : Ainf F), (0 : Af F))
  simp

theorem evI_realAd_ks {F : Type} [Field F] [NumberField F] (t : ℝ) :
    evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t)) = _
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

theorem psi_moves_pf {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (x : F) (hx : x ≠ 0) :
    ∃ l : AF F, ψ (-(l * algebraMap F (AF F) x)) ≠ 1 := by
  set c : ℝ := (Module.finrank ℚ F : ℝ) with hc
  have hcpos : 0 < c := by
    rw [hc]; exact_mod_cast Module.finrank_pos
  set t : ℝ := 1 / (2 * c) with ht
  refine ⟨-(realAd F t) * algebraMap F (AF F) x⁻¹, ?_⟩
  have hl : -(-(realAd F t) * algebraMap F (AF F) x⁻¹ * algebraMap F (AF F) x) = realAd F t := by
    rw [neg_mul, neg_mul, neg_neg, mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, mul_one]
  rw [hl, hψ.2.2 _ (at_realAd_ks t), evI_realAd_ks, Algebra.trace_algebraMap, mixedEmbedding.finrank]
  have : ((Module.finrank ℚ F • t : ℝ) : ℂ) = 1 / 2 := by
    rw [nsmul_eq_mul, ← hc, ht]; push_cast; field_simp
    exact div_self (by exact_mod_cast hcpos.ne')
  rw [this]
  have h2 : -(2 * (Real.pi : ℂ) * Complex.I) * (1 / 2) = -(Real.pi * Complex.I) := by ring
  rw [h2, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

end PositivityTheory.SiegelWeilFormula.kunf

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.FrameInvPf
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.kunf

theorem jw_sq_ks {R : Type} [CommRing R] (n : ℕ) (e : R) : jw n e * jw n e = e • 1 := by
  rw [jw, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
  simp

private theorem map_jw_eq_self_of_involution {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : R)
    (hse : s e = e) : (jw n e).map s = jw n e := by
  unfold jw
  rw [Matrix.fromBlocks_map]
  congr 1
  · ext i j; simp
  · ext i j; simp [Matrix.one_apply]
  · ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, Matrix.smul_apply, h, hse]
  · ext i j; simp

theorem frame_inv_pf {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ x, s (s x) = x) {n : ℕ} (e : R) (he : e * e = 1)
    (hse : s e = e) (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hM : Mᵀ * jw n e * M.map s = jw n e) :
    M * Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ = 1 ∧
    Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ * M = 1 := by
  set N := Matrix.fromBlocks (M.toBlocks₂₂.map s)ᵀ (e • (M.toBlocks₁₂.map s)ᵀ) (e • (M.toBlocks₂₁.map s)ᵀ)
      (M.toBlocks₁₁.map s)ᵀ with hN
  have hss : (M.map s).map s = M := by ext i j; simp [hs]
  have hM' : (M.map s)ᵀ * jw n e * M = jw n e := by
    have := congrArg (fun X => X.map s) hM
    simp only [Matrix.map_mul, Matrix.transpose_map, map_jw_eq_self_of_involution s hs e hse, hss] at this
    simpa [Matrix.transpose_map] using this
  have hJ : jw n e * jw n e = e • 1 := jw_sq_ks n e
  have hK : N = e • (jw n e * (M.map s)ᵀ * jw n e) := by
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks (M.map s)]
    simp only [jw, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, hN]
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, smul_smul, he]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;> simp
  have h1 : N * M = 1 := by
    rw [hK, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (M.map s)ᵀ, hM', hJ,
      smul_smul, he, one_smul]
  exact ⟨mul_eq_one_comm.mp h1, h1⟩

end PositivityTheory.SiegelWeilFormula.kunf

end
end

