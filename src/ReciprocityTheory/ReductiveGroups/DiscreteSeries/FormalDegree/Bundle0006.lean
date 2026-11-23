module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PSpecB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacobianLeExp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.EigenvectorUnitaryMulStar
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def wS {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) : ℝ :=
  ‖(((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
    (S.1.orderEmbOfFin S.2)).det‖ ^ 2

def yS {ε : Fin n → Bool} (z : PCoord ε → ℂ) (S : Finset (Fin n)) : ℝ := ∑ s ∈ S, pev z s

theorem minor_weight_cast {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) :
    ((wS z hi S : ℝ) : ℂ) =
      (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
        (S.1.orderEmbOfFin S.2)).det *
      star (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi)
        (S.1.orderEmbOfFin S.2)).det := by
  rw [wS, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']

theorem pmat_eq_eigenvectorUnitary_conj_diagonal_pev {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    pmat z = ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      diagonal (fun s => ((pev z s : ℝ) : ℂ)) *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
  have hu : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 :=
    Unitary.mul_star_self_of_mem (pmat_isHermitian z).eigenvectorUnitary.2
  calc pmat z = pmat z * (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ) := by rw [hu, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, pmat_mul_evU]

theorem pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 ∧
    ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hU := (pmat_isHermitian z).eigenvectorUnitary.2
  exact ⟨Unitary.mul_star_self_of_mem hU, Unitary.star_mul_self_of_mem hU⟩

theorem matrix_map_id (M : Matrix (Fin n) (Fin n) ℂ) : M.map (RingHom.id ℂ) = M := by
  ext a b
  rfl

theorem leading_minor_sum_weights {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (d : Fin n → ℂ) :
    Del (((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal d *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ) i =
      ∑ S, ((wS z hi S : ℝ) : ℂ) * ∏ s ∈ S.1, d s := by
  unfold Del
  rw [dite_eq_left hi]
  have h := leading_minor_conj_diagonal (RingHom.id ℂ) hi ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) d
  rw [matrix_map_id, matrix_map_id] at h
  rw [h]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [minor_weight_cast z hi S]
  rfl

theorem lemma3a {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (t : ℝ) :
    Del (NormedSpace.exp ((t : ℂ) • pmat z)) i =
      ∑ S, ((wS z hi S : ℝ) : ℂ) * Complex.exp ((t * yS z S.1 : ℝ) : ℂ) := by
  have hu := (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1
  have hUu : IsUnit ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := isUnit_iff_exists.mpr ⟨_, hu, (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).2⟩
  have hsm : (t : ℂ) • pmat z = ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => ((t * pev z s : ℝ) : ℂ)) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)⁻¹ := by
    rw [Matrix.inv_eq_right_inv hu]
    conv_lhs => rw [pmat_eq_eigenvectorUnitary_conj_diagonal_pev z]
    have hd : diagonal (fun s => ((t * pev z s : ℝ) : ℂ)) =
        (t : ℂ) • diagonal (fun s => ((pev z s : ℝ) : ℂ)) := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hd, mul_smul_comm, smul_mul_assoc]
  have hexp : NormedSpace.exp ((t : ℂ) • pmat z) =
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => Complex.exp ((t * pev z s : ℝ) : ℂ)) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    rw [hsm, Matrix.exp_conj _ _ hUu, Matrix.exp_diagonal, Matrix.inv_eq_right_inv hu]
    congr 1
    congr 1
    congr 1
    rw [Pi.exp_def]
    funext s
    simp only [Complex.exp_eq_exp_ℂ]
  rw [hexp, leading_minor_sum_weights z hi]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← Complex.exp_sum]
  congr 2
  simp [yS, Finset.mul_sum]

theorem lemma3b {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) : ∑ S, wS z hi S = 1 := by
  have h := leading_minor_sum_weights z hi (fun _ => (1 : ℂ))
  simp only [Matrix.diagonal_one, (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1, Finset.prod_const_one, mul_one] at h
  have h1 : Del (1 : Matrix (Fin n) (Fin n) ℂ) i = 1 := by
    unfold Del
    rw [dite_eq_left hi, Matrix.submatrix_one _ (Fin.castLE_injective hi), Matrix.det_one]
  exact_mod_cast h.symm.trans h1

open Polynomial in
theorem sum_weights_coeff_eq_det {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (μ : Fin n → ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal μ *
      ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = M) (k : ℕ) :
    ∑ S, ((wS z hi S : ℝ) : ℂ) * (∏ s ∈ S.1, (1 + X * C (μ s))).coeff k =
      (det (1 + (X : ℂ[X]) • (M.submatrix (Fin.castLE hi) (Fin.castLE hi)).map C)).coeff k := by
  have hL := leading_minor_conj_diagonal (Polynomial.C : ℂ →+* ℂ[X]) hi ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) (fun s => 1 + X * C (μ s))
  rw [conj_polynomial_diagonal _ (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).1 μ, hM] at hL
  have hsub : (1 + (X : ℂ[X]) • M.map C).submatrix (Fin.castLE hi) (Fin.castLE hi) =
      1 + (X : ℂ[X]) • (M.submatrix (Fin.castLE hi) (Fin.castLE hi)).map C := by
    ext a b
    simp [Matrix.one_apply, (Fin.castLE_injective hi).eq_iff]
  rw [hsub] at hL
  rw [hL, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [← minor_weight_cast z hi S, Polynomial.coeff_C_mul]

theorem trace_leading_submatrix_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    trace ((pmat z).submatrix (Fin.castLE hi) (Fin.castLE hi)) = 0 := by
  rw [trace_leading_submatrix]
  simp [pmat_diag_zero]


open Polynomial in
theorem lemma3c {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ S, wS z hi S * yS z S.1 = 0 := by
  have hP := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ)) (pmat z) (pmat_eq_eigenvectorUnitary_conj_diagonal_pev z).symm 1
  beta_reduce at hP
  rw [Matrix.coeff_det_one_add_X_smul_one, trace_leading_submatrix_pmat z hi] at hP
  have hc : ∀ S : {S : Finset (Fin n) // S.card = i},
      (∏ s ∈ S.1, (1 + Polynomial.X * Polynomial.C ((pev z s : ℝ) : ℂ))).coeff 1 =
        ((yS z S.1 : ℝ) : ℂ) := by
    intro S
    rw [(coeff_prod_one_add_low S.1 _).2.1, yS]
    push_cast
    rfl
  simp only [hc] at hP
  exact_mod_cast hP


open Polynomial in
theorem lemma3d {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ S, wS z hi S * yS z S.1 ^ 2 = Vi (pmat z) i := by
  have hP2 := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ)) (pmat z) (pmat_eq_eigenvectorUnitary_conj_diagonal_pev z).symm 2
  have hsq : ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * diagonal (fun s => ((pev z s : ℝ) : ℂ) ^ 2) * ((pmat_isHermitian z).eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ = pmat z * pmat z := by
    rw [← sq_conj_diagonal _ _ (pmat_eigenvectorUnitary_mul_conjTranspose_and_conj_mul z).2, ← pmat_eq_eigenvectorUnitary_conj_diagonal_pev z]
  have hP1 := sum_weights_coeff_eq_det z hi (fun s => ((pev z s : ℝ) : ℂ) ^ 2) (pmat z * pmat z) hsq 1
  beta_reduce at hP1 hP2
  rw [Matrix.coeff_det_one_add_X_smul_one] at hP1
  have h2 := coeff_two_det_hermitian _ ((pmat_isHermitian z).submatrix (Fin.castLE hi))
  rw [trace_leading_submatrix_pmat z hi] at h2
  have hS : ∀ S : {S : Finset (Fin n) // S.card = i}, ((yS z S.1 : ℝ) : ℂ) ^ 2 =
      2 * (∏ s ∈ S.1, (1 + Polynomial.X * Polynomial.C ((pev z s : ℝ) : ℂ))).coeff 2 +
        (∏ s ∈ S.1, (1 + Polynomial.X * Polynomial.C (((pev z s : ℝ) : ℂ) ^ 2))).coeff 1 := by
    intro S
    obtain ⟨-, -, h2'⟩ := coeff_prod_one_add_low S.1 (fun s => ((pev z s : ℝ) : ℂ))
    obtain ⟨-, h1'', -⟩ := coeff_prod_one_add_low S.1 (fun s => ((pev z s : ℝ) : ℂ) ^ 2)
    rw [h2', h1'', yS]
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  rw [variance_eq_trace_diff hi (pmat z) (pmat_isHermitian z)]
  simp only [hS, mul_add, Finset.sum_add_distrib, mul_left_comm _ (2 : ℂ), ← Finset.mul_sum]
  rw [hP2, hP1, h2]
  ring

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntMuCD
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def intMuCD_pM (ε : Fin n → Bool) : KG ε × (PCoord ε → ℂ) → (Fin n → Fin n → ℂ) := fun kz => polarM kz

def intMuCD_P (ε : Fin n → Bool) : Measure (KG ε × (PCoord ε → ℂ)) :=
  (dk ε).prod (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z))

theorem intMuCD_muPolarMat_eq (ε : Fin n → Bool) :
    muPolarMat ε = Measure.map (intMuCD_pM ε) (intMuCD_P ε) := rfl

theorem lintegral_comap_embedding {α : Type*} [MeasurableSpace α] {e : α → (Fin n → Fin n → ℂ)}
    (he : MeasurableEmbedding e) (μ : Measure (Fin n → Fin n → ℂ)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.range e)
    (F : (Fin n → Fin n → ℂ) → ENNReal) :
    ∫⁻ g, F (e g) ∂(Measure.comap e μ) = ∫⁻ x, F x ∂μ := by
  have h1 := he.lintegral_map (μ := Measure.comap e μ) F
  rw [he.map_comap, Measure.restrict_eq_self_of_ae_mem hμ] at h1
  exact h1.symm

theorem intMuCD_measurable_pM (ε : Fin n → Bool) : Measurable (intMuCD_pM ε) := by
  exact Continuous.measurable (f := intMuCD_pM ε) (polarM_continuous ε)

theorem intMuCD_polar_int (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ x, F x ∂(muPolarMat ε) =
      ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hpm := intMuCD_measurable_pM ε
  have hJ : Measurable (fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) :=
    ENNReal.measurable_ofReal.comp (jac_continuous ε).measurable
  rw [intMuCD_muPolarMat_eq, lintegral_map hF hpm, intMuCD_P]
  refine (lintegral_prod (F ∘ intMuCD_pM ε) (hF.comp hpm).aemeasurable).trans ?_
  refine lintegral_congr (fun k => ?_)
  refine (lintegral_withDensity_eq_lintegral_mul _ hJ (hF.comp (hpm.comp measurable_prodMk_left))).trans ?_
  refine lintegral_congr (fun z => ?_)
  exact mul_comm _ _

theorem intMuCD_ae_range (ε : Fin n → Bool) (S : Set (Fin n → Fin n → ℂ)) (hS : MeasurableSet S)
    (h : ∀ kz : KG ε × (PCoord ε → ℂ), intMuCD_pM ε kz ∈ S) : ∀ᵐ x ∂(muPolarMat ε), x ∈ S := by
  rw [intMuCD_muPolarMat_eq]
  exact (ae_map_iff (p := fun x => x ∈ S) (intMuCD_measurable_pM ε).aemeasurable hS).2 (ae_of_all _ h)

def intMuCD_eM (ε : Fin n → Bool) : UJ ε → (Fin n → Fin n → ℂ) := fun g => toM g

def intMuCD_eU (ε : Fin n → Bool) : Formalism.REAL.UJ ε → (Fin n → Fin n → ℂ) := fun g => Formalism.MainNotions.S.umat g

private theorem exists_UJ_toM_eq_of_inUJ {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ∃ u : UJ ε, toM u = g := by
  change g ∈ Set.range (fun u : UJ ε => toM u)
  rw [range_toM]
  exact hg

theorem lintegral_muPolar (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ g, F (toM g) ∂(muPolar ε) =
      ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hemb : MeasurableEmbedding (intMuCD_eM ε) := (isClosedEmbedding_toM ε).measurableEmbedding
  have hae : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range (intMuCD_eM ε) :=
    intMuCD_ae_range ε _ hemb.measurableSet_range fun kz => exists_UJ_toM_eq_of_inUJ (polarM_inUJ kz)
  calc ∫⁻ g, F (toM g) ∂(muPolar ε)
        = ∫⁻ g, F (intMuCD_eM ε g) ∂(Measure.comap (intMuCD_eM ε) (muPolarMat ε)) := rfl
    _ = ∫⁻ x, F x ∂(muPolarMat ε) := lintegral_comap_embedding hemb _ hae F
    _ = _ := intMuCD_polar_int ε F hF

theorem lintegral_muCD (ε : Fin n → Bool) (F : (Fin n → Fin n → ℂ) → ENNReal) (hF : Measurable F) :
    ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε) =
      ENNReal.ofReal (cPQ ε) * ∫⁻ k, ∫⁻ z, F (polarM (k, z)) * ENNReal.ofReal (Jac z) ∂volume ∂(dk ε) := by
  have hemb : MeasurableEmbedding (intMuCD_eU ε) := (isClosedEmbedding_toM ε).measurableEmbedding
  have hae : ∀ᵐ x ∂(muPolarMat ε), x ∈ Set.range (intMuCD_eU ε) :=
    intMuCD_ae_range ε _ hemb.measurableSet_range fun kz => exists_UJ_toM_eq_of_inUJ (polarM_inUJ kz)
  calc ∫⁻ g, F (Formalism.MainNotions.S.umat g) ∂(muCD ε)
        = ENNReal.ofReal (cPQ ε) *
            ∫⁻ g, F (intMuCD_eU ε g) ∂(Measure.comap (intMuCD_eU ε) (muPolarMat ε)) := by
          rw [muCD, lintegral_smul_measure]
          rfl
    _ = _ := by rw [lintegral_comap_embedding hemb _ hae F, intMuCD_polar_int ε F hF]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBound
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem jac_le_exp {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    Jac z ≤ Real.exp (((n : ℝ) - 1) * Real.sqrt (2 * (q0 ε : ℝ)) * Real.sqrt (hs (pmat z))) := by
  have hpos : 0 < Jac z := lt_of_lt_of_le one_pos (jac_ge_one z)
  have h := log_jac_le_rho z
  rw [rhoP, ← mul_assoc] at h
  calc Jac z = Real.exp (Real.log (Jac z)) := (Real.exp_log hpos).symm
    _ ≤ _ := Real.exp_le_exp.mpr h

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarAct
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def plog (h : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (Matrix.isHermitian_conjTranspose_mul_self h).cfc Real.log

def actR {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : PCoord ε → ℂ :=
  fun ab => plog (NormedSpace.exp (pmat z) * g) ab.1.1 ab.1.2

theorem pact_cfc_log_exp (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian)
    (h : (NormedSpace.exp X).IsHermitian) : h.cfc Real.log = X := by
  have hSA : IsSelfAdjoint X := Matrix.isHermitian_iff_isSelfAdjoint.mp hX
  obtain ⟨W, hWdef⟩ : ∃ W, W = (hX.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have hW : star W * W = 1 := by
    rw [hWdef]
    exact Matrix.mem_unitaryGroup_iff'.mp hX.eigenvectorUnitary.2
  have hWi : W⁻¹ = star W := Matrix.inv_eq_left_inv hW
  have hWu : IsUnit W := (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hW)
  have hexp : NormedSpace.exp X = hX.cfc Real.exp := by
    have hd : NormedSpace.exp (RCLike.ofReal ∘ hX.eigenvalues : Fin n → ℂ) =
        (RCLike.ofReal ∘ Real.exp ∘ hX.eigenvalues : Fin n → ℂ) := by
      funext i
      simp [Complex.ofReal_exp, ← Complex.exp_eq_exp_ℂ]
    conv_lhs => rw [hX.spectral_theorem]
    rw [Matrix.IsHermitian.cfc]
    simp only [Unitary.conjStarAlgAut_apply, Unitary.coe_star]
    rw [← hWdef, ← hWi, Matrix.exp_conj _ _ hWu, Matrix.exp_diagonal, hd]
  rw [← Matrix.IsHermitian.cfc_eq, hexp, ← Matrix.IsHermitian.cfc_eq,
    ← cfc_comp Real.log Real.exp X hSA
      (Real.continuousOn_log.mono (by rintro _ ⟨x, -, rfl⟩; exact (Real.exp_pos x).ne'))
      Real.continuous_exp.continuousOn]
  have hle : Real.log ∘ Real.exp = id := funext Real.log_exp
  rw [hle]
  exact cfc_id ℝ X hSA

theorem pact_cfc_congr {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A = B) (f : ℝ → ℝ) : hA.cfc f = hB.cfc f := by
  subst h
  rfl

theorem plog_unitary_mul_exp (k X : Matrix (Fin n) (Fin n) ℂ) (hk : kᴴ * k = 1) (hX : X.IsHermitian) :
    plog (k * NormedSpace.exp X) = X := by
  have hE : (NormedSpace.exp X)ᴴ = NormedSpace.exp X := by
    rw [← Matrix.exp_conjTranspose, hX.eq]
  have h2 : (k * NormedSpace.exp X)ᴴ * (k * NormedSpace.exp X) = NormedSpace.exp (X + X) := by
    rw [Matrix.exp_add_of_commute X X (Commute.refl X), Matrix.conjTranspose_mul, hE,
      Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k, hk, Matrix.one_mul]
  have hB : (NormedSpace.exp (X + X)).IsHermitian := by
    rw [← h2]
    exact Matrix.isHermitian_conjTranspose_mul_self _
  unfold plog
  rw [pact_cfc_congr (Matrix.isHermitian_conjTranspose_mul_self (k * NormedSpace.exp X)) hB h2 Real.log,
    pact_cfc_log_exp (X + X) (hX.add hX) hB, ← two_smul ℂ X, smul_smul]
  norm_num

private theorem toMK_unit_lemma {ε : Fin n → Bool} (k : KG ε) : (toMK k)ᴴ * toMK k = 1 := by
  have hk := k.2
  unfold S7.KG Kset at hk
  unfold S7.toMK
  exact Matrix.mem_unitaryGroup_iff'.mp hk.1

theorem plog_polarM {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : plog (polarM (k, z)) = pmat z :=
  plog_unitary_mul_exp (toMK k) (pmat z) (toMK_unit_lemma k) (pmat_isHermitian z)

theorem pact_pmat_coords {ε : Fin n → Bool} (w : PCoord ε → ℂ) :
    (fun ab : PCoord ε => pmat w ab.1.1 ab.1.2) = w := by
  funext ab
  obtain ⟨⟨a, b⟩, h⟩ := ab
  simp only [pmat]
  rw [dite_eq_left h]

private theorem actR_eq_lemma {ε : Fin n → Bool} {g U : Matrix (Fin n) (Fin n) ℂ} {z w : PCoord ε → ℂ}
    (hU : Uᴴ * U = 1) (h : NormedSpace.exp (pmat z) * g = U * NormedSpace.exp (pmat w)) :
    actR g z = w := by
  unfold actR
  rw [h, plog_unitary_mul_exp U (pmat w) hU (pmat_isHermitian w)]
  exact pact_pmat_coords w

theorem actR_of_eq_polarM {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} {z w : PCoord ε → ℂ} {k : KG ε}
    (h : NormedSpace.exp (pmat z) * g = polarM (k, w)) : actR g z = w := by
  unfold actR
  rw [h, plog_polarM]
  exact pact_pmat_coords w

theorem pact_inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

theorem actR_spec {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    ∃ k : KG ε, NormedSpace.exp (pmat z) * g = polarM (k, actR g z) := by
  obtain ⟨⟨k, w⟩, hkw⟩ := polarM_surj _ (pact_inUJ_mul (exp_pmat_inUJ z) hg)
  refine ⟨k, ?_⟩
  rw [actR_of_eq_polarM hkw.symm]
  exact hkw.symm

theorem actR_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : actR (g * h) z = actR h (actR g z) := by
  obtain ⟨k1, h1⟩ := actR_spec hg z
  obtain ⟨k2, h2⟩ := actR_spec hh (actR g z)
  simp only [polarM] at h1 h2
  apply actR_eq_lemma (U := toMK k1 * toMK k2)
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (toMK k1)ᴴ, toMK_unit_lemma k1,
      Matrix.one_mul, toMK_unit_lemma k2]
  · rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc (toMK k1) (NormedSpace.exp (pmat (actR g z))) h, h2,
      Matrix.mul_assoc (toMK k1) (toMK k2)]

theorem actR_one {ε : Fin n → Bool} (z : PCoord ε → ℂ) : actR (1 : Matrix (Fin n) (Fin n) ℂ) z = z := by
  apply actR_eq_lemma (U := 1)
  · simp
  · rw [Matrix.mul_one, Matrix.one_mul]

theorem pact_pmat_zero {ε : Fin n → Bool} : pmat (0 : PCoord ε → ℂ) = 0 := by
  ext a b
  simp [pmat]

private theorem toMK_unit_lemma_2 {ε : Fin n → Bool} (k : KG ε) : toMK k * (toMK k)ᴴ = 1 := by
  have hk := k.2
  unfold S7.KG Kset at hk
  unfold S7.toMK
  exact Matrix.mem_unitaryGroup_iff.mp hk.1

theorem actR_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : actR (toMK k) z = adK k⁻¹ z := by
  have hU := toMK_unit_lemma k
  have hU' : toMK k * (toMK k)ᴴ = 1 := toMK_unit_lemma_2 k
  have hinv : toMK k⁻¹ * toMK k = 1 := by
    simp [S7.toMK, S7.toM]
  have hi1 : (toMK k)⁻¹ = (toMK k)ᴴ := Matrix.inv_eq_left_inv hU
  have hi2 : (toMK k)⁻¹ = toMK k⁻¹ := Matrix.inv_eq_left_inv hinv
  have hunit : IsUnit (toMK k) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hU)
  apply actR_eq_lemma hU
  have hi3 : (toMK k)⁻¹ᴴ = toMK k := by rw [hi1, Matrix.conjTranspose_conjTranspose]
  rw [pmat_adK, ← hi2, hi3, Matrix.exp_conj' _ _ hunit, hi1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU',
    Matrix.one_mul]

theorem actR_exp_zero {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    actR (NormedSpace.exp (pmat y)) (0 : PCoord ε → ℂ) = y := by
  apply actR_eq_lemma (U := 1)
  · simp
  · rw [pact_pmat_zero, NormedSpace.exp_zero, Matrix.one_mul]

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PsiMExpPmat
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem psiM_polar {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) (k : KG ε)
    (z : PCoord ε → ℂ) :
    PsiM T μ (toMK k * NormedSpace.exp (pmat z)) = T.op k * psM T μ (NormedSpace.exp (pmat z)) := by
  have hX := pmat_inP z
  have hex : ∃ (k' : KG ε) (X' : Matrix (Fin n) (Fin n) ℂ), inP ε X' ∧
      toMK k * NormedSpace.exp (pmat z) = toMK k' * NormedSpace.exp X' := ⟨k, pmat z, hX, rfl⟩
  unfold PsiM
  rw [dite_eq_left hex]
  obtain ⟨hP, hEq⟩ := hex.choose_spec.choose_spec
  obtain ⟨h1, h2⟩ := polar_unique hX hP hEq
  rw [← h2, ← h1]

theorem psiM_exp_pmat {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    (z : PCoord ε → ℂ) : PsiM T μ (NormedSpace.exp (pmat z)) = psM T μ (NormedSpace.exp (pmat z)) := by
  have h := psiM_polar T μ (1 : KG ε) z
  have e : toMK (1 : KG ε) = 1 := rfl
  have o : T.op (1 : KG ε) = 1 := by simp [KType.op, map_one]
  rwa [e, Matrix.one_mul, o, one_mul] at h

end ReciprocityTheory.ChartRestriction.DS
end
end

