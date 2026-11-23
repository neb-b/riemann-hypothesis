module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.OneParameterSubgroups.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.InvMulSelfOfMemIndefiniteUnitary
section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

private theorem Jm_mul_selfDiscreteSeriesExistence (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

private theorem Jm_conjTransposeDiscreteSeriesExistence (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  change star (if ε a = true then (1 : ℂ) else -1) = _
  split_ifs <;> simp

private theorem Jm_mul_Jm_mul_eq (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (Jm ε * Y) = Y := by
  rw [← Matrix.mul_assoc, Jm_mul_selfDiscreteSeriesExistence, Matrix.one_mul]

theorem inv_eq_signature_conjTranspose_conj {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ = Jm ε * gᴴ * Jm ε := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  apply Matrix.inv_eq_left_inv
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_selfDiscreteSeriesExistence]

theorem inv_mul_self_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g⁻¹ * g = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  rw [inv_eq_signature_conjTranspose_conj hg, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h, Jm_mul_selfDiscreteSeriesExistence]

theorem mul_inv_self_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g (Matrix.isUnit_det_of_left_inverse (inv_mul_self_of_mem_indefiniteUnitary hg))

theorem isUnit_of_mem_indefiniteUnitary {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) : IsUnit g :=
  ⟨⟨g, g⁻¹, mul_inv_self_of_mem_indefiniteUnitary hg, inv_mul_self_of_mem_indefiniteUnitary hg⟩, rfl⟩

theorem inG_conj_unitary {ε : Fin n → Bool} {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hX : inG ε X) : inG ε (g * X * g⁻¹) := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_selfDiscreteSeriesExistence ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTransposeDiscreteSeriesExistence ε
  have hX0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have hX' : Jm ε * Xᴴ + X * Jm ε = 0 := by
    have e : Jm ε * Xᴴ + X * Jm ε = Jm ε * (Xᴴ * Jm ε + Jm ε * X) * Jm ε := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one,
        Jm_mul_Jm_mul_eq]
    rw [e, hX0, Matrix.mul_zero, Matrix.zero_mul]
  have key : (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) =
      Jm ε * g * (Jm ε * Xᴴ + X * Jm ε) * gᴴ * Jm ε := by
    rw [inv_eq_signature_conjTranspose_conj hg]
    simp only [Matrix.conjTranspose_mul, hJh, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
  show (g * X * g⁻¹)ᴴ * Jm ε + Jm ε * (g * X * g⁻¹) = 0
  rw [key, hX', Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul]

private theorem Jm_conjTranspose_Jm_eq_neg_of_inG {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * Xᴴ * Jm ε = -X := by
  have h0 : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left h0
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, Jm_mul_Jm_mul_eq]

theorem conj_involution_complex_comb {ε : Fin n → Bool} {A B : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) (hB : inG ε B) :
    stJ ε (A + Complex.I • B) = -A + Complex.I • B := by
  unfold stJ
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Jm_conjTranspose_Jm_eq_neg_of_inG hA, Jm_conjTranspose_Jm_eq_neg_of_inG hB]
  simp [Complex.star_def, Complex.conj_I]

theorem actM_add_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X Y : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) :
    actM E (X + c • Y) = actM E X + c • actM E Y := by
  simp only [actM, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_smul, mul_smul,
    Finset.sum_add_distrib, Finset.smul_sum]

theorem actM_neg {M : Type*} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM E (-X) = -actM E X := by
  simp only [actM, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem isometry_inner_eq {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {h : Matrix (Fin n) (Fin n) ℂ}
    (hn : ∀ v : H, ‖σ h v‖ = ‖v‖) (a b : H) : ⟪σ h a, σ h b⟫_ℂ = ⟪a, b⟫_ℂ := by
  exact LinearIsometry.inner_map_map
    ({ toLinearMap := (σ h : H →ₗ[ℂ] H), norm_map' := hn } : H →ₗᵢ[ℂ] H) a b

theorem derived_action_skew_adjoint {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smD ε σ) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inG ε Y) {u u' : H}
    (hu : HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • Y)) u) u' 0) :
    ⟪w, u'⟫_ℂ = -⟪((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H), u⟫_ℂ := by
  have hd := (isDerivedOn_smE hσ).deriv Y hY ⟨w, hw⟩
  have h3 : HasDerivAt
      (fun t : ℝ => ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) w, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ)
      (⟪σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) w, u'⟫_ℂ +
        ⟪((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H), σ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) u⟫_ℂ) 0 :=
    hd.inner ℂ hu
  have h4 : (fun t : ℝ =>
      ⟪σ (NormedSpace.exp ((t : ℂ) • Y)) w, σ (NormedSpace.exp ((t : ℂ) • Y)) u⟫_ℂ) =
      fun _ => ⟪w, u⟫_ℂ :=
    funext fun t => isometry_inner_eq (hσ.2.1 _ (exp_smul_mem_UJset hY t)) w u
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0 : ℝ) ⟪w, u⟫_ℂ)
  have h0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  rw [h0, hσ.1.1] at h5
  simp only [ContinuousLinearMap.one_apply] at h5
  exact eq_neg_of_add_eq_zero_left h5

theorem hasDerivAt_conj_exp_action {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ∈ smD ε σ) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g w))
      (σ g ((actM (smE ε σ) X ⟨w, hw⟩ : smD ε σ) : H)) 0 := by
  have hgX : inG ε (g * X * g⁻¹) := inG_conj_unitary hg hX
  have hd := (isDerivedOn_smE hσ).deriv X hX ⟨w, hw⟩
  have hfun : (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹))) (σ g w)) =
      fun t : ℝ => σ g (σ (NormedSpace.exp ((t : ℂ) • X)) w) := by
    funext t
    have hm : NormedSpace.exp ((t : ℂ) • (g * X * g⁻¹)) * g = g * NormedSpace.exp ((t : ℂ) • X) := by
      rw [show (t : ℂ) • (g * X * g⁻¹) = g * ((t : ℂ) • X) * g⁻¹ by
          rw [Matrix.mul_smul, Matrix.smul_mul],
        Matrix.exp_conj g _ (isUnit_of_mem_indefiniteUnitary hg), Matrix.mul_assoc, inv_mul_self_of_mem_indefiniteUnitary hg, Matrix.mul_one]
    have h1 := hσ.1.2 _ (exp_smul_mem_UJset hgX t) g hg
    have h2 := hσ.1.2 g hg _ (exp_smul_mem_UJset hX t)
    rw [hm] at h1
    exact congrArg (fun L : H →L[ℂ] H => L w) (h1.symm.trans h2)
  rw [hfun]
  exact ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd

end Rep

private theorem inG_of_Jm_conj_eq_neg {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ}
    (h : Jm ε * Yᴴ * Jm ε = -Y) : inG ε Y := by
  show Yᴴ * Jm ε + Jm ε * Y = 0
  have e : Yᴴ * Jm ε = Jm ε * (Jm ε * Yᴴ * Jm ε) := by
    rw [Matrix.mul_assoc (Jm ε) Yᴴ, Jm_mul_Jm_mul_eq]
  rw [e, h, Matrix.mul_neg, neg_add_cancel]

private theorem exists_inG_add_I_smul_inG (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, inG ε A ∧ inG ε B ∧ X = A + Complex.I • B := by
  have hJ : Jm ε * Jm ε = 1 := Jm_mul_selfDiscreteSeriesExistence ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTransposeDiscreteSeriesExistence ε
  refine ⟨(1 / 2 : ℂ) • (X - Jm ε * Xᴴ * Jm ε), (1 / (2 * Complex.I)) • (X + Jm ε * Xᴴ * Jm ε),
    ?_, ?_, ?_⟩
  · apply inG_of_Jm_conj_eq_neg
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Jm_mul_Jm_mul_eq]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp, ← smul_neg, neg_sub]
  · apply inG_of_Jm_conj_eq_neg
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJh,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc, hJ, Matrix.mul_one, Jm_mul_Jm_mul_eq]
    have hc : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp [Complex.star_def, Complex.conj_I]
    rw [hc, neg_smul, add_comm (Jm ε * (Xᴴ * Jm ε)) X]
  · have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
      rw [mul_one_div, mul_comm 2 Complex.I, ← div_div, div_self Complex.I_ne_zero]
    have h2 : X - Jm ε * Xᴴ * Jm ε + (X + Jm ε * Xᴴ * Jm ε) = (2 : ℂ) • X := by
      rw [two_smul]; abel
    rw [smul_smul, hI, ← smul_add, h2, smul_smul]
    norm_num

theorem b3a : MatrixCoeffConjugationMove := by
  intro n ε H _ _ σ w hσ hw g hg X
  have hφ : ∀ Y, phiW ε σ w Y = ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) := fun Y => by
    simp only [phiW, dif_pos hw]
  have hlin : ∀ (Y Z : Matrix (Fin n) (Fin n) ℂ) (c : ℂ),
      ((actM (smE ε σ) (Y + c • Z) ⟨w, hw⟩ : smD ε σ) : H) =
        ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) +
          c • ((actM (smE ε σ) Z ⟨w, hw⟩ : smD ε σ) : H) := by
    intro Y Z c
    rw [actM_add_smul]
    simp
  have hneg : ∀ Y, ((actM (smE ε σ) (-Y) ⟨w, hw⟩ : smD ε σ) : H) =
      -((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H) := by
    intro Y
    rw [actM_neg]
    simp
  have key : ∀ Y, inG ε Y → ⟪w, σ g ((actM (smE ε σ) Y ⟨w, hw⟩ : smD ε σ) : H)⟫_ℂ =
      -⟪((actM (smE ε σ) (g * Y * g⁻¹) ⟨w, hw⟩ : smD ε σ) : H), σ g w⟫_ℂ :=
    fun Y hY => derived_action_skew_adjoint hσ hw (inG_conj_unitary hg hY) (hasDerivAt_conj_exp_action hσ hw hg hY)
  obtain ⟨A, B, hA, hB, rfl⟩ := exists_inG_add_I_smul_inG ε X
  have hconj : g * (A + Complex.I • B) * g⁻¹ = g * A * g⁻¹ + Complex.I • (g * B * g⁻¹) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hconj, conj_involution_complex_comb (inG_conj_unitary hg hA) (inG_conj_unitary hg hB), hφ, hφ, hlin, hlin, hneg,
    map_add, map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
    inner_neg_left, key A hA, key B hB]
  simp only [Complex.conj_I]
  ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.MatrixCoeffBoundsImplyBound
section
noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem trace_dMat (d : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℂ) :
    trace (dMat d * X) = ∑ a, (d a : ℂ) * X a a := by
  simp [Matrix.trace, dMat, Matrix.diagonal_mul]

theorem stJ_apply (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    stJ ε X a b = (if ε a then 1 else -1) * star (X b a) * (if ε b then 1 else -1) := by
  simp only [stJ, Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply]

theorem norm_stJ_apply (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ‖stJ ε X a b‖ = ‖X b a‖ := by
  rw [stJ_apply]; split_ifs <;> simp

theorem l1_le_card_mul_norm (X : Matrix (Fin n) (Fin n) ℂ) : l1 X ≤ (n : ℝ) ^ 2 * ‖X‖ := by
  calc l1 X ≤ ∑ _a : Fin n, ∑ _b : Fin n, ‖X‖ :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => Matrix.norm_entry_le_entrywise_sup_norm X
    _ = _ := by simp; ring

theorem norm_mul_le_n (X Y : Matrix (Fin n) (Fin n) ℂ) : ‖X * Y‖ ≤ n * (‖X‖ * ‖Y‖) := by
  rw [Matrix.norm_le_iff (by positivity)]
  intro a b
  rw [Matrix.mul_apply]
  calc _ ≤ ∑ c, ‖X a c * Y c b‖ := norm_sum_le _ _
    _ ≤ ∑ _c : Fin n, ‖X‖ * ‖Y‖ := sum_le_sum fun c _ => by
        rw [norm_mul]
        exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm X)
          (Matrix.norm_entry_le_entrywise_sup_norm Y) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

theorem act_bound {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M) (w : M) (d : Fin n → ℝ) (t C : ℝ)
    (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a b, X a b ≠ 0 → ‖E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w‖ ≤ C) :
    ‖actM E X w - ((t : ℂ) * trace (dMat d * X)) • w‖ ≤ C * l1 X := by
  have e : actM E X w - ((t : ℂ) * trace (dMat d * X)) • w =
      ∑ a, ∑ b, X a b • (E a b w - (if a = b then (((t * d a : ℝ)) : ℂ) else 0) • w) := by
    simp only [actM, LinearMap.sum_apply, LinearMap.smul_apply, smul_sub, sum_sub_distrib,
      trace_dMat, mul_sum, sum_smul]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [sum_eq_single a (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_smul, smul_zero])
      (by simp), if_pos rfl, smul_smul]
    congr 1; push_cast; ring
  rw [e, l1, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun b _ => ?_)
  by_cases h0 : X a b = 0
  · simp [h0]
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (h a b h0) (norm_nonneg _)

theorem matrixCoeffBounds_imply_bound : MatrixCoeffBoundsImplyBound := by
  classical
  intro h2 h3a h3b h3c hinf n ε d Λ₀ R
  obtain ⟨C, hC, hB⟩ := h2 n ε d Λ₀
  obtain ⟨K, hK, hT⟩ := h3c n |R|
  set C' : ℝ := C * (n : ℝ) ^ 2 * (1 + |R|) with hC'
  set Cd : ℝ := ∑ a, |d a| with hCd
  set ρb : ℝ := 2 * (n * (|R| * |R|)) with hρb
  have hC'0 : 0 ≤ C' := by positivity
  have hCd0 : 0 ≤ Cd := sum_nonneg fun a _ => abs_nonneg _
  refine ⟨(3 * C' + C' * 1 * ρb + Cd * K + C' * 1 * K) * Real.exp (Cd * ρb), ?_⟩
  intro t ht H _ _ σ lam w ⟨hσ, hw, hw1, hhw, hcas⟩ hlam Y hY hYR
  obtain ⟨bp, bl, ball⟩ := hB t ht (smD ε σ) (smE ε σ) lam ⟨w, hw⟩
    ⟨(isDerivedOn_smE hσ).glRep, hinf n ε H σ hσ, hw1, hhw, hcas⟩ hlam
  let φ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] H :=
    { toFun := fun X => ((actM (smE ε σ) X ⟨w, hw⟩ : smD ε σ) : H)
      map_add' := fun X X' => by simp [actM, add_smul, sum_add_distrib]
      map_smul' := fun c X => by simp [actM, smul_sum, smul_smul] }
  have hφ : ∀ X, phiW ε σ w X = φ X := fun X => by rw [phiW, dite_eq_left hw]; rfl
  let dl : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => trace (dMat d * X)
      map_add' := fun X X' => by rw [Matrix.mul_add, trace_add]
      map_smul' := fun c X => by simp }
  have hsub : ∀ X (c : ℂ), ‖φ X - c • w‖ =
      ‖actM (smE ε σ) X ⟨w, hw⟩ - c • (⟨w, hw⟩ : smD ε σ)‖ := fun X c => rfl
  have hYn : ‖Y‖ ≤ |R| := by
    rw [Matrix.norm_le_iff (abs_nonneg R)]
    intro a b
    refine (le_abs_self _).trans (sq_le_sq.mp ?_)
    refine le_trans ?_ hYR
    calc ‖Y a b‖ ^ 2 ≤ ∑ j, ‖Y a j‖ ^ 2 :=
          single_le_sum (f := fun j => ‖Y a j‖ ^ 2) (fun j _ => by positivity) (mem_univ b)
      _ ≤ S7.hs Y := single_le_sum (f := fun i => ∑ j, ‖Y i j‖ ^ 2)
          (fun i _ => by positivity) (mem_univ a)
  let Yl : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a b => if InLL ε d a b then Y a b else 0
  let Yp : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun a b => if InNP ε d a b then Y a b else 0
  set Ym := partNM ε d Y with hYm
  have hpart : ∀ (p : Fin n → Fin n → Prop) [∀ a b, Decidable (p a b)],
      ‖(Matrix.of fun a b => if p a b then Y a b else 0 : Matrix (Fin n) (Fin n) ℂ)‖ ≤ |R| := by
    intro p _
    rw [Matrix.norm_le_iff (abs_nonneg R)]
    intro a b
    rw [Matrix.of_apply]
    split_ifs
    · exact (Matrix.norm_entry_le_entrywise_sup_norm Y).trans hYn
    · simp
  have hYmn : ‖Ym‖ ≤ |R| := hpart _
  have hsum : Yl + Yp + Ym = Y := by
    ext a b
    simp only [Yl, Yp, hYm, partNM, Matrix.add_apply, Matrix.of_apply, InLL, InNP, InNM]
    rcases lt_trichotomy a b with h | h | h
    · by_cases he : ε a = ε b <;> by_cases hd : d a = d b <;> simp [h, he, hd, lt_asymm h, eq_comm]
    · subst h; simp
    · by_cases he : ε a = ε b <;> by_cases hd : d a = d b <;> simp [h, he, hd, lt_asymm h, eq_comm]
  have hne : ∀ a b, InNP ε d a b → a ≠ b := by
    rintro a b (h | h) rfl <;> exact lt_irrefl _ h.1
  have hbd : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖X‖ ≤ |R| → C * l1 X ≤ C' := fun X hX => by
    have := (l1_le_card_mul_norm X).trans (mul_le_mul_of_nonneg_left hX (by positivity))
    calc C * l1 X ≤ C * ((n : ℝ) ^ 2 * |R|) := mul_le_mul_of_nonneg_left this hC
      _ ≤ C' := by rw [hC']; nlinarith [mul_nonneg hC (sq_nonneg (n : ℝ))]
  have hNP : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖X‖ ≤ |R| → (∀ a b, X a b ≠ 0 → InNP ε d a b) →
      ‖φ X‖ ≤ C' := by
    intro X hX hs
    have h0 : trace (dMat d * X) = 0 := by
      rw [trace_dMat]
      refine sum_eq_zero fun a _ => ?_
      by_contra h
      exact hne a a (hs a a (right_ne_zero_of_mul h)) rfl
    have := act_bound (smE ε σ) ⟨w, hw⟩ d t C X fun a b h => by
      rw [if_neg (hne a b (hs a b h)), zero_smul, sub_zero]; exact bp a b (hs a b h)
    rw [h0, mul_zero, zero_smul, sub_zero] at this
    exact this.trans (hbd X hX)
  have hstn : ∀ X : Matrix (Fin n) (Fin n) ℂ, ‖stJ ε X‖ ≤ 1 * ‖X‖ := fun X => by
    rw [one_mul, Matrix.norm_le_iff (norm_nonneg _)]
    intro a b
    rw [norm_stJ_apply]; exact Matrix.norm_entry_le_entrywise_sup_norm X
  have hdn : ∀ X, ‖dl X‖ ≤ Cd * ‖X‖ := fun X => by
    show ‖trace (dMat d * X)‖ ≤ _
    rw [trace_dMat, hCd, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (Matrix.norm_entry_le_entrywise_sup_norm X) (abs_nonneg _)
  have hdl : dl Yl = trace (dMat d * Y) := by
    show trace (dMat d * Yl) = _
    rw [trace_dMat, trace_dMat]
    exact sum_congr rfl fun a _ => by simp [Yl, InLL]
  have hdiag : ∀ a, (Y a a).re = 0 := fun a => by
    have := congrArg Complex.re (congrFun (congrFun hY a) a)
    simp only [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, conjTranspose_apply,
      Matrix.zero_apply] at this
    split_ifs at this <;> simp at this <;> linarith
  set Z : Matrix (Fin n) (Fin n) ℂ := (((Real.sqrt t)⁻¹ : ℝ) : ℂ) • Y with hZ
  have hZG : inG ε Z := by
    have hY' : Yᴴ * Jm ε + Jm ε * Y = 0 := hY
    show Zᴴ * Jm ε + Jm ε * Z = 0
    rw [hZ, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, hY', smul_zero]
  have key := N.one_param w hw1 φ dl (stJ ε) hC'0 hCd0 zero_le_one hK ht hdn hstn
    (fun X X' => by simp [stJ, Matrix.mul_add, Matrix.add_mul])
    (fun X => by
      show trace (dMat d * stJ ε X) = starRingEnd ℂ (trace (dMat d * X))
      set_option synthInstance.maxHeartbeats 100000 in
        rw [trace_dMat, trace_dMat, map_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [stJ_apply]; split_ifs <;> simp)
    Yl Yp Ym (Y * Ym - Ym * Y)
    (fun τ => NormedSpace.exp ((τ : ℂ) • Y) * Ym * NormedSpace.exp (-((τ : ℂ) • Y)))
    (by rw [hdl, trace_dMat, Complex.re_sum]; exact sum_eq_zero fun a _ => by simp [hdiag])
    (fun τ hτ => hT Y Ym hYn hYmn τ hτ.1 hτ.2)
    (hNP Yp (hpart _) fun a b h => by
      by_contra h'; exact h (by simp [Yp, h']))
    (hNP _ ((hstn Ym).trans (by simpa using hYmn)) fun a b h => by
      by_contra h'
      apply h
      rw [← norm_eq_zero, norm_stJ_apply, norm_eq_zero]
      simp [hYm, partNM, InNM, h'])
    (by
      rw [hsub]
      refine (act_bound (smE ε σ) ⟨w, hw⟩ d t C Yl fun a b h => bl a b ?_).trans (hbd Yl (hpart _))
      by_contra h'; exact h (by simp [Yl, h']))
    (fun X => by
      rw [hsub]
      refine (ball X).trans ?_
      have h1 := l1_le_card_mul_norm X
      have h0 : 0 ≤ C * Real.sqrt t := by positivity
      calc C * Real.sqrt t * l1 X ≤ C * Real.sqrt t * ((n : ℝ) ^ 2 * ‖X‖) :=
            mul_le_mul_of_nonneg_left h1 h0
        _ ≤ C' * Real.sqrt t * ‖X‖ := by
            rw [hC']
            have : 0 ≤ C * Real.sqrt t * ((n : ℝ) ^ 2 * ‖X‖) * |R| := by positivity
            nlinarith)
    (fun s => σ (NormedSpace.exp ((s : ℂ) • Z)))
    (fun s v => hσ.2.1 _ (exp_smul_mem_UJset hZG s) v)
    (by simp [hσ.1.1])
    (fun s _ => by rw [hsum, ← hφ]; exact h3b n ε H σ w hσ hw Z hZG s)
    (fun s _ => by
      have := h3a n ε H σ w hσ hw _ (exp_smul_mem_UJset hZG s) Ym
      rw [hφ, hφ, ← Matrix.exp_neg] at this
      have e : (s : ℂ) • Z = ((s / Real.sqrt t : ℝ) : ℂ) • Y := by
        rw [hZ, smul_smul]; push_cast; rw [div_eq_mul_inv]
      rw [this, e])
  have hρ : ‖Y * Ym - Ym * Y‖ ≤ ρb := by
    have a1 := (norm_mul_le_n Y Ym).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hYn hYmn (norm_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg n))
    have a2 := (norm_mul_le_n Ym Y).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hYmn hYn (norm_nonneg _) (abs_nonneg _)) (Nat.cast_nonneg n))
    have := norm_sub_le (Y * Ym) (Ym * Y)
    rw [hρb]; linarith
  have hq : -(qForm ε d Y) = dl (Y * Ym - Ym * Y) := by rw [qForm, neg_neg]; rfl
  rw [hq, ← hdl]
  simp only [Complex.ofReal_one, one_smul] at key
  refine key.trans ?_
  rw [div_mul_eq_mul_div]
  have hd2 : ‖dl (Y * Ym - Ym * Y)‖ ≤ Cd * ρb :=
    (hdn _).trans (mul_le_mul_of_nonneg_left hρ hCd0)
  have hρ0 : 0 ≤ ρb := by positivity
  gcongr

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.SmInfUnitary
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem smInfUnitary : SmInfUnitaryStatement :=
  fun _ _ _ _ _ _ hσ => isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end

