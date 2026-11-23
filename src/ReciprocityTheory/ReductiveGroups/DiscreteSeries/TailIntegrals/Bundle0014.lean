module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0012
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.DetEqMulMinorOfColZero

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ProdIicCastLE
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

variable {k r : ℕ}

theorem pe_eq (a : Fin (r + 1)) :
    (WithLp.toLp 2 (phiV' k r a) : EE k r) = HE k r (WithLp.toLp 2 (phiV k r a)) := by
  rw [HE_apply, WithLp.ofLp_toLp]; rfl

theorem pe_orth (hk : 1 ≤ k) : Orthonormal ℂ (fun a => (WithLp.toLp 2 (phiV' k r a) : EE k r)) := by
  have h := qe_orth (k := k) (r := r) hk
  rw [orthonormal_iff_ite] at h ⊢
  intro a b; simp only [pe_eq, HE_adj, HE_HE]; exact h a b

theorem pe_iso (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    inner ℂ (WithLp.toLp 2 (phiV' k r a) : EE k r) (HE k r (WithLp.toLp 2 (phiV' k r b))) = 0 := by
  rw [pe_eq, pe_eq, HE_HE, HE_adj, HE_apply, WithLp.ofLp_toLp, toLp_phiV a]
  by_cases ha : a.val < r
  · rw [if_pos ha, inner_bvec, hpk_mulVec, phiV_apply]
    simp only [sigI_val, sgnI]
    split_ifs <;> first | rfl | (exfalso; omega) | simp
  · rw [if_neg ha, inner_smul_left, inner_add_left, inner_bvec, inner_bvec, hpk_mulVec, hpk_mulVec,
      phiV_apply, phiV_apply]
    simp only [sigI_val, sgnI, starRingEnd_apply]
    split_ifs <;> first | rfl | (exfalso; omega) | ring | simp

theorem phiV'_linInd' (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) :=
  (pe_orth hk).linearIndependent.map' (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap
    (LinearEquiv.ker _)

theorem phiV'_iso' (hk : 1 ≤ k) (a b : Fin (r + 1)) : herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := by
  rw [herm_eq]; exact pe_iso hk b a

theorem sum_castLE {M : Type*} [AddCommMonoid M] {l : ℕ} (h : l + 1 ≤ r + 1) (f : Fin (r + 1) → M)
    (hf : ∀ b : Fin (r + 1), l < b.val → f b = 0) :
    ∑ b, f b = ∑ b : Fin (l + 1), f (Fin.castLE h b) := by
  rw [show (∑ b : Fin (l + 1), f (Fin.castLE h b)) = ∑ b ∈ Finset.univ.map (Fin.castLEEmb h), f b by rw [Finset.sum_map]; rfl]
  refine (Finset.sum_subset (Finset.subset_univ _) fun b _ hb => hf b ?_).symm
  by_contra hcon
  exact hb (Finset.mem_map.2 ⟨⟨b.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem prod_Iic_castLE (l : Fin (r + 1)) (g : Fin (r + 1) → ℝ) :
    ∏ j ∈ Finset.Iic l, g j = ∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j) := by
  rw [show (∏ j : Fin (l.val + 1), g (Fin.castLE (by omega) j)) =
      ∏ j ∈ Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)), g j by
    rw [Finset.prod_map]; rfl]
  congr 1
  ext j
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hj; exact ⟨⟨j.val, by rw [Fin.le_def] at hj; omega⟩, Fin.ext rfl⟩
  · rintro ⟨b, rfl⟩; rw [Fin.le_def]; simp; omega

theorem iw_core (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (hk : 1 ≤ k)
    (hY : LinearIndependent ℂ Y) (hiso : ∀ a b, herm (Hpk k r) (Y a) (Y b) = 0) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ j, τ j j ≠ 0) ∧ (∀ a, Y a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l Y := by
  obtain ⟨u, τ, hu, hτ, hd, hwe, hspan⟩ := gs_fac (fun a => (WithLp.toLp 2 (Y a) : EE k r)) (linInd_toLp Y hY)
  have hwi : ∀ a b, inner ℂ (WithLp.toLp 2 (Y a) : EE k r) (HE k r (WithLp.toLp 2 (Y b))) = 0 :=
    fun a b => by rw [← herm_eq]; exact hiso b a
  have hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0 := by
    intro a b
    obtain ⟨ca, hca⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan a)
    obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hca, ← hcb, map_sum, sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right, hwi, mul_zero, mul_zero]
  obtain ⟨κ, hκK, hκ⟩ := exists_Kmat hk _ u (pe_orth hk) hu (fun a b => pe_iso hk a b) hui
  have hκ' : ∀ b, u b = WithLp.toLp 2 (κ *ᵥ phiV' k r b) := fun b => (hκ b).symm
  refine ⟨κ, hκK, τ, hτ, hd, fun a => ?_, fun l => ?_⟩
  · have h1 : (WithLp.toLp 2 (Y a) : EE k r) = ∑ b, τ b a • (WithLp.toLp 2 (κ *ᵥ phiV' k r b) : EE k r) := by
      rw [hwe a]; simp only [hκ']
    have h2 := congrArg (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h2
    simpa using h2
  · rw [ga_eq]
    have hle : l.val + 1 ≤ r + 1 := by omega
    have hsub : ∀ a : Fin (l.val + 1), (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r) =
        ∑ b : Fin (l.val + 1), (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)) b a • u (Fin.castLE hle b) := by
      intro a
      rw [hwe (Fin.castLE hle a)]
      refine sum_castLE hle _ fun b hb => ?_
      have hlt : Fin.castLE hle a < b := by
        rw [Fin.lt_def, Fin.val_castLE]; have := a.isLt; omega
      rw [show τ b (Fin.castLE hle a) = 0 from hτ hlt, zero_smul]
    have hτl : (τ.submatrix (Fin.castLE hle) (Fin.castLE hle)).BlockTriangular id :=
      fun i j hij => hτ (show Fin.castLE hle j < Fin.castLE hle i from hij)
    have hdet := det_gram_of (fun a : Fin (l.val + 1) => (WithLp.toLp 2 (Y (Fin.castLE hle a)) : EE k r))
      (fun b => u (Fin.castLE hle b)) (τ.submatrix (Fin.castLE hle) (Fin.castLE hle))
      (hu.comp _ (Fin.castLE_injective hle)) hτl hsub
    rw [hdet, Complex.ofReal_re, prod_Iic_castLE]
    rfl

end ReciprocityTheory.ChartRestriction.DS.Xi.GS

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem phiV'_linInd (k r : ℕ) (hk : 1 ≤ k) : LinearIndependent ℂ (phiV' k r) := GS.phiV'_linInd' hk

theorem phiV'_iso (k r : ℕ) (hk : 1 ≤ k) (a b : Fin (r + 1)) :
    herm (Hpk k r) (phiV' k r a) (phiV' k r b) = 0 := GS.phiV'_iso' hk a b

theorem iwB : IW := fun k r Y hk hY hiso => by
  obtain ⟨κ, hκ, τ, h1, -, h3, h4⟩ := GS.iw_core Y hk hY hiso
  exact ⟨κ, hκ, τ, h1, h3, h4⟩

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.RankOneLeviComm
section
noncomputable section

set_option linter.unusedSimpArgs false

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section grp
variable (k r' : ℕ)

theorem mat_ext_lev {A B : Mat k (1 + r')} (h0 : A *ᵥ e0 k r' = B *ᵥ e0 k r')
    (h1 : A *ᵥ es0 k r' = B *ᵥ es0 k r') (h2 : ∀ v, A *ᵥ liftVec k 1 r' v = B *ᵥ liftVec k 1 r' v) : A = B := by
  have key : ∀ q : Fin (2 * (1 + r') + k + 1), A *ᵥ Pi.single q 1 = B *ᵥ Pi.single q 1 := by
    intro q
    by_cases hq0 : q.val = 0
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = e0 k r' := by
        have hq : q = eI k (1 + r') (a0 r') := Fin.ext (by simp [eI, a0, hq0])
        rw [hq]
        rfl
      rw [he, h0]
    by_cases hql : q.val = 2 * (1 + r') + k
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) = es0 k r' := by
        have hq : q = esI k (1 + r') (a0 r') := Fin.ext (by simp [esI, a0, hql])
        rw [hq]
        rfl
      rw [he, h1]
    · have he : (Pi.single q (1 : ℂ) : Fin (2 * (1 + r') + k + 1) → ℂ) =
          liftVec k 1 r' (Pi.single ⟨q.val - 1, by omega⟩ 1) := by
        funext p
        simp only [liftVec, Pi.single_apply, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega)
      rw [he, h2]
  ext p q
  have h := congrFun (key q) p
  simpa [Matrix.mulVec_single_one, Matrix.transpose_apply] using h

theorem lev_mul (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift]

theorem lev_one : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext_lev
  · simp only [levi_fixes_base_vector, Matrix.one_mulVec]
  · simp only [levi_fixes_last_basis, Matrix.one_mulVec]
  · intro v
    simp only [lev_lift, Matrix.one_mulVec]

theorem lev_conjT (g : Mat k r') : (ιLev k 1 r' g)ᴴ = ιLev k 1 r' gᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, ιLev]
  split_ifs <;> (try subst_vars) <;> simp_all [Matrix.conjTranspose_apply]

theorem lev_mem {g : Mat k r'} (hg : g ∈ GV k r') : ιLev k 1 r' g ∈ GV k (1 + r') := by
  have hg' : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r')
  rw [lev_conjT]
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, Hpk_mulVec_e0, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, hermMatrix_last_basis, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, Hpk_lift]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem rankOne_levi_comm (c : ℂ) (g : Mat k r') : w0 k r' c * ιLev k 1 r' g = ιLev k 1 r' g * w0 k r' c := by
  apply mat_ext_lev
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_base_vector, long_weyl_sends_base_to_dual, Matrix.mulVec_smul, levi_fixes_last_basis]
  · simp only [← Matrix.mulVec_mulVec, levi_fixes_last_basis, rankOneMatrix_last_basis, Matrix.mulVec_smul, levi_fixes_base_vector]
  · intro v
    simp only [← Matrix.mulVec_mulVec, lev_lift, rankOneMatrix_lift]

theorem lev_K {κ : Mat k r'} (hκ : κ ∈ Kset k r') : ιLev k 1 r' κ ∈ Kset k (1 + r') := by
  refine ⟨lev_mem k r' hκ.1, ?_⟩
  rw [lev_conjT, ← lev_mul, hκ.2, lev_one]

end grp

section gn
variable {n : ℕ}

theorem normSq_sum_eq_trace (Y : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (Y i j) : ℝ) : ℂ) = (Yᴴ * Y).trace := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

theorem gN_unitary (k r : ℕ) {κ : Mat k r} (hκ : κᴴ * κ = 1) (X : Mat k r) : gN (κ * X) = gN X := by
  unfold gN
  congr 1
  have h1 := normSq_sum_eq_trace (κ * X)
  have h2 := normSq_sum_eq_trace X
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul] at h1
  exact_mod_cast h1.trans h2.symm

theorem gN_cont (k r : ℕ) : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => Complex.continuous_normSq.comp (continuous_id.matrix_elem i j))

end gn

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiIntH
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.XI

namespace XI

private theorem lintegral_prod_le_lintegral_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α × β → ℝ≥0∞) :
    ∫⁻ p, f p ∂(μ.prod ν) ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  exact lintegral_prod_le f

private theorem side {k r : ℕ} (s : Fin (r + 1) → ℝ) (hs : ∀ l, 0 ≤ s l) (z : Fin (2 * r + k + 1) → ℂ)
    (μW μN : Measure (Mt k r)) (hW : IsHaarOn (UWset k r z) μW)
    (hconj : ∀ h₀ ∈ UWset k r z, μN.map (conjM h₀) = μN) (hcomp : IsCompact (UWset k r z))
    (hcl : IsClosedSubgroup (UWset k r z)) (hI : IInt μN z s (1 / 2) < ∞) :
    (∫⁻ p : Mt k r × Mt k r, (xiN k r s (Matrix.of p.2 * Matrix.of p.1) : ℝ≥0∞) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂(μW.prod μN)) < ∞ := by
  obtain ⟨K₀, hK₀⟩ := hcomp.exists_bound_of_continuousOn (cont_gN (k := k) (r := r)).continuousOn
  obtain ⟨K, hK1, hKb⟩ : ∃ K : ℝ, 1 ≤ K ∧ ∀ g ∈ UWset k r z, gN g ≤ K := by
    refine ⟨max K₀ 1, le_max_right _ _, fun g hg => ?_⟩
    have h1 := hK₀ g hg
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  obtain ⟨C, hC0, hCeq⟩ : ∃ C : ℝ, 0 ≤ C ∧ C = ∏ l : Fin (r + 1), (K ^ (l.val + 1)) ^ s l :=
    ⟨_, Finset.prod_nonneg fun l _ => Real.rpow_nonneg (pow_nonneg (by linarith) _) _, rfl⟩
  have hlam : Continuous (fun m : Mt k r => lam k r z (Matrix.of m)) := by
    unfold lam ell
    refine Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_))
    split_ifs with ha
    · first
        | (simp only [Matrix.of_apply]; fun_prop)
        | fun_prop
        | exact (continuous_apply _).comp (continuous_apply _)
    · first
        | (simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]; fun_prop)
        | (simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply]; fun_prop)
        | exact (continuous_apply _).comp (Continuous.matrix_mulVec continuous_id continuous_const)
  have hWfin : μW Set.univ < ∞ := by
    have h2 : μW Set.univ ≤ μW (UWset k r z) + μW (UWset k r z)ᶜ := by
      first
        | exact measure_univ_le_add_compl _
        | (rw [← Set.union_compl_self (UWset k r z)]; exact measure_union_le _ _)
    rw [hW.conc, add_zero] at h2
    exact lt_of_le_of_lt h2 (hW.finite_compact _ hcomp)
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by
    rw [ae_iff]
    first
      | exact hW.conc
      | exact measure_mono_null (fun a ha => ha) hW.conc
  have hinner : ∀ h ∈ UWset k r z, (∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN) ≤
      ENNReal.ofReal C * IInt μN z s (1 / 2) := by
    intro h hh
    have hu : IsUnit h.det := hcl.unit h hh
    have hinv : h⁻¹ ∈ UWset k r z := hcl.inv_mem h hh
    have hu' : IsUnit h⁻¹.det := hcl.unit _ hinv
    have hii : h⁻¹⁻¹ = h := Matrix.nonsing_inv_nonsing_inv h hu
    have hcm : Measurable (conjM (k := k) (r := r) h⁻¹) := by
      apply Continuous.measurable
      first
        | exact continuous_pi fun i => continuous_pi fun j => by
            simp only [conjM, Matrix.mul_apply, Matrix.of_apply]; fun_prop
        | (unfold conjM; fun_prop)
        | (unfold conjM; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    have hG : Measurable (fun m : Mt k r => ENNReal.ofReal (xiR k r s (Matrix.of m)) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) := by
      have hm1 : Measurable (fun m : Mt k r => ENNReal.ofReal (xiR k r s (Matrix.of m))) :=
        (meas_xi k r s).coe_nnreal_ennreal
      have hm2 : Measurable (fun m : Mt k r =>
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) :=
        ENNReal.measurable_ofReal.comp ((continuous_const.add hlam.abs).measurable.pow_const _)
      exact hm1.mul hm2
    have hpt : ∀ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) := by
      intro n
      have e : Matrix.of (conjM h⁻¹ n) = h⁻¹ * Matrix.of n * h := by
        show h⁻¹ * Matrix.of n * h⁻¹⁻¹ = _
        rw [hii]
      have hl : lam k r z (h⁻¹ * Matrix.of n * h) = lam k r z (Matrix.of n) := by
        have := lam_conj hinv hu' (Matrix.of n)
        rwa [hii] at this
      have hxi : xiR k r s (Matrix.of n * h) ≤ C * xiR k r s (h⁻¹ * Matrix.of n * h) := by
        have := xi_bd s hs h hu K hK1 (hKb h hh) (hKb h⁻¹ hinv) (h⁻¹ * Matrix.of n * h)
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
          Matrix.one_mul] at this
        rw [hCeq]
        exact this
      have hw : (1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ)) ≤
          (1 + |lam k r z (Matrix.of n)|) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (lam k r z (Matrix.of n))])
          (by norm_num)
      rw [e, hl, ← mul_assoc, ← ENNReal.ofReal_mul hC0]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hxi) (ENNReal.ofReal_le_ofReal hw)
    calc (∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN)
        ≤ ∫⁻ n : Mt k r, ENNReal.ofReal C * (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) ∂μN :=
          lintegral_mono hpt
      _ = ENNReal.ofReal C * ∫⁻ n : Mt k r, (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) ∂μN :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C * ∫⁻ m : Mt k r, (ENNReal.ofReal (xiR k r s (Matrix.of m)) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) ∂(μN.map (conjM h⁻¹)) := by
          rw [lintegral_map hG hcm]
      _ = ENNReal.ofReal C * IInt μN z s (1 / 2) := by
          rw [hconj h⁻¹ hinv]
          try rfl
  calc (∫⁻ p : Mt k r × Mt k r, (xiN k r s (Matrix.of p.2 * Matrix.of p.1) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂(μW.prod μN))
      ≤ ∫⁻ x : Mt k r, ∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * Matrix.of x) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN ∂μW :=
        lintegral_prod_le_lintegral_lintegral μW μN _
    _ ≤ ∫⁻ _x : Mt k r, ENNReal.ofReal C * IInt μN z s (1 / 2) ∂μW :=
        lintegral_mono_ae (hae.mono fun x hx => hinner (Matrix.of x) hx)
    _ = ENNReal.ofReal C * IInt μN z s (1 / 2) * μW Set.univ := lintegral_const _
    _ < ∞ := by
        first
          | exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI) hWfin
          | exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_ne_top hI.ne) hWfin.ne

end XI

theorem xiIntH (hB2 : InductiveHeisenbergInputs) : XiIntStep := by
  unfold InductiveHeisenbergInputs at hB2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hCI, hCW, -, -, -, -, -, -, -, hClW, -, -, -, -, -⟩ := hB2
  intro k r Wp Wq _ _ _ _ _ _ D s hs hI hI'
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hs0 : ∀ l, 0 ≤ s l := by
    intro l
    have h1 := (hs l).2
    have h2 : (1 : ℝ) ≤ s0 k r l := by
      unfold s0
      split_ifs <;> linarith
    linarith
  unfold XiInt
  refine ⟨XI.meas_xi k r s, ?_, ?_⟩
  · exact XI.side s hs0 D.z D.μW D.μN D.haarW
      (fun h₀ hh => hCI k r Wp Wq D h₀ (Set.mem_union_left _ hh))
      (hCW k r D.z D.z_mem D.T_pos) (hClW k r D.z) hI
  · exact XI.side s hs0 D.z' D.μW' D.μN D.haarW'
      (fun h₀ hh => hCI k r Wp Wq D h₀ (Set.mem_union_right _ hh))
      (hCW k r D.z' D.z'_mem D.T'_pos) (hClW k r D.z') hI'

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

