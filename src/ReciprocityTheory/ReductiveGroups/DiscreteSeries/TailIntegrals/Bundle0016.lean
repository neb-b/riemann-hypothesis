module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0035
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.Bundle0015
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.LastBasisZero

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HeisenbergHaarFactsHold
section
namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem heisenbergHaarFacts_hold : InductiveHeisenbergInputs :=
  ⟨Formalism.FourierDecayAlt.P.stabilizer_integration_formula,
    Formalism.FourierDecayAlt.P.rank_one_coordinates_formula,
    Formalism.FourierDecayAlt.P.stabilizer_one_parameter_mem,
    Formalism.FourierDecayAlt.P.unipotent_haar_recursion,
    Formalism.FourierDecayAlt.P.unipotent_haar_base_case,
    Formalism.FourierDecayAlt.P.heisenberg_conjugation_by_levi,
    Formalism.FourierDecayAlt.P.heisenberg_levi_conjugation_measure,
    Formalism.FourierDecayAlt.P.heisenberg_inverse,
    Formalism.FourierDecayAlt.P.heisMul_statement,
    Formalism.FourierDecayAlt.P.heisenberg_mem_unipotent,
    Formalism.FourierDecayAlt.P.heisenberg_subgroup_closed,
    Formalism.FourierDecayAlt.P.heisenberg_haar_measure,
    Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting,
    Formalism.FourierDecayAlt.P.weyl_subgroup_compact,
    Formalism.FourierDecayAlt.P.norm_power_integrable_sharp,
    Formalism.FourierDecayAlt.P.matrix_norm_ge_one,
    Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar,
    Formalism.FourierDecayAlt.P.haar_measure_inversion,
    Formalism.FourierDecayAlt.P.compact_group_haar_exists,
    Formalism.FourierDecayAlt.P.unitary_group_closed,
    Formalism.FourierDecayAlt.P.unipotent_radical_closed,
    Formalism.FourierDecayAlt.P.weyl_subgroup_closed,
    Formalism.FourierDecayAlt.P.levi_haar_measure_exists,
    Formalism.FourierDecayAlt.P.weyl_haar_exists,
    Formalism.FourierDecayAlt.P.unipotent_haar_exists,
    Formalism.FourierDecayAlt.P.unitary_group_haar_exists,
    Formalism.FourierDecayAlt.P.heisenberg_action_formula⟩

end ReciprocityTheory.ChartRestriction.DS.Xi
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.MpUnitary
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace BL

section cont
variable {p m : ℕ}

theorem cont_ite {β : Type} [TopologicalSpace β] [Zero β] (c : Prop) [Decidable c] {f : Xp p m → β}
    (hf : Continuous f) : Continuous (fun x => if c then f x else 0) := by
  by_cases h : c
  · simp only [h, if_true]; exact hf
  · simp only [h, if_false]; exact continuous_const

theorem cont_Lsq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => Lsq x l) := by
  unfold Lsq
  exact continuous_const.fun_add (continuous_finsetSum _ fun j _ =>
    cont_ite _ (((continuous_apply j).comp continuous_fst).norm.pow 2))

theorem cont_rhoSq (l : Fin (p + 1)) : Continuous (fun x : Xp p m => rhoSq x l) := by
  unfold rhoSq
  refine ((cont_Lsq _).add (continuous_finsetSum _ fun i _ => ?_)).add (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).norm.pow 2)

theorem cont_bco (l : Fin (p + 1)) : Continuous (fun x : Xp p m => bco x l) := by
  unfold bco
  refine ((Complex.continuous_ofReal.comp ((continuous_finsetSum _ fun i _ => ?_).fun_neg.div_const 2)).add
    ((Complex.continuous_ofReal.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      continuous_const)).sub (continuous_finsetSum _ fun j _ => ?_)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).norm.pow 2
  · exact cont_ite _ (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_fst).star)

theorem cont_de (l : Fin (p + 1)) : Continuous (fun x : Xp p m => de x l) := by
  unfold de
  exact Real.continuous_sqrt.comp (((cont_Lsq l).mul (cont_rhoSq l)).add ((cont_bco l).norm.pow 2))

theorem cont_linF (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) : Continuous (fun x : Xp p m => linF η η' ζ x) := by
  unfold linF
  refine (continuous_finsetSum _ fun j _ => ?_).add (continuous_finsetSum _ fun i _ => ?_)
  · exact (((continuous_apply j).comp continuous_fst).mul continuous_const).add
      (((continuous_apply j).comp (continuous_fst.comp continuous_snd)).mul continuous_const)
  · exact ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd))).mul continuous_const

def GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) (x : Xp p m) : ℝ≥0∞ :=
  (∏ l, ENNReal.ofReal (de x l ^ (-s l))) * ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))

theorem meas_GI (s : Fin (p + 1) → ℝ) (δ : ℝ) (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) :
    Measurable (GI s δ η η' ζ c₀) := by
  unfold GI
  refine (Finset.measurable_prod _ fun l _ => ?_).mul ?_
  · exact ENNReal.measurable_ofReal.comp ((cont_de l).measurable.pow_const _)
  · exact ENNReal.measurable_ofReal.comp ((continuous_const.add ((continuous_const.mul
      (Complex.continuous_im.comp (cont_linF η η' ζ))).add continuous_const).abs).measurable.pow_const _)

end cont

theorem mp_unitary {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun y : Fin N → ℂ => U *ᵥ y) volume volume := by
  set f : (Fin N → ℂ) →ₗ[ℝ] (Fin N → ℂ) := (Matrix.toLin' U).restrictScalars ℝ with hf
  have hfU : (fun y : Fin N → ℂ => U *ᵥ y) = ⇑f := by funext y; simp [hf, Matrix.toLin'_apply]
  have hn : ((Complex.normSq U.det : ℝ) : ℂ) = 1 := by
    have h := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    rw [Complex.normSq_eq_conj_mul_self]; exact h
  have hdet : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]; exact_mod_cast hn
  rw [hfU]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

theorem mp_hpar {k n : ℕ} (U : Mat k n) (hU : Uᴴ * U = 1) :
    MeasurePreserving (fun X : HPar k n => (U *ᵥ X.1, X.2)) volume volume :=
  (mp_unitary U hU).prod (MeasurePreserving.id volume)

theorem os_q (hOS : OS) (q p m : ℕ) (hq : q = p + 1) (δ γ : ℝ) (e : Fin (q + 1) → ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hγ : 0 < γ) (hγ8 : γ ≤ δ / 8) (he : ∀ l, 0 < e l) (hsum : e 0 + 2 * ∑ i : Fin q, e i.succ < γ / 2) :
    ∃ C : ℝ, ∀ (η η' : Fin q → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ), η' ⟨0, by omega⟩ ≠ 0 →
      ∫⁻ x, GI (fun l => s0N q m l - e l) δ η η' ζ c₀ x ≤
        ENNReal.ofReal (C * ‖η' ⟨0, by omega⟩‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4)) := by
  subst hq
  obtain ⟨C, hC⟩ := hOS p m δ γ e hδ hδ2 hγ hγ8 he hsum
  refine ⟨C, fun η η' ζ c₀ h0 => ?_⟩
  have e0 : (⟨0, by omega⟩ : Fin (p + 1)) = 0 := Fin.ext (by simp)
  rw [e0] at h0 ⊢
  exact hC η η' ζ c₀ h0

end BL

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.StarLastDotLast
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem ea_ga_nonneg {k r : ℕ} (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1)) : 0 ≤ Ga k r l Y := by
  let A : Matrix (Fin (2 * r + k + 1)) (Fin (l.val + 1)) ℂ := Matrix.of fun i b => Y (Fin.castLE (by omega) b) i
  have e : Aᴴ * A = Matrix.of fun a b : Fin (l.val + 1) =>
      star (Y (Fin.castLE (by omega) a)) ⬝ᵥ Y (Fin.castLE (by omega) b) := by
    ext a b; simp [A, Matrix.mul_apply, dotProduct]
  have h := (posSemidef_conjTranspose_mul_self A).det_nonneg
  rw [e] at h
  exact (Complex.nonneg_iff.mp h).1

theorem ea_ga_zero {k r : ℕ} (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : Ga k r 0 Y = (star (Y 0) ⬝ᵥ Y 0).re := by
  have h1 : ∀ (m : ℕ), m = 0 → ∀ A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ, A.det = A 0 0 := by
    rintro m rfl A; exact det_fin_one A
  unfold Ga
  rw [h1 (0 : Fin (r + 1)).val (by simp)]
  simp only [of_apply, Fin.castLE_zero]

theorem star_last_dot_last (k r' : ℕ) : star (es0 k r') ⬝ᵥ es0 k r' = 1 := by
  simp only [dotProduct, Pi.star_apply, last_basis_apply]
  rw [Finset.sum_eq_single ⟨2 * (1 + r') + k, by omega⟩] <;> simp [Fin.ext_iff]

theorem ea_gram_core {k r' m : ℕ} {κ : Mat k (1 + r')} (hκ : κᴴ * κ = 1) {D : ℝ} (hD : D ≠ 0)
    (W : Fin (m + 1) → Fin (2 * (1 + r') + k + 1) → ℂ) (U : Fin m → Fin (2 * r' + k + 1) → ℂ) (β : Fin m → ℂ)
    (h0 : W 0 = κ *ᵥ ((D : ℂ) • es0 k r'))
    (hs : ∀ i, W i.succ = κ *ᵥ (liftVec k 1 r' (U i) + β i • es0 k r')) :
    Matrix.det (Matrix.of fun a b => star (W a) ⬝ᵥ W b) =
      (D : ℂ) ^ 2 * Matrix.det (Matrix.of fun a b => star (U a) ⬝ᵥ U b) := by
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD
  have hsD : star (D : ℂ) = D := Complex.conj_ofReal D
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := Matrix.of fun a b => star (W a) ⬝ᵥ W b with hM
  have e00 : M 0 0 = (D : ℂ) ^ 2 := by
    simp only [hM, of_apply, h0, ea_dot_unit hκ, star_smul, smul_dotProduct, dotProduct_smul, star_last_dot_last,
      smul_eq_mul, hsD]
    ring
  have e0s : ∀ j, M 0 j.succ = (D : ℂ) * β j := by
    intro j
    simp only [hM, of_apply, h0, hs, ea_dot_unit hκ, star_smul, smul_dotProduct, dotProduct_add, dotProduct_smul,
      star_last_dot_lift, star_last_dot_last, smul_eq_mul, hsD]
    ring
  have es : ∀ i, M i.succ 0 = star (β i) * D := by
    intro i
    simp only [hM, of_apply, h0, hs, ea_dot_unit hκ, star_add, star_smul, add_dotProduct, smul_dotProduct,
      dotProduct_smul, star_lift_dot_last, star_last_dot_last, smul_eq_mul]
    ring
  have ess : ∀ i j, M i.succ j.succ = star (U i) ⬝ᵥ U j + star (β i) * β j := by
    intro i j
    simp only [hM, of_apply, hs, ea_dot_unit hκ, star_add, star_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, dot_lift_lift, star_lift_dot_last, star_last_dot_lift, star_last_dot_last, smul_eq_mul]
    ring
  let cc : Fin (m + 1) → ℂ := Fin.cons 0 (fun i => star (β i) / D)
  have hc0 : cc 0 = 0 := by simp [cc]
  have hcs : ∀ i, cc i.succ = star (β i) / D := fun i => by simp [cc]
  have hdet : M.det = (Matrix.of fun i j => M i j - cc i * M 0 j).det := by
    apply det_eq_of_forall_row_eq_smul_add_const cc 0 hc0
    intro i j
    simp only [of_apply, hc0, zero_mul, sub_zero]
    ring
  rw [hdet, det_eq_mul_minor_of_col_zero_alt]
  · have hsub : (Matrix.of fun i j => M i j - cc i * M 0 j).submatrix Fin.succ Fin.succ =
        Matrix.of fun a b => star (U a) ⬝ᵥ U b := by
      ext i j
      simp only [submatrix_apply, of_apply, ess, hcs, e0s]
      field_simp
      ring
    rw [hsub]
    simp only [of_apply, hc0, zero_mul, sub_zero, e00]
  · intro i
    simp only [of_apply, hcs, es, e00]
    field_simp
    ring

theorem ea_ga_sc {k r' : ℕ} {κ : Mat k (1 + r')} (hκ : κᴴ * κ = 1) {D : ℝ} (hD : D ≠ 0)
    (Y : Fin (1 + r' + 1) → Fin (2 * (1 + r') + k + 1) → ℂ) (U : Fin (r' + 1) → Fin (2 * r' + k + 1) → ℂ)
    (β : Fin (r' + 1) → ℂ) (h0 : Y 0 = κ *ᵥ ((D : ℂ) • es0 k r'))
    (hs : ∀ b, Y (sc r' b) = κ *ᵥ (liftVec k 1 r' (U b) + β b • es0 k r')) (l : Fin (r' + 1)) :
    Ga k (1 + r') (sc r' l) Y = D ^ 2 * Ga k r' l U := by
  have hle : l.val + 1 + 1 ≤ 1 + r' + 1 := by omega
  have hle' : l.val + 1 ≤ r' + 1 := by omega
  have key := ea_gram_core hκ hD (fun a : Fin (l.val + 1 + 1) => Y (Fin.castLE hle a))
    (fun i : Fin (l.val + 1) => U (Fin.castLE hle' i)) (fun i => β (Fin.castLE hle' i))
    (by simp only [Fin.castLE_zero]; exact h0)
    (fun i => by simp only [castLE_succ_eq r' hle i]; exact hs _)
  show (Matrix.det (Matrix.of fun a b : Fin (l.val + 1 + 1) =>
      star (Y (Fin.castLE hle a)) ⬝ᵥ Y (Fin.castLE hle b))).re = D ^ 2 * Ga k r' l U
  rw [key, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  rfl

theorem ea_yx_ga {k r' : ℕ} (hHM : HeisMem) (x : HPar k r') :
    0 < Ga k (1 + r') 0 (Yx k r' x) ∧ ∀ l, 0 ≤ Ga k (1 + r') l (Yx k r' x) := by
  refine ⟨?_, fun l => ea_ga_nonneg _ l⟩
  rw [ea_ga_zero]
  have hY0 : Yx k r' x 0 = (heis0 k r' x)⁻¹ *ᵥ es0 k r' := by rw [Yx, phi2, phiV_zero, levi_fixes_last_basis]
  have hne : Yx k r' x 0 ≠ 0 := by
    intro h
    have h1 : heis0 k r' x *ᵥ Yx k r' x 0 = es0 k r' := by
      rw [hY0, mulVec_mulVec, UH_mul_inv k (1 + r') (hHM k r' x).1, one_mulVec]
    rw [h, mulVec_zero] at h1
    have h2 := congrFun h1 ⟨2 * (1 + r') + k, by omega⟩
    simp [last_basis_apply] at h2
  exact (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hne)).1

theorem heisenberg_rankOne_decomposition_levi (hB2 : InductiveHeisenbergInputs) (hIW : IW) (k r' : ℕ) (hk : 1 ≤ k) (x : HPar k r') (c : ℂ) (hc : c ≠ 0) :
    ∃ κ ∈ Kset k (1 + r'), ∃ m ∈ GV k r', ∃ z : HPar k r',
      (heis0 k r' x)⁻¹ * w0 k r' c =
        κ * w0 k r' (c * (Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) : ℂ)) * ιLev k 1 r' m * heis0 k r' z ∧
      ∀ l : Fin (r' + 1), Ga k r' l (fun a => m *ᵥ phiV' k r' a) * Ga k (1 + r') 0 (Yx k r' x) =
        Ga k (1 + r') (sc r' l) (Yx k r' x) := by
  obtain ⟨_, hOSC, hOSM, _, _, _, _, hHI, _, hHM, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hHA⟩ := hB2
  have hG0 : 0 < Ga k (1 + r') 0 (Yx k r' x) := (ea_yx_ga hHM x).1
  have hD2 : Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) ^ 2 = Ga k (1 + r') 0 (Yx k r' x) := Real.sq_sqrt hG0.le
  set D := Real.sqrt (Ga k (1 + r') 0 (Yx k r' x)) with hDdef
  have hDpos : 0 < D := Real.sqrt_pos.mpr hG0
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hDpos.ne'
  have hsD : star (D : ℂ) = D := Complex.conj_ofReal D
  have hh := ea_hinv_gv hHI hHM x
  have hwc : w0 k r' c ∈ GV k (1 + r') := rankOne_mem_unitary hOSM hc
  obtain ⟨κ1, hκ1, τ, hτ, hYτ, hτn⟩ :=
    hIW k (1 + r') (Yx k r' x) hk (ea_yx_li hk hHI hHM hOSM x) (ea_yx_iso hk hHI hHM hOSM x)

  have hY0τ : Yx k r' x 0 = τ 0 0 • (κ1 *ᵥ e0 k r') := by
    rw [hYτ 0, Finset.sum_eq_single 0, phiV'_zero]
    · intro b _ hb
      rw [hτ (show id 0 < id b from Fin.pos_of_ne_zero hb), zero_smul]
    · simp
  have hτ0 : ‖τ 0 0‖ = D := by
    have h1 := hτn 0
    have hI : Finset.Iic (0 : Fin (1 + r' + 1)) = {0} := by
      ext j; simp only [Finset.mem_Iic, Finset.mem_singleton, Fin.le_zero_iff]
    rw [hI, Finset.prod_singleton] at h1
    rw [hDdef, ← h1, Real.sqrt_sq (norm_nonneg _)]

  set u : ℂ := (D : ℂ) / star (τ 0 0) with hudef
  have hsu : (star u)⁻¹ = τ 0 0 / D := by
    rw [hudef, star_div₀, star_star, hsD, inv_div]
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_div, norm_star, Complex.norm_of_nonneg hDpos.le, hτ0, div_self hDpos.ne']
  set κ := κ1 * w0 k r' u with hκdef
  have hκ : κ ∈ Kset k (1 + r') := ea_k_mul hκ1 (rankOne_mem_maximalCompact hOSM hu)
  have hκK := ea_k_iff.mp hκ
  have hY0 : Yx k r' x 0 = κ *ᵥ ((D : ℂ) • es0 k r') := by
    rw [hκdef, mulVec_smul, ← mulVec_mulVec, rankOneMatrix_last_basis, hsu, mulVec_smul, smul_smul, hY0τ]
    congr 1
    field_simp
  have hY0' : Yx k r' x 0 = (heis0 k r' x)⁻¹ *ᵥ es0 k r' := by
    rw [ea_yx, phiV'_zero, ← mulVec_mulVec, long_weyl_sends_base_to_dual, one_smul]

  have hκinv : κ⁻¹ ∈ GV k (1 + r') := ea_k_inv_mem hκ
  have hκκ : ∀ v, κ⁻¹ *ᵥ (κ *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, UH_inv_mul k (1 + r') hκK.1, one_mulVec]
  set g := κ⁻¹ * (heis0 k r' x)⁻¹ * w0 k r' c with hgdef
  have hg : g ∈ GV k (1 + r') := ea_gv_mul (ea_gv_mul hκinv hh) hwc
  have hge : g *ᵥ e0 k r' = (c * D) • es0 k r' := by
    calc g *ᵥ e0 k r' = κ⁻¹ *ᵥ (c • ((heis0 k r' x)⁻¹ *ᵥ es0 k r')) := by
          rw [hgdef, ← mulVec_mulVec, long_weyl_sends_base_to_dual, ← mulVec_mulVec, mulVec_smul]
      _ = (c * D) • es0 k r' := by
          rw [← hY0', hY0, mulVec_smul κ⁻¹ c, hκκ, smul_smul]
  have hC : herm (Hpk k (1 + r')) (g *ᵥ e0 k r') (e0 k r') = c * D := by
    rw [hge, herm_smul_l, herm_last_first_eq_one, mul_one]
  have hCne : (c * D : ℂ) ≠ 0 := mul_ne_zero hc hDc
  obtain ⟨⟨p1, m, z⟩, ⟨hm, hgp⟩, -⟩ := hOSC k r' g hg (by rw [hC]; exact hCne)
  dsimp only at hm hgp
  rw [hC] at hgp

  have hoe : oneStep k r' p1 (c * D) m z *ᵥ e0 k r' = (c * D) • ((heis0 k r' p1)⁻¹ *ᵥ es0 k r') := by
    rw [oneStep, ← mulVec_mulVec, heisenberg_first_basis hHA, ← mulVec_mulVec, levi_fixes_base_vector, ← mulVec_mulVec, long_weyl_sends_base_to_dual, mulVec_smul]
  have hn1 : (heis0 k r' p1)⁻¹ *ᵥ es0 k r' = es0 k r' := by
    have h' : (c * D) • ((heis0 k r' p1)⁻¹ *ᵥ es0 k r') = (c * D) • es0 k r' := by
      rw [← hoe, ← hgp, hge]
    exact smul_right_injective _ hCne h'
  rw [hHI, heisenberg_last_basis hHA] at hn1
  have hy : p1.1 = 0 := by
    funext j
    have h := congrFun hn1 (mp k r' j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lift_mp, last_basis_middle_zero, first_basis_middle_zero, mul_zero, add_zero,
      zero_add, Pi.neg_apply, neg_eq_zero] at h
    exact h
  have hb0 : hb k r' (-p1.1) (-p1.2) = 0 := by
    have h := congrFun hn1 0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lift_zero_pos, last_basis_zero, first_basis_zero, mul_one,
      zero_add] at h
    exact h
  have hs0 : p1.2 = 0 := by
    have h := congrArg Complex.im hb0
    simpa [hb] using h
  have hp1 : p1 = ((0 : Fin (2 * r' + k + 1) → ℂ), (0 : ℝ)) := Prod.ext hy hs0
  rw [hp1, oneStep, ea_heis0_zero, ea_inv_one, Matrix.one_mul] at hgp
  have hmain : (heis0 k r' x)⁻¹ * w0 k r' c = κ * g := by
    rw [hgdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, UH_mul_inv k (1 + r') hκK.1, Matrix.one_mul]
  refine ⟨κ, hκ, m, hm, z, ?_, ?_⟩
  · rw [hmain, hgp]; simp only [Matrix.mul_assoc]
  · intro l
    have hYs : ∀ b, Yx k r' x (sc r' b) = κ *ᵥ (liftVec k 1 r' (m *ᵥ phiV' k r' b) +
        (-(herm (Hpk k r') (phiV' k r' b) z.1 * (c * D))) • es0 k r') := by
      intro b
      have e1 : Yx k r' x (sc r' b) = ((heis0 k r' x)⁻¹ * w0 k r' c) *ᵥ liftVec k 1 r' (phiV' k r' b) := by
        rw [ea_yx, phiV'_sc, ← mulVec_mulVec, rankOneMatrix_lift, ← mulVec_mulVec, rankOneMatrix_lift]
      have hgl : g *ᵥ liftVec k 1 r' (phiV' k r' b) = liftVec k 1 r' (m *ᵥ phiV' k r' b) +
          (-(herm (Hpk k r') (phiV' k r' b) z.1 * (c * D))) • es0 k r' := by
        rw [hgp, ← mulVec_mulVec, ea_heis_lift hHA, ← mulVec_mulVec, mulVec_sub, lev_lift, mulVec_smul, levi_fixes_base_vector,
          mulVec_sub, rankOneMatrix_lift, mulVec_smul, long_weyl_sends_base_to_dual, smul_smul, sub_eq_add_neg, neg_smul]
      rw [e1, hmain, ← mulVec_mulVec, hgl]
    rw [ea_ga_sc hκK.2 hDpos.ne' (Yx k r' x) (fun a => m *ᵥ phiV' k r' a)
      (fun b => -(herm (Hpk k r') (phiV' k r' b) z.1 * (c * D))) hY0 hYs l, hD2, mul_comm]

end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XphiLinInd
section
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

section fs
variable {k r : ℕ}

theorem iic_eq (l : Fin (r + 1)) :
    Finset.Iic l = Finset.univ.map (Fin.castLEEmb (show l.val + 1 ≤ r + 1 by omega)) := by
  ext c
  simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and, Fin.le_def]
  constructor
  · intro hc; exact ⟨⟨c.val, by omega⟩, Fin.ext rfl⟩
  · rintro ⟨a, rfl⟩
    have := a.isLt
    simp only [Fin.castLEEmb_apply, Fin.val_castLE]
    omega

theorem ofReal_fsR (s : Fin (r + 1) → ℝ) (x : Mat k r) (τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hGa : ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l (fun a => x *ᵥ phiV' k r a))
    (hpos : ∀ l, 0 < Ga k r l (fun a => x *ᵥ phiV' k r a)) :
    ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  unfold fsR
  rw [ENNReal.ofReal_prod_of_nonneg (fun l _ => Real.rpow_nonneg (hpos l).le _)]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ht : Ga k r l (fun a => x *ᵥ phiV' k r a) = ((cl τ l : ℝ)) ^ 2 := by
    rw [← hGa l, iic_eq, Finset.prod_map, Finset.prod_pow, cl, NNReal.coe_prod]
    rfl
  have hc : 0 < (cl τ l : ℝ) := by
    have h0 := hpos l
    rw [ht] at h0
    exact lt_of_le_of_ne (NNReal.coe_nonneg _) (fun he => by rw [← he] at h0; simp at h0)
  rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← ENNReal.ofReal_rpow_of_pos hc,
    ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  ring

theorem xphi_linInd (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    LinearIndependent ℂ (fun a => x *ᵥ phiV' k r a) := by
  have hinj : Function.Injective (Matrix.mulVecLin x) := fun u v huv => by
    have h2 := congrArg (fun w => x⁻¹ *ᵥ w) huv
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, uh_inv_mul hx] using h2
  exact (phiV'_linInd k r hk).map' (Matrix.mulVecLin x) (LinearMap.ker_eq_bot.2 hinj)

theorem iw_at (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, x *ᵥ phiV' k r a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ s, ENNReal.ofReal (fsR k r s x) = ∏ l, ((cl τ l : ℝ≥0∞)) ^ (-s l) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hGa⟩ := hIW k r (fun a => x *ᵥ phiV' k r a) hk (xphi_linInd hk hx)
    (fun a b => by rw [herm_UH' _ hx]; exact phiV'_iso k r hk a b)
  exact ⟨κ, hκ, τ, hτ, hY, fun s => ofReal_fsR s x τ hGa (fun l => GS.ga_pos k r _ (xphi_linInd hk hx) l)⟩

theorem fsE_left (hIW : IW) (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (x⁻¹ * g) = ENNReal.ofReal (fsR k r s x) * FsE k r s (κ⁻¹ * g) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hx
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_left hx hκ.1 τ hτ hY g)

theorem fsE_right (hIW : IW) (hk : 1 ≤ k) {y : Mat k r} (hy : y ∈ GV k r) :
    ∃ κ ∈ Kset k r, ∀ (s : Fin (r + 1) → ℝ) (g : Mat k r),
      FsE k r s (g * y) = ENNReal.ofReal (fsR k r s y) * FsE k r s (g * κ) := by
  obtain ⟨κ, hκ, τ, hτ, hY, hf⟩ := iw_at hIW hk hy
  refine ⟨κ, hκ, fun s g => ?_⟩
  rw [hf s]
  exact fsE_fac s _ _ _ (dl_right τ hτ hY g)

theorem fsR_nonneg {k r : ℕ} (hk : 1 ≤ k) {x : Mat k r} (hx : x ∈ GV k r) (s : Fin (r + 1) → ℝ) :
    0 ≤ fsR k r s x :=
  Finset.prod_nonneg fun l _ => Real.rpow_nonneg (GS.ga_pos k r _ (xphi_linInd hk hx) l).le _

end fs

section meas
variable {k r : ℕ}

theorem cont_lmul (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) :=
  Continuous.matrix_mul continuous_const continuous_id

theorem cont_rmul (a : Mat k r) : Continuous (rmulF a : Mt k r → Mt k r) :=
  Continuous.matrix_mul continuous_id continuous_const

def lmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM a
  invFun := lmulM a⁻¹
  left_inv g := by
    show a⁻¹ * (a * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_inv_mul ha, Matrix.one_mul]; rfl
  right_inv g := by
    show a * (a⁻¹ * Matrix.of g) = g
    rw [← Matrix.mul_assoc, uh_mul_inv ha, Matrix.one_mul]; rfl
  measurable_toFun := (cont_lmul a).measurable
  measurable_invFun := (cont_lmul a⁻¹).measurable

def rmulE {a : Mat k r} (ha : a ∈ GV k r) : Mt k r ≃ᵐ Mt k r where
  toFun := rmulF a
  invFun := rmulF a⁻¹
  left_inv g := by
    show Matrix.of g * a * a⁻¹ = g
    rw [Matrix.mul_assoc, uh_mul_inv ha, Matrix.mul_one]; rfl
  right_inv g := by
    show Matrix.of g * a⁻¹ * a = g
    rw [Matrix.mul_assoc, uh_inv_mul ha, Matrix.mul_one]; rfl
  measurable_toFun := (cont_rmul a).measurable
  measurable_invFun := (cont_rmul a⁻¹).measurable

theorem lmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (lmulM a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (lmulE ha) (μ := μ)
  rw [show ⇑(lmulE ha) = lmulM a from rfl, hμ.left a ha] at h
  exact h.symm

theorem rmul_int {a : Mat k r} (ha : a ∈ GV k r) {μ : Measure (Mt k r)} (hμ : IsHaarOn (GV k r) μ)
    (f : Mt k r → ℝ≥0∞) : ∫⁻ g, f (rmulF a g) ∂μ = ∫⁻ g, f g ∂μ := by
  have h := lintegral_map_equiv f (rmulE ha) (μ := μ)
  rw [show ⇑(rmulE ha) = rmulF a from rfl, hμ.right a ha] at h
  exact h.symm

end meas

end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
end
end

