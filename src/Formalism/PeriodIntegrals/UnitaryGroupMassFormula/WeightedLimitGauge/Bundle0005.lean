module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PhiDiff
section
noncomputable section

open Matrix NormedSpace

namespace PI.RhsWLim.W

open PI.RhsWLim

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {k r : ℕ}

lemma opBeta_add (q q' : TrE k) (a : Fin k) :
    opBeta k (q + q') a = opBeta k q a + opBeta k q' a := by
  simp only [opBeta, PiLp.add_apply, Complex.ofReal_add]; ring

lemma opBeta_smul (c : ℝ) (q : TrE k) (a : Fin k) :
    opBeta k (c • q) a = (c : ℂ) * opBeta k q a := by
  simp only [opBeta, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]; ring

def opGenLin (k r : ℕ) : TrE k →ₗ[ℝ] Mat k r where
  toFun := opGen k r
  map_add' q q' := by
    ext i j
    simp only [opGen, Matrix.add_apply]
    split_ifs <;> simp [opBeta_add, star_add]; ring
  map_smul' c q := by
    ext i j
    simp only [opGen, Matrix.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [opBeta_smul, Complex.real_smul, star_mul', Complex.conj_ofReal]; ring

def opGenL (k r : ℕ) : TrE k →L[ℝ] Mat k r := LinearMap.toContinuousLinearMap (opGenLin k r)

@[simp] lemma opGenL_apply (q : TrE k) : opGenL k r q = opGen k r q := rfl

lemma opGen_zero : opGen k r (0 : TrE k) = 0 := (opGenLin k r).map_zero

def mvL (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Mat k r →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by simp [Matrix.smul_mulVec] }

@[simp] lemma mvL_apply (v : Fin (2 * r + k + 1) → ℂ) (M : Mat k r) : mvL k r v M = M *ᵥ v := rfl

def psiV (k r : ℕ) (T' : ℝ) (q : TrE k) : Fin (2 * r + k + 1) → ℂ :=
  NormedSpace.exp (opGen k r q) *ᵥ opBase k r T'

lemma psiV_zero (T' : ℝ) : psiV k r T' 0 = opBase k r T' := by
  simp [psiV, opGen_zero, NormedSpace.exp_zero]

lemma opBase_last (T' : ℝ) : opBase k r T' (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
  simp [opBase, wLast, bvec]

lemma mulVec_base (T' : ℝ) (M : Mat k r) (i : Fin (2 * r + k + 1)) :
    (M *ᵥ opBase k r T') i = (Real.sqrt T' : ℂ) * M i (wI k r (Fin.last k)) := by
  simp [opBase, wLast, bvec, Matrix.mulVec_smul]

lemma opGen_y (q : TrE k) (a : Fin k) :
    opGen k r q (wI k r a.castSucc) (wI k r (Fin.last k)) = opBeta k q a := by
  simp [opGen, wI, a.isLt]

lemma opGen_c (q : TrE k) :
    opGen k r q (wI k r (Fin.last k)) (wI k r (Fin.last k)) = (q none : ℂ) * Complex.I := by
  simp [opGen, wI]

lemma psiV_contDiffAt (T' : ℝ) : ContDiffAt ℝ 1 (psiV k r T') 0 := by
  have h1 : ContDiffAt ℝ 1 (opGen k r) (0 : TrE k) := (opGenL k r).contDiff.contDiffAt
  have h2 : ContDiffAt ℝ 1 (NormedSpace.exp : Mat k r → Mat k r) (opGen k r 0) :=
    (exp_analytic (𝕂 := ℝ) (opGen k r 0)).contDiffAt
  exact (mvL k r (opBase k r T')).contDiff.contDiffAt.comp (0 : TrE k) (h2.comp (0 : TrE k) h1)

lemma psiV_strict (T' : ℝ) : HasStrictFDerivAt (psiV k r T')
    ((mvL k r (opBase k r T')).comp ((1 : Mat k r →L[ℝ] Mat k r).comp (opGenL k r))) 0 := by
  have h1 : HasStrictFDerivAt (opGen k r) (opGenL k r) (0 : TrE k) := (opGenL k r).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r) (1 : Mat k r →L[ℝ] Mat k r)
      (opGen k r 0) := by
    rw [opGen_zero]
    exact hasStrictFDerivAt_exp_zero_of_radius_pos (expSeries_radius_pos ℝ (Mat k r))
  exact (mvL k r (opBase k r T')).hasStrictFDerivAt.comp (0 : TrE k) (h2.comp (0 : TrE k) h1)

lemma dpsi_apply (T' : ℝ) (q : TrE k) (i : Fin (2 * r + k + 1)) :
    ((mvL k r (opBase k r T')).comp ((1 : Mat k r →L[ℝ] Mat k r).comp (opGenL k r))) q i
      = (Real.sqrt T' : ℂ) * opGen k r q i (wI k r (Fin.last k)) := by
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply, opGenL_apply, mvL_apply]
  exact mulVec_base T' _ i

def dgn (T' : ℝ) : Option (Fin k × Bool) → ℝ := fun o => match o with
  | none => 1
  | some _ => Real.sqrt T' / Real.sqrt 2

def DL (k : ℕ) (T' : ℝ) : TrE k →L[ℝ] TrE k := LinearMap.toContinuousLinearMap
  { toFun := fun q => (WithLp.equiv 2 (Option (Fin k × Bool) → ℝ)).symm (fun o => dgn T' o * q o)
    map_add' := fun q q' => by ext o; simp [mul_add]
    map_smul' := fun c q => by ext o; simp; ring }

@[simp] lemma DL_apply (T' : ℝ) (q : TrE k) (o : Option (Fin k × Bool)) : DL k T' q o = dgn T' o * q o := rfl

lemma DL_det (T' : ℝ) (hT : 0 < T') : (DL k T').det = (T' / 2) ^ k := by
  show LinearMap.det (DL k T' : TrE k →ₗ[ℝ] TrE k) = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis]
  have hm : LinearMap.toMatrix (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis
      (EuclideanSpace.basisFun (Option (Fin k × Bool)) ℝ).toBasis (DL k T' : TrE k →ₗ[ℝ] TrE k)
      = Matrix.diagonal (dgn T') := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    simp only [OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe, DL_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  rw [hm, Matrix.det_diagonal, Fintype.prod_option]
  simp only [dgn, one_mul]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    mul_comm k 2, pow_mul, div_pow, Real.sq_sqrt hT.le, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

lemma phiT_coord_c (T' : ℝ) (q : TrE k) :
    phiT k r T' q none = (Complex.log (psiV k r T' q (wI k r (Fin.last k)))).im := by
  rw [Complex.log_im]; rfl

lemma psiV_last_zero (T' : ℝ) : psiV k r T' 0 (wI k r (Fin.last k)) = (Real.sqrt T' : ℂ) := by
  rw [psiV_zero, opBase_last]

lemma beta_re_im (T' : ℝ) (q : TrE k) (a : Fin k) :
    (Real.sqrt T' : ℂ) * opBeta k q a =
      ((Real.sqrt T' / Real.sqrt 2 * q (some (a, false)) : ℝ) : ℂ)
        + ((Real.sqrt T' / Real.sqrt 2 * q (some (a, true)) : ℝ) : ℂ) * Complex.I := by
  have h2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  simp only [opBeta]
  push_cast
  field_simp

theorem phiT_contDiffAt (T' : ℝ) (hT : 0 < T') : ContDiffAt ℝ 1 (phiT k r T') 0 := by
  have hp := psiV_contDiffAt (k := k) (r := r) T'
  refine (contDiffAt_piLp 2).2 fun o => ?_
  rcases o with _ | ⟨a, b⟩
  · have hlog : ContDiffAt ℝ 1 Complex.log (psiV k r T' 0 (wI k r (Fin.last k))) := by
      rw [psiV_last_zero]
      exact (Complex.contDiffAt_log (Complex.ofReal_mem_slitPlane.2 (Real.sqrt_pos.2 hT))).restrict_scalars ℝ
    have := Complex.imCLM.contDiff.contDiffAt.comp (0 : TrE k)
      (hlog.comp (0 : TrE k) ((ContinuousLinearMap.proj (R := ℝ) (wI k r (Fin.last k))).contDiff.contDiffAt.comp
        (0 : TrE k) hp))
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q => ?_)
    exact phiT_coord_c T' q
  · have hj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ)
      (wI k r a.castSucc)).contDiff.contDiffAt.comp (0 : TrE k) hp
    cases b
    · exact Complex.reCLM.contDiff.contDiffAt.comp (0 : TrE k) hj
    · exact Complex.imCLM.contDiff.contDiffAt.comp (0 : TrE k) hj

theorem phiT_strict (T' : ℝ) (hT : 0 < T') : HasStrictFDerivAt (phiT k r T') (DL k T') 0 := by
  have hp := psiV_strict (k := k) (r := r) T'
  refine (hasStrictFDerivAt_piLp 2).2 fun o => ?_
  rcases o with _ | ⟨a, b⟩
  · have hs : ((Real.sqrt T' : ℝ) : ℂ) ∈ Complex.slitPlane :=
      Complex.ofReal_mem_slitPlane.2 (Real.sqrt_pos.2 hT)
    have hlog := ((Complex.hasStrictDerivAt_log hs).hasStrictFDerivAt).restrictScalars ℝ
    rw [← psiV_last_zero (k := k) (r := r)] at hlog
    have H := Complex.imCLM.hasStrictFDerivAt.comp (0 : TrE k)
      (hlog.comp (0 : TrE k) ((ContinuousLinearMap.proj (R := ℝ) (wI k r (Fin.last k))).hasStrictFDerivAt.comp
        (0 : TrE k) hp))
    have hf : (fun x => phiT k r T' x none) =
        Complex.imCLM ∘ Complex.log ∘ (fun f : Fin (2 * r + k + 1) → ℂ => f (wI k r (Fin.last k))) ∘ psiV k r T' := by
      funext x; exact phiT_coord_c T' x
    rw [hf]
    refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
    have hsq : (Real.sqrt T' : ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; positivity
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.proj_apply,
      opGenL_apply, mvL_apply, mulVec_base, opGen_c, psiV_last_zero, Complex.imCLM_apply, PiLp.proj_apply,
      DL_apply, dgn, one_mul, smul_eq_mul]
    have : (Real.sqrt T' : ℂ) * ((q none : ℂ) * Complex.I) * (Real.sqrt T' : ℂ)⁻¹ = (q none : ℂ) * Complex.I := by
      field_simp
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, this]; simp
  · have Hj := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * r + k + 1) => ℂ)
      (wI k r a.castSucc)).hasStrictFDerivAt.comp (0 : TrE k) hp
    cases b
    · have H := Complex.reCLM.hasStrictFDerivAt.comp (0 : TrE k) Hj
      refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, dpsi_apply, opGen_y,
        beta_re_im, Complex.reCLM_apply, PiLp.proj_apply, DL_apply, dgn]
      change ((opGen k r q *ᵥ opBase k r T') (wI k r a.castSucc)).re = _
      rw [mulVec_base, opGen_y, beta_re_im]
      simp
    · have H := Complex.imCLM.hasStrictFDerivAt.comp (0 : TrE k) Hj
      refine H.congr_fderiv (ContinuousLinearMap.ext fun q => ?_)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, dpsi_apply, opGen_y,
        beta_re_im, Complex.imCLM_apply, PiLp.proj_apply, DL_apply, dgn]
      change ((opGen k r q *ᵥ opBase k r T') (wI k r a.castSucc)).im = _
      rw [mulVec_base, opGen_y, beta_re_im]
      simp

theorem hermitianDefectAdd : PhiDiff := by
  intro k r T' _ hT
  refine ⟨phiT_contDiffAt T' hT, ?_⟩
  rw [(phiT_strict (r := r) T' hT).hasFDerivAt.fderiv]
  exact DL_det T' hT

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsTest
section
noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k r : ℕ}

theorem wI_injective : Function.Injective (wI k r) := by
  intro a b h
  have h' := congrArg Fin.val h
  simp only [PI.RhsWLim.wI] at h'
  exact Fin.ext (by omega)

theorem sum_wb (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → f i = 0) :
    ∑ i, f i = ∑ j : Fin (k + 1), f (wI k r j) := by
  have h1 : ∑ j : Fin (k + 1), f (PI.RhsWLim.wI k r j) = ∑ i ∈ Finset.univ.image (PI.RhsWLim.wI k r), f i :=
    (Finset.sum_image (fun a _ b _ h => wI_injective h)).symm
  rw [h1]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro i _ hi
  apply hf
  by_contra hc
  apply hi
  rw [Finset.mem_image]
  exact ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _, Fin.ext (by simp only [PI.RhsWLim.wI]; omega)⟩

theorem tau_wI (j : Fin (k + 1)) : HU.tau k r (wI k r j) = wI k r j := by
  have hj := j.isLt
  apply Fin.ext
  show (if r + j.val < r ∨ r + k < r + j.val then 2 * r + k - (r + j.val) else r + j.val) = r + j.val
  rw [if_neg (by omega)]

theorem hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = HU.sgn k r i * v (HU.tau k r i) := by
  simp [Matrix.mulVec, dotProduct, PI.RhsWLim.W.HU.hpk_row, ite_mul]

theorem sgn_wI (j : Fin (k + 1)) : HU.sgn k r (wI k r j) = if j = Fin.last k then -1 else 1 := by
  by_cases h : j = Fin.last k
  · subst h
    simp [PI.RhsWLim.W.HU.sgn, PI.RhsWLim.wI]
  · have hne : j.val ≠ k := fun e => h (Fin.ext (by rw [Fin.val_last]; exact e))
    simp [PI.RhsWLim.W.HU.sgn, PI.RhsWLim.wI, h, hne]

theorem herm_wb (v z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) v z = herm (Hb k) (wbPart k r v) (wbPart k r z) := by
  simp only [PI.RhsWLim.herm, dotProduct]
  rw [sum_wb (k := k) (r := r)]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [Pi.star_apply, hpk_mulVec_apply, PI.RhsWLim.Hb, Matrix.mulVec_diagonal, PI.RhsWLim.wbPart,
      sgn_wI, tau_wI]
  · intro i hi
    simp [hz i hi]

theorem embWb_wI (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (j m : Fin (k + 1)) :
    embWb k r μ (wI k r j) (wI k r m) = μ j m := by
  have hj := j.isLt
  have hm := m.isLt
  have hc : (r ≤ (PI.RhsWLim.wI k r j).val ∧ (PI.RhsWLim.wI k r j).val ≤ r + k) ∧
      (r ≤ (PI.RhsWLim.wI k r m).val ∧ (PI.RhsWLim.wI k r m).val ≤ r + k) := by
    simp only [PI.RhsWLim.wI]
    omega
  unfold PI.RhsWLim.embWb
  rw [dite_eq_left hc]
  exact congrArg₂ μ (Fin.ext (by simp [PI.RhsWLim.wI])) (Fin.ext (by simp [PI.RhsWLim.wI]))

theorem wbPart_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') :
    wbPart k r (embWb k r μ *ᵥ z') = μ *ᵥ wbPart k r z' := by
  funext j
  simp only [PI.RhsWLim.wbPart, Matrix.mulVec, dotProduct]
  rw [sum_wb (k := k) (r := r)]
  · simp only [embWb_wI]
  · intro i hi
    simp [hz' i hi]

theorem herm_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z) (hz' : inWb k r z') :
    herm (Hpk k r) (embWb k r μ *ᵥ z') z = herm (Hb k) (μ *ᵥ wbPart k r z') (wbPart k r z) := by
  rw [herm_wb _ _ hz, wbPart_emb μ z' hz']

theorem herm_fix {h : Mat k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) (u : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (h *ᵥ u) z = herm (Hpk k r) u z := by
  obtain ⟨hU, -, hfix⟩ := hh
  have hU' : hᴴ * PI.RhsWLim.Hpk k r * h = PI.RhsWLim.Hpk k r := hU
  unfold PI.RhsWLim.herm
  calc star z ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ (h *ᵥ u))
      = star (h *ᵥ z) ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ (h *ᵥ u)) := by rw [hfix]
    _ = star z ⬝ᵥ ((hᴴ * PI.RhsWLim.Hpk k r * h) *ᵥ u) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = star z ⬝ᵥ (PI.RhsWLim.Hpk k r *ᵥ u) := by rw [hU']

theorem inv_fix {h : Mat k r} {z : Fin (2 * r + k + 1) → ℂ} (hh : h ∈ UWset k r z) : h⁻¹ *ᵥ z = z := by
  obtain ⟨hU, -, hfix⟩ := hh
  have hdet := PI.RhsWLim.W.HU.isUnit_of_uh hU
  calc h⁻¹ *ᵥ z = h⁻¹ *ᵥ (h *ᵥ z) := by rw [hfix]
    _ = z := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul h hdet, Matrix.one_mulVec]

theorem circle_null (c : ℝ) : (volume : Measure ℂ) {ζ | Complex.normSq ζ = c} = 0 := by
  have hsub : {ζ : ℂ | Complex.normSq ζ = c} ⊆ Metric.sphere (0 : ℂ) (Real.sqrt c) := by
    intro ζ hζ
    have hζ' : Complex.normSq ζ = c := hζ
    rw [mem_sphere_zero_iff_norm, ← hζ', Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg ζ)]
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 _)

private theorem pairF_mul_embWb_mul_inv {z z' : Fin (2 * r + k + 1) → ℂ} (hz : PI.RhsWLim.inWb k r z) (hz' : PI.RhsWLim.inWb k r z')
    {p q : PI.RhsWLim.Mat k r} (hp : p ∈ PI.RhsWLim.UWset k r z) (hq : q ∈ PI.RhsWLim.UWset k r z')
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    pairF k r z z' (fun i j => (p * PI.RhsWLim.embWb k r μ * q⁻¹) i j) =
      PI.RhsWLim.herm (PI.RhsWLim.Hb k) (μ *ᵥ PI.RhsWLim.wbPart k r z') (PI.RhsWLim.wbPart k r z) := by
  show PI.RhsWLim.herm (PI.RhsWLim.Hpk k r) ((p * PI.RhsWLim.embWb k r μ * q⁻¹) *ᵥ z') z = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, herm_fix hp,
    inv_fix hq, herm_emb μ z z' hz hz']

theorem rhsTest : RhsTest := by
  intro k r z z' μW μW' a a' μsec hD g hg
  simp only [PI.RhsWLim.rhsW]
  obtain ⟨-, -, hnW, -⟩ := hD.haarW
  obtain ⟨-, -, hnW', -⟩ := hD.haarW'
  obtain ⟨-, hS⟩ := hD.sec
  have hW : ∀ᵐ x ∂μW, Matrix.of x ∈ PI.RhsWLim.UWset k r z := ae_iff.mpr hnW
  have hW' : ∀ᵐ x ∂μW', Matrix.of x ∈ PI.RhsWLim.UWset k r z' := ae_iff.mpr hnW'
  have hae : ∀ᵐ ζ : ℂ, Complex.normSq ζ ≠ PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' := by
    rw [ae_iff]
    simpa using circle_null (PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z')
  rw [← lintegral_const_mul' (ENNReal.ofReal (a * a')) _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [hae] with ζ hζ
  try dsimp only
  by_cases hreg : PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' < Complex.normSq ζ
  · have hsec := (hS ζ hreg).2
    rw [lintegral_congr_ae (μ := μW) (g := fun _ => g ζ * ENNReal.ofReal a') ?_]
    · rw [lintegral_const, hD.massW, ENNReal.ofReal_mul hD.a_pos.le]
      ring
    · filter_upwards [hW] with h hh
      try dsimp only
      rw [lintegral_congr_ae (μ := μW') (g := fun _ => g ζ) ?_]
      · rw [lintegral_const, hD.massW']
      · filter_upwards [hW'] with h' hh'
        exact (congrArg g (pairF_mul_embWb_mul_inv hD.z_mem hD.z'_mem hh hh' (μsec ζ))).trans (congrArg g hsec)
  · have hle : ¬ (PI.RhsWLim.Tz k r z * PI.RhsWLim.Tz k r z' ≤ Complex.normSq ζ) :=
      fun hle => hreg (lt_of_le_of_ne hle (Ne.symm hζ))
    have h0 : PI.RhsWLim.zWeight k (PI.RhsWLim.Tz k r z) (PI.RhsWLim.Tz k r z') ζ = 0 := by
      unfold PI.RhsWLim.zWeight
      exact if_neg hle
    simp [h0]

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvR
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

theorem inv_fix {b : Mat k r} (hb : IsUnit b.det) {v : Fin (2 * r + k + 1) → ℂ} (h : b *ᵥ v = v) :
    b⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]

theorem uwset_inv {b : Mat k r} (hb : b ∈ UWset k r z') : b⁻¹ ∈ UWset k r z' := by
  obtain ⟨hU, hfix, hz⟩ := hb
  have hu := HU.isUnit_of_uh hU
  exact ⟨HU.uh_inv hU, fun a => ⟨inv_fix hu (hfix a).1, inv_fix hu (hfix a).2⟩, inv_fix hu hz⟩

theorem inner_r (hW : IsHaarOn (UWset k r z') μW') (M : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ)
    (b : Mat k r) (hb : b ∈ UWset k r z') :
    ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW' =
      ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by
  have hbi : b⁻¹ ∈ UWset k r z' := uwset_inv hb
  have hu : IsUnit (b⁻¹).det := HU.isUnit_of_uh hbi.1
  have hbu : IsUnit b.det := HU.isUnit_of_uh hb.1
  have hmap : μW'.map (lmulM b⁻¹) = μW' := hW.2.2.2 _ hbi
  have key : ∀ h' : Mt k r, M * (Matrix.of h')⁻¹ * b = M * (Matrix.of (lmulE b⁻¹ hu h'))⁻¹ := by
    intro h'
    change M * (Matrix.of h')⁻¹ * b = M * (b⁻¹ * Matrix.of h')⁻¹
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hbu, mul_assoc]
  calc ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW'
      = ∫⁻ h', (fun y : Mt k r => φ (fun i j => (M * (Matrix.of y)⁻¹) i j)) (lmulE b⁻¹ hu h') ∂μW' := by
        refine lintegral_congr fun h' => ?_
        simp only [key h']
    _ = ∫⁻ y, φ (fun i j => (M * (Matrix.of y)⁻¹) i j) ∂(μW'.map (lmulE b⁻¹ hu)) :=
        by rw [lintegral_map_equiv]
    _ = ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by
        rw [show ⇑(lmulE b⁻¹ hu) = lmulM b⁻¹ from rfl, hmap]

theorem rhsW_rmul (hd : WbData k r z z' μW μW' a a' μsec) (b : Mat k r) (hb : b ∈ UWset k r z')
    (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    rhsW k r z z' μW μW' μsec (fun x => φ (rmulM b x)) = rhsW k r z z' μW μW' μsec φ := by
  unfold rhsW
  refine lintegral_congr fun ζ => ?_
  congr 1
  refine lintegral_congr fun h => ?_
  exact inner_r hd.haarW' _ φ hφ b hb

theorem rInvNu : RInvNu := by
  intro k r z z' μW μW' a a' μsec hd b hb
  have hm : Measurable (rmulM b : Mt k r → Mt k r) := (rmulM_cont b).measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  have hi : Measurable (s.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hs
  have e1 := ZetaZeros.repr hd (s.indicator 1) hi
  have e2 := ZetaZeros.repr hd (fun x => s.indicator 1 (rmulM b x)) (hi.comp hm)
  have e3 := rhsW_rmul hd b hb (s.indicator 1) hi
  rw [lintegral_indicator_one hs] at e1
  have e4 : ∫⁻ x, s.indicator 1 (rmulM b x) ∂(nuR k r z z' μW μW' μsec) =
      nuR k r z z' μW μW' μsec (rmulM b ⁻¹' s) := by
    rw [← lintegral_indicator_one (hm hs)]
    refine lintegral_congr fun x => ?_
    simp only [Set.indicator, Pi.one_apply]
    rfl
  rw [← e4, ← e2, e3, e1]

end PI.RhsWLim.W.RI
end
end

