module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PLeadBlockGaussTail

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AePolynomialNonvanishingRows
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem eq_zero_of_hermNorm_eq_zero {n : ℕ} (h : HermNorm n) {u : Fin n → ℂ} (hu : h.norm u = 0) :
    u = 0 := by
  have hs : ∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => by positivity)).mp hu
  have hz : h.mat *ᵥ u = 0 := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hs i (Finset.mem_univ i)
    simpa using hi
  have := congrArg (fun w => h.mat⁻¹ *ᵥ w) hz
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det] using this

theorem eval_scale_groups {k n δ : ℕ} {q : MvPolynomial (Fin k × Fin n) ℂ} (hq : IsMultiHomog δ q)
    (c : Fin k → ℂ) (v : Fin k × Fin n → ℂ) :
    eval (fun ij => c ij.1 * v ij) q = (∏ i, c i ^ δ) * eval v q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hq (mem_support_iff.mp hd)
  have hrow : ∀ i, ∑ j, d (i, j) = δ := by
    intro i
    have := congrFun hw i
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simp [groupWeight, Fintype.sum_prod_type, Pi.single_apply, Finset.sum_apply] at this
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)] at this
    simpa using this
  have hc : ∏ ij : Fin k × Fin n, c ij.1 ^ d ij = ∏ i, c i ^ δ := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hrow]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem eval_nrmGroups_ne_zero {k n δ : ℕ} (h : HermNorm n) {q : MvPolynomial (Fin k × Fin n) ℂ}
    (hq : IsMultiHomog δ q) {v : Fin k × Fin n → ℂ} (hv : eval v q ≠ 0) :
    eval (nrmGroups h k v) q ≠ 0 := by
  classical
  have e : nrmGroups h k v =
      fun ij => (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) ij.1 * v ij := rfl
  rw [e, eval_scale_groups hq (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) v]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) hv
  rcases Nat.eq_zero_or_pos δ with rfl | hpos
  · simp
  refine pow_ne_zero _ fun hc => hv ?_
  have hn : h.norm (fun j => v (i, j)) = 0 := by simpa using hc
  have hr := eq_zero_of_hermNorm_eq_zero h hn
  have hv' : v = fun ij => (Function.update (1 : Fin k → ℂ) i 0) ij.1 * v ij := by
    funext ⟨a, j⟩
    by_cases ha : a = i
    · subst ha
      simpa using congrFun hr j
    · simp [Function.update_of_ne ha]
  rw [hv', eval_scale_groups hq, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hpos.ne']), zero_mul]

theorem exists_poly_eval_coefRows {n e : ℕ} (h : HermNorm n) {q : MvPolynomial (Fin e × Fin n) ℂ}
    (hq : q ≠ 0) :
    ∃ Q : MvPolynomial (Fin (e + 1) × Fin n) ℂ, Q ≠ 0 ∧
      ∀ π : Fin (e + 1) → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) Q = eval (coefRows h π) q := by
  let f : Fin e × Fin n → MvPolynomial (Fin (e + 1) × Fin n) ℂ :=
    fun ij => ∑ k, C (h.mat⁻¹ ij.2 k) * X (ij.1.succ, k)
  have key : ∀ π : Fin (e + 1) → Fin n → ℂ,
      eval (fun ij => π ij.1 ij.2) (bind₁ f q) = eval (coefRows h π) q := by
    intro π
    have hf : (fun ij => eval (fun ij => π ij.1 ij.2) (f ij)) = coefRows h π := by
      funext ij
      simp [f, coefRows, Matrix.mulVec, dotProduct]
    rw [← hf]
    exact eval₂Hom_bind₁ _ _ _ _
  refine ⟨bind₁ f q, fun hQ => hq (MvPolynomial.funext fun v => ?_), key⟩
  have hv : coefRows h (Fin.cons 0 fun i => h.mat *ᵥ fun j => v (i, j)) = v := by
    funext ij
    simp [coefRows, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]
  rw [map_zero, ← hv, ← key, hQ, map_zero]

theorem ae_eval_nrmGroups_coefRows_ne_zero :
    ∀ (n e δ : ℕ) (h : HermNorm n) (q : MvPolynomial (Fin e × Fin n) ℂ), q ≠ 0 → IsMultiHomog δ q →
      ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, eval (nrmGroups h e (coefRows h π)) q ≠ 0 := by
  intro n e δ h q hq hδ
  obtain ⟨Q, hQ, key⟩ := exists_poly_eval_coefRows h hq
  filter_upwards [ConeFibreDegree.ae_eval_matrix_ne_zero Q hQ] with π hπ
  rw [key] at hπ
  exact eval_nrmGroups_ne_zero h hδ hπ

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreCountRotationInvariant
section
set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv

noncomputable section

theorem measurePreserving_swapMat (m n : ℕ) :
    MeasurePreserving (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j)
      volume volume := by
  have h1 := (measurePreserving_curry_matrix m n).symm (MeasurableEquiv.curry (Fin m) (Fin n) ℂ)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin m => ℂ)
    (Equiv.prodComm (Fin m) (Fin n))
  have h3 := measurePreserving_curry_matrix n m
  have h4 := h3.comp (h2.comp h1)
  have h5 : (fun (π : Fin m → Fin n → ℂ) (j : Fin n) (i : Fin m) => π i j) =
      (MeasurableEquiv.curry (Fin n) (Fin m) ℂ) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin m => ℂ)
          (Equiv.prodComm (Fin m) (Fin n))) ∘
          (MeasurableEquiv.curry (Fin m) (Fin n) ℂ).symm := by
    funext π j i
    simp only [MeasurableEquiv.coe_curry_symm, MeasurableEquiv.curry, Function.comp]
    simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Function.curry_apply,
      MeasurableEquiv.coe_piCongrLeft]
    exact (Equiv.piCongrLeft_apply_apply (fun _ : Fin n × Fin m => ℂ)
      (Equiv.prodComm (Fin m) (Fin n)) (Function.uncurry π) (i, j)).symm
  rw [h5]
  exact h4

theorem transpose_mem_unitaryGroup' {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin m) ℂ) : Aᵀ ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.1 hA
  have h2 : (star A * A)ᵀ = 1 := by rw [h, Matrix.transpose_one]
  rw [Matrix.transpose_mul] at h2
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_map] using h2

def colAct {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (π : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun i j => ∑ k, unitMat V i k * π k j

theorem colAct_eq_mul {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (π : Fin m → Fin n → ℂ) :
    colAct V π = (unitMat V * (Matrix.of π : Matrix (Fin m) (Fin n) ℂ)) := by
  funext i j
  simp [colAct, Matrix.mul_apply]

theorem colAct_symm_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    colAct V.symm (colAct V π) = π := by
  have h : unitMat V.symm * unitMat V = 1 := by simpa using unitMat_mul_symm V.symm
  rw [colAct_eq_mul, colAct_eq_mul]
  show unitMat V.symm * (unitMat V * Matrix.of π) = π
  rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  rfl

theorem colAct_eq_swap {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    colAct V π = fun i j => ((fun k => π k j) ᵥ* (unitMat V)ᵀ) i := by
  funext i j
  simp [colAct, Matrix.vecMul, dotProduct, mul_comm]

theorem measurePreserving_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    MeasurePreserving (colAct (n := n) V) volume volume := by
  have h1 : MeasurePreserving (fun (ρ : Fin n → Fin m → ℂ) (j : Fin n) => ρ j ᵥ* (unitMat V)ᵀ)
      volume volume :=
    volume_preserving_pi fun _ =>
      measurePreserving_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V))
  have h2 := (measurePreserving_swapMat n m).comp (h1.comp (measurePreserving_swapMat m n))
  convert h2 using 1
  funext π
  rw [colAct_eq_swap]
  rfl

def colActEquiv {m n : ℕ} (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) where
  toFun := colAct V
  invFun := colAct V.symm
  left_inv := colAct_symm_colAct V
  right_inv π := by simpa using colAct_symm_colAct V.symm π
  measurable_toFun := (measurePreserving_colAct V).measurable
  measurable_invFun := (measurePreserving_colAct V.symm).measurable

theorem matGauss_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ) :
    matGauss (colAct V π) = matGauss π := by
  simp only [matGauss]
  congr 3
  rw [colAct_eq_swap, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact sum_norm_sq_vecMul (transpose_mem_unitaryGroup' (unitMat_mem V)) (fun k => π k j)

theorem linProj_colAct {m n : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : linProj (colAct V π) y = V (linProj π y) := by
  ext i
  rw [unitary_apply_eq_sum]
  simp only [linProj, colAct]
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem linProj_smul {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : linProj π (c • y) = c • linProj π y := by
  ext i
  simp only [linProj, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem cntOver_colAct {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsScaleStable S)
    {w : EuclideanSpace ℂ (Fin (e + 1))} (hw : w ≠ 0)
    (V : EuclideanSpace ℂ (Fin (e + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (e + 1)))
    (hV : V w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1)) (π : Fin (e + 1) → Fin n → ℂ) :
    cntOver S (colAct V π) (firstCoordVec (e + 1)) = cntOver S π w := by
  set c : ℂ := ((‖w‖ : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact_mod_cast norm_ne_zero_iff.2 hw
  have himg : ptsOver S (colAct V π) (firstCoordVec (e + 1)) =
      (fun y => c⁻¹ • y) '' ptsOver S π w := by
    ext z
    constructor
    · rintro ⟨hzS, hz⟩
      refine ⟨c • z, ⟨hS z hzS c hc0, ?_⟩, by simp [smul_smul, hc0]⟩
      apply V.injective
      rw [linProj_smul, map_smul, ← linProj_colAct, hz, hV]
    · rintro ⟨y, ⟨hyS, hy⟩, rfl⟩
      refine ⟨hS y hyS _ (inv_ne_zero hc0), ?_⟩
      rw [linProj_smul, linProj_colAct, hy, hV, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hinj : Set.InjOn (fun y : EuclideanSpace ℂ (Fin n) => c⁻¹ • y) (ptsOver S π w) :=
    (MulAction.injective₀ (inv_ne_zero hc0)).injOn
  simp only [cntOver]
  rw [himg, hinj.encard_image]

theorem lintegral_matGauss_cntOver :
    ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S →
      ∀ (w : EuclideanSpace ℂ (Fin (e + 1))), w ≠ 0 → ∀ T : ℝ≥0∞ → ℝ≥0∞,
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π w) =
          ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  intro n e S hS w hw T
  obtain ⟨U, -, -, hU⟩ := exists_unitary_leadCoordPlane (n := e + 1) (m := e + 1) (by omega) le_rfl
    ⊤ (by simp) w trivial
  have hV : U.symm w = ((‖w‖ : ℝ) : ℂ) • firstCoordVec (e + 1) := by
    rw [U.symm_apply_eq, hU]
  have hemb : MeasurableEmbedding (colAct (n := n) U.symm) :=
    (colActEquiv U.symm).measurableEmbedding
  have key := (measurePreserving_colAct (n := n) U.symm).lintegral_comp_emb hemb
    (fun π => matGauss π * T (cntOver S π (firstCoordVec (e + 1))))
  refine Eq.trans ?_ key
  refine lintegral_congr fun π => ?_
  simp only [matGauss_colAct, cntOver_colAct hS hw U.symm hV]

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton.CntInv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FubiniStudyLogLeLogNorm
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem fsLog_pointOf_le_log_norm : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)), y ≠ 0 →
  ∑ j, u j * h.pointOf y j ≠ 0 → fsLog h u (h.pointOf y) ≤ Real.log (h.norm u) :=
  fun _ h _ _ _ hne => fsLog_le h hne

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFinite
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

def entryGauss (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-‖z‖ ^ 2))

theorem measurable_entryGauss : Measurable entryGauss := by
  unfold entryGauss
  exact ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp ((continuous_norm.pow 2).neg)).measurable

theorem lintegral_entryGauss_lt_top : ∫⁻ z, entryGauss z < ⊤ := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ((continuous_pow 2).neg)).measurable
  have h1 : ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) < ⊤ := by
    simpa using (integrable_exp_neg_mul_sq one_pos).lintegral_lt_top
  have he : ∀ z : ℂ, entryGauss z =
      (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)))
        (Complex.measurableEquivRealProd z) := by
    intro z
    show ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) =
      ENNReal.ofReal (Real.exp (-z.re ^ 2)) * ENNReal.ofReal (Real.exp (-z.im ^ 2))
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    congr 2
    ring
  calc ∫⁻ z, entryGauss z
      = ∫⁻ z, (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)))
          (Complex.measurableEquivRealProd z) := lintegral_congr he
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Real.exp (-p.1 ^ 2)) * ENNReal.ofReal (Real.exp (-p.2 ^ 2)) :=
        Complex.volume_preserving_equiv_real_prod.lintegral_comp
          ((hm.comp measurable_fst).mul (hm.comp measurable_snd))
    _ = (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2))) * ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x ^ 2)) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul hm.aemeasurable hm.aemeasurable
    _ < ⊤ := ENNReal.mul_lt_top h1 h1

theorem lintegral_entryGauss_pos : 0 < ∫⁻ z, entryGauss z := by
  rw [pos_iff_ne_zero, Ne, lintegral_eq_zero_iff measurable_entryGauss]
  intro h
  obtain ⟨z, hz⟩ := h.exists
  have : entryGauss z ≠ 0 := by
    simp [entryGauss, Real.exp_pos]
  exact this hz

theorem gaussM_univ_eq (m n : ℕ) :
    gaussM m n Set.univ = ∏ _i : Fin m, ∏ _j : Fin n, ∫⁻ z, entryGauss z := by
  have hx : ∀ x : Fin m → Fin n → ℂ, matGauss x = ∏ i, ∏ j, entryGauss (x i j) := by
    intro x
    simp only [matGauss, entryGauss, ← Finset.sum_neg_distrib, Real.exp_sum]
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
  rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [hx]
  have hmeas : ∀ _i : Fin m, Measurable (fun y : Fin n → ℂ => ∏ j, entryGauss (y j)) := fun _ =>
    Finset.measurable_prod _ fun j _ => measurable_entryGauss.comp (measurable_pi_apply j)
  have hin : ∫⁻ y : Fin n → ℂ, ∏ j, entryGauss (y j) = ∏ _j : Fin n, ∫⁻ z, entryGauss z := by
    rw [volume_pi]
    exact LeadBlockGaussTail.lintegral_pi_prod (volume : Measure ℂ) n (fun _ => entryGauss)
      fun _ => measurable_entryGauss
  have hout := LeadBlockGaussTail.lintegral_pi_prod (volume : Measure (Fin n → ℂ)) m
    (fun _ y => ∏ j, entryGauss (y j)) hmeas
  rw [volume_pi]
  rw [hout]
  exact Finset.prod_congr rfl fun _ _ => hin

theorem gaussM_univ_pos_lt_top : ∀ m n : ℕ, 0 < gaussM m n Set.univ ∧ gaussM m n Set.univ < ⊤ := by
  intro m n
  rw [gaussM_univ_eq]
  constructor
  · exact CanonicallyOrderedAdd.prod_pos.2 fun i _ =>
      CanonicallyOrderedAdd.prod_pos.2 fun j _ => lintegral_entryGauss_pos
  · exact ENNReal.prod_lt_top fun i _ => ENNReal.prod_lt_top fun j _ => lintegral_entryGauss_lt_top

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionBallIndicator
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

theorem coneTangentAverage_inter (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J) (hm : 0 < m) (hmn : m ≤ n)
    (hfib : ∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤)
    (A : Set (EuclideanSpace ℂ (Fin n))) (hA : MeasurableSet A) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ y in coneSet h J ∩ A,
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      ∫⁻ y in coneSet h J ∩ A, tangentGaussProfile n m ‖y‖
        ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
  have hMass : ConeLocalMass.Statement := ConeLocalMass.of_open ConeFiniteFibreDim.proof
  have hMeas : ConeJacMeasurable.Statement :=
    ConeJacMeasurable.proof TangentJacCompress.proof KernelProjMeasurable.proof
  have hDim : ConeTangentDim.Statement :=
    ConeTangentDim.proof (ConeKrullDimLe.proof ConeFiniteFibreDim.proof) NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)
  have hInv : TangentGaussInvariant.Statement := TangentGaussInvariant.proof
  have hres : (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J ∩ A) =
      ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
        Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)).restrict A := by
    rw [Measure.restrict_restrict hA, Set.inter_comm]
  rw [hres]
  have hS : SFinite ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) :=
    sFinite_restrict_of_ball _ _ (hMass n m h J hJ hm hmn hfib)
  have hG : Measurable fun π : Fin m → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin m → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hP : Continuous fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) =>
      linProj p.1 p.2 := by
    unfold linProj
    fun_prop
  have hF : AEMeasurable
      (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
        matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) :=
    (hG.comp measurable_fst).aemeasurable.mul
      (((measurable_one.indicator Metric.isOpen_ball.measurableSet).comp
        hP.measurable).aemeasurable.mul (hMeas n m h J hJ hm hmn hfib).ennreal_ofReal)
  have hFA : AEMeasurable
      (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
        matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        (((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)).restrict A)) := by
    have hpr := Measure.prod_restrict (μ := (volume : Measure (Fin m → Fin n → ℂ)))
      (ν := (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
        Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) Set.univ A
    rw [Measure.restrict_univ] at hpr
    rw [hpr]
    exact hF.restrict
  rw [show (fun π : Fin m → Fin n → ℂ => matGauss π *
      ∫⁻ y in A, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y)
          ∂((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) =
      fun π => ∫⁻ y in A, matGauss π *
        ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y))
          ∂((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)) from
    funext fun π => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm,
    lintegral_lintegral_swap hFA]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hDim n m h J hJ hm hmn hfib,
    ae_restrict_mem (isClosed_coneSet h J).measurableSet] with y hy hyC
  simp only [← mul_assoc]
  exact hInv n m hm hmn _ hy y (mem_coneTangent_self h hJ hyC)

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

