module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsURepOnOfIsTau
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Dec.FormF
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.PsiBound

lemma det_exp_sq {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y) :
    (NormedSpace.exp Y).det * (NormedSpace.exp Y).det = 1 := by
  have hJ := Jm_mul_self ε
  have h1 : Jm ε * Y * Jm ε = -Y := by
    rw [Matrix.mul_assoc, h.2, Matrix.mul_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h2 : NormedSpace.exp (Jm ε * Y * Jm ε) = Jm ε * NormedSpace.exp Y * Jm ε :=
    Matrix.exp_units_conj (⟨Jm ε, Jm ε, hJ, hJ⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ) Y
  have h3 : (Jm ε).det * (Jm ε).det = 1 := by rw [← det_mul, hJ, det_one]
  have h4 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have h5 := congrArg Matrix.det h4
  rw [← h1, h2, det_mul, det_mul, det_mul, det_one] at h5
  linear_combination h5 - (NormedSpace.exp Y).det * (NormedSpace.exp Y).det * h3

lemma muInt_cast {n : ℕ} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (a : Fin n) :
    (muInt lam a : ℝ) = lam a + Formalism.QuantumDeterminants.rhoStd n a := by
  obtain ⟨m, hm⟩ := hlam.2 a
  have : lam a + Formalism.QuantumDeterminants.rhoStd n a = ((m + n - 1 - (a : ℕ) : ℤ) : ℝ) := by
    unfold Formalism.QuantumDeterminants.rhoStd; push_cast; linarith
  unfold muInt
  rw [this, Int.floor_intCast]

lemma norm_Phi_le {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {X km : Matrix (Fin n) (Fin n) ℂ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h)
    (hX : inP ε X) (hk : km ∈ Kset ε) :
    ‖Phi lam (km⁻¹ * NormedSpace.exp X * km)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := by
  obtain ⟨hpos, hle⟩ := GlobalTheory.MinorDecay.prod_leadMinor_decay n ε lam h X km hlam hgap hX hk
  obtain ⟨hY, -, hexp⟩ := GlobalTheory.MinorDecay.conj_facts hX hk
  have hsq := det_exp_sq hY
  rw [← hexp] at hsq
  have hs0 : 0 ≤ hs X := by unfold hs; positivity
  unfold decHS rkR
  rw [Real.sq_sqrt hs0]
  refine le_trans (le_of_eq ?_) hle
  set z := km⁻¹ * NormedSpace.exp X * km with hz
  have hn : ∀ l hl, ‖leadMinor z l hl‖ = (leadMinor z l hl).re := fun l hl => by
    rw [← Complex.abs_re_eq_norm.2 (hpos l hl).2, abs_of_pos (hpos l hl).1]
  unfold Phi
  rw [norm_prod]
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_castSucc]
    have hdet : leadMinor z ((Fin.last m).val + 1) (Fin.last m).isLt = z.det := rfl
    have hone : ‖z.det‖ = 1 := by
      have h1 := congrArg norm hsq
      rw [norm_mul, norm_one] at h1
      nlinarith [norm_nonneg z.det]
    rw [norm_zpow, hdet, hone, _root_.one_zpow, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_zpow, hn, ← Real.rpow_intCast]
    congr 1
    have hi : (Fin.castSucc i).val + 1 < m + 1 := by simp
    unfold sInt
    rw [dite_eq_left hi]
    push_cast
    rw [muInt_cast hlam, muInt_cast hlam]
    unfold Formalism.QuantumDeterminants.rhoStd
    simp only [Fin.val_castSucc]
    push_cast
    have : lam (Fin.castSucc i) = lam ⟨i.val, by omega⟩ := rfl
    rw [this]
    ring

lemma weighted_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (d : ℕ) (φ a b : α → ℂ)
    (M U V : ℝ) (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : ∀ x, ‖φ x‖ ≤ M)
    (i1 : Integrable (fun x => ‖a x‖ ^ 2) μ) (i2 : Integrable (fun x => ‖b x‖ ^ 2) μ)
    (ha : (d : ℝ) * ∫ x, ‖a x‖ ^ 2 ∂μ = V ^ 2) (hb : (d : ℝ) * ∫ x, ‖b x‖ ^ 2 ∂μ = U ^ 2) :
    ‖(d : ℂ) * ∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * U * V := by
  have key : ∀ t : ℝ, 0 < t →
      ‖(d : ℂ) * ∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * (t / 2) * V ^ 2 + M * (1 / (2 * t)) * U ^ 2 := by
    intro t ht
    have hbd := norm_integral_le_of_norm_le (μ := μ) (f := fun x => φ x * (a x * b x))
      (g := fun x => M * (t / 2) * ‖a x‖ ^ 2 + M * (1 / (2 * t)) * ‖b x‖ ^ 2)
      ((i1.const_mul _).add (i2.const_mul _)) (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, norm_mul]
        have hab : ‖a x‖ * ‖b x‖ ≤ t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2 := by
          have : t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2 - ‖a x‖ * ‖b x‖ =
              (t * ‖a x‖ - ‖b x‖) ^ 2 / (2 * t) := by
            field_simp; ring
          have h2 : 0 ≤ (t * ‖a x‖ - ‖b x‖) ^ 2 / (2 * t) := by positivity
          linarith
        calc _ ≤ M * (t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2) :=
              mul_le_mul (hφ x) hab (by positivity) hM
          _ = _ := by ring)
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul] at hbd
    rw [norm_mul, Complex.norm_natCast]
    refine (mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg d)).trans (le_of_eq ?_)
    rw [mul_add, mul_left_comm, ha, mul_left_comm (d : ℝ), hb]
  refine le_of_forall_pos_le_add fun e he => ?_
  obtain ⟨δ, hδ, hδe⟩ : ∃ δ : ℝ, 0 < δ ∧ M * (U + V) * δ ≤ e :=
    ⟨e / (M * (U + V) + 1), by positivity, by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith⟩
  refine (key ((U + δ) / (V + δ)) (by positivity)).trans ?_
  have h1 : (U + δ) / (V + δ) / 2 * V ^ 2 ≤ (U + δ) * V / 2 := by
    rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (U + δ) * V * δ := by positivity
    nlinarith
  have h2 : 1 / (2 * ((U + δ) / (V + δ))) * U ^ 2 ≤ (V + δ) * U / 2 := by
    have : 1 / (2 * ((U + δ) / (V + δ))) * U ^ 2 = (V + δ) * U ^ 2 / (2 * (U + δ)) := by
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (V + δ) * U * δ := by positivity
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hM
  have h4 : 0 ≤ M * (U + V) * δ := by positivity
  nlinarith

section Tau

variable {n : ℕ} {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

lemma isURepOn_of_isTau (h : IsTau ε abelian₂ τ w) : IsURepOn (Kset ε) τ := by
  obtain ⟨hW, hrep, hdiff, hadj, -⟩ := h
  refine ⟨⟨hrep.1, fun a ha b hb => hrep.2 a (K_KC ha) b (K_KC hb)⟩, fun g hg v => ?_, fun v => ?_⟩
  · have h1 := hadj g (K_KC hg) v (τ g v)
    have h2 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 gᴴ (K_KC (Kset_star ε hg)) g (K_KC hg), h2, hrep.1,
      ContinuousLinearMap.one_apply] at h1
    rw [@norm_eq_sqrt_re_inner ℂ, h1, ← @norm_eq_sqrt_re_inner ℂ]
  · let b := stdOrthonormalBasis ℂ W
    have e : (fun k => τ k v) = fun k => ∑ i, ⟪b i, τ k v⟫_ℂ • b i :=
      funext fun k => (b.sum_repr' _).symm
    rw [e]
    refine continuousOn_finsetSum _ fun i _ => ContinuousOn.smul ?_ continuousOn_const
    exact (hdiff (b i) v).continuousOn.mono fun k hk => K_KC hk

lemma schur_norm (h : IsTau ε abelian₂ τ w) (x : W) :
    (Module.finrank ℂ W : ℝ) * ∫ k : KG ε, ‖⟪x, τ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) = ‖x‖ ^ 2 := by
  have hU := isURepOn_of_isTau h
  obtain ⟨hW, -, -, -, hirr, hw, -⟩ := h
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  obtain ⟨c, -, hc⟩ := avgSchur n ε W τ w hW hU hirr (by rintro rfl; simp at hw)
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) :=
    (hU.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have hc' : ∀ y : W, ∫ k : KG ε, ⟪τ (toMK k) w, y⟫_ℂ * ⟪y, τ (toMK k) w⟫_ℂ ∂(muK ε) = c * ⟪y, y⟫_ℂ :=
    fun y => hc y (innerSL ℂ y)
  let b := stdOrthonormalBasis ℂ W
  have hd : (Module.finrank ℂ W : ℂ) * c = 1 := by
    have h2 : ∑ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) =
        (Module.finrank ℂ W : ℂ) * c := by
      simp only [hc', inner_self_eq_norm_sq_to_K, b.orthonormal.1]
      simp
    rw [← h2, ← MeasureTheory.integral_finsetSum _ fun i _ =>
      ((h1.inner continuous_const).mul (continuous_const.inner h1)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)]
    have h3 : ∀ k : KG ε, ‖τ (toMK k) w‖ = 1 := fun k => (hU.2.1 _ k.2 w).trans hw
    simp only [b.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K, h3]
    simp
  have e : ∀ k : KG ε, ⟪τ (toMK k) w, x⟫_ℂ * ⟪x, τ (toMK k) w⟫_ℂ =
      ((‖⟪x, τ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [← inner_conj_symm (τ (toMK k) w) x, Complex.conj_mul']; simp
  have h4 := hc' x
  simp only [e, integral_complex_ofReal] at h4
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, h4, Complex.ofReal_natCast, ← mul_assoc, hd, one_mul, Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x

lemma ps_entry (h : IsTau ε abelian₂ τ w) (lam : Fin n → ℝ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    (u y : W) :
    ⟪y, ps ε lam τ w x u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * x * toMK k) *
      (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  haveI := h.1
  haveI := FiniteDimensional.complete ℂ W
  have hk := toMK_cont ε
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) :=
    ((isURepOn_of_isTau h).2.2 w).comp_continuous hk fun k => k.2
  have h2 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k)) := by
    have e : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k => K_inv k.2
    simp only [e]
    unfold Phi
    refine continuous_finsetProd _ fun i _ => Continuous.zpow₀ ?_ _ fun k => Or.inl ?_
    · unfold leadMinor
      exact (((hk.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hk).matrix_submatrix
        _ _).matrix_det
    · exact ((hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC k.2).1)).submatrix
        (Fin.castLE_injective _)).det_pos.ne'
  have h3 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    h2.smul (((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp
      ((innerSL ℂ).continuous.comp h1)).clm_apply h1)
  have h4 := h3.integrable_of_hasCompactSupport (μ := muK ε) (HasCompactSupport.of_compactSpace _)
  unfold ps
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply h4,
    ← integral_inner (h4.apply_continuousLinearMap u)]
  congr 2
  funext k
  simp [inner_smul_right, mul_comm]

end Tau

end GlobalTheory.PsiBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetDetNormPos
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.MeanDual

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def invT (g : MatInf E j) : MatInf E j := fun w a b => (Matrix.of (g w))⁻¹ b a

def trDual (Λ : Submodule (𝓞 E) (Fin j → E)) : Submodule (𝓞 E) (Fin j → E) where
  carrier := {y | ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ)}
  add_mem' := by
    intro a b ha hb x hx
    obtain ⟨z, hz⟩ := ha x hx
    obtain ⟨z', hz'⟩ := hb x hx
    exact ⟨z + z', by rw [dotProduct_add, map_add (f := _), hz, hz']; push_cast; ring⟩
  zero_mem' := fun x _ => ⟨0, by simp⟩
  smul_mem' := by
    intro c y hy x hx
    obtain ⟨z, hz⟩ := hy (c • x) (Λ.smul_mem c hx)
    refine ⟨z, ?_⟩
    rw [← hz, dotProduct_smul, smul_dotProduct]

theorem mem_trDual {Λ : Submodule (𝓞 E) (Fin j → E)} {y : Fin j → E} :
    y ∈ trDual E j Λ ↔ ∀ x ∈ Λ, ∃ z : ℤ, Algebra.trace ℚ E (x ⬝ᵥ y) = 2 * (z : ℚ) := Iff.rfl

theorem of_invT (g : MatInf E j) (w : InfinitePlace E) :
    Matrix.of (invT E j g w) = ((Matrix.of (g w))⁻¹)ᵀ := rfl

theorem of_mul (g h : MatInf E j) (w : InfinitePlace E) :
    Matrix.of ((g * h) w) = Matrix.of (g w) * Matrix.of (h w) := rfl

theorem matInf_ext {g h : MatInf E j} (H : ∀ w, Matrix.of (g w) = Matrix.of (h w)) : g = h :=
  funext fun w => Matrix.of.injective (H w)

theorem detNorm_pos_iff (g : MatInf E j) :
    0 < detNorm E j g ↔ ∀ w, (Matrix.of (g w)).det ≠ 0 := by
  unfold detNorm
  constructor
  · intro h w hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp [hw])] at h
    exact lt_irrefl _ h
  · intro h
    exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (h w)) 2

theorem invT_mul (g h : MatInf E j) : invT E j (g * h) = invT E j g * invT E j h := by
  apply matInf_ext
  intro w
  rw [of_invT, of_mul, of_mul, of_invT, of_invT, Matrix.mul_inv_rev, Matrix.transpose_mul]

theorem detNorm_invT_pos_iff (g : MatInf E j) :
    0 < detNorm E j (invT E j g) ↔ 0 < detNorm E j g := by
  simp only [detNorm_pos_iff, of_invT, Matrix.det_transpose, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', ne_eq, inv_eq_zero]

theorem invT_invT {g : MatInf E j} (hg : 0 < detNorm E j g) : invT E j (invT E j g) = g := by
  apply matInf_ext
  intro w
  rw [of_invT, of_invT, ← Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
    Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 ((detNorm_pos_iff E j g).1 hg w))]

theorem detNorm_mul (g h : MatInf E j) : detNorm E j (g * h) = detNorm E j g * detNorm E j h := by
  unfold detNorm
  simp only [of_mul, Matrix.det_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]

theorem continuous_detNorm :
    Continuous (fun g : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j g) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  refine Continuous.pow (Continuous.norm ?_) 2
  exact Continuous.matrix_det (A := fun g : InfinitePlace E → Fin j → Fin j → ℂ => Matrix.of (g w))
    (continuous_apply w)

theorem measurableSet_detNorm_pos : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
  (isOpen_lt continuous_const (continuous_detNorm E j)).measurableSet

end GlobalTheory.MeanDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulLeft
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.HaarLeftInv

def leftMat {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    Matrix (Fin j) (Fin j) ℂ →ₗ[ℝ] Matrix (Fin j) (Fin j) ℂ where
  toFun T := A * T
  map_add' S T := Matrix.mul_add _ _ _
  map_smul' c T := by simp

theorem det_leftMat {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (leftMat A) = (‖A.det‖ ^ 2) ^ j := by
  have h := (GlobalTheory.TwoSidedJac.real_jacobians).1 j j A 1 (leftMat A) (fun T => by
    show A * T = A * T * 1
    rw [Matrix.mul_one])
  rw [h, Matrix.det_one, norm_one, one_pow, mul_one, ← pow_mul]

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def leftMul (a : MatInf E j) :
    (InfinitePlace E → Fin j → Fin j → ℂ) →ₗ[ℝ] (InfinitePlace E → Fin j → Fin j → ℂ) :=
  LinearMap.pi fun w => (show (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) from
    leftMat (Matrix.of (a w))).comp (LinearMap.proj w)

theorem det_leftMul (a : MatInf E j) : LinearMap.det (leftMul E j a) = detNorm E j a ^ j := by
  calc LinearMap.det (leftMul E j a)
      = ∏ w, LinearMap.det (leftMat (Matrix.of (a w))) := LinearMap.det_pi _
    _ = ∏ w, (‖(Matrix.of (a w)).det‖ ^ 2) ^ j := by simp only [det_leftMat]
    _ = (∏ w, ‖(Matrix.of (a w)).det‖ ^ 2) ^ j := Finset.prod_pow _ _ _
    _ = detNorm E j a ^ j := by rfl

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl
  rw [hw, Matrix.det_mul, norm_mul, mul_pow]

theorem continuous_detNorm :
    Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  exact ((Continuous.matrix_det (continuous_apply w)).norm).pow 2

theorem isAddHaar_volume : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  have : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem measurePreserving_mul_left : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (a : MatInf E j), 0 < detNorm E j a → MeasurableEmbedding (fun g : MatInf E j => a * g) ∧ MeasurePreserving (fun g : MatInf E j => a * g) (haarGL E j) (haarGL E j) := by
  intro E _ _ j a ha
  have : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    isAddHaar_volume E j
  have hdet0 : LinearMap.det (leftMul E j a) ≠ 0 := by
    rw [det_leftMul]
    exact pow_ne_zero _ ha.ne'
  have hemb : MeasurableEmbedding ⇑(leftMul E j a) :=
    ((LinearMap.toContinuousLinearMap (leftMul E j a)).toContinuousLinearEquivOfDetNeZero
      hdet0).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpos : 0 < (detNorm E j a)⁻¹ ^ j := pow_pos (inv_pos.mpr ha) j
  have hmap : Measure.map (leftMul E j a) (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) =
      ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, det_leftMul, ← inv_pow,
      abs_of_pos hpos]
  have hc0 : ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hctop : ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρ : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((continuous_detNorm E j).measurable.inv).pow_const j).ennreal_ofReal
  have hρf : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ,
      ENNReal.ofReal ((detNorm E j (leftMul E j a x))⁻¹ ^ j) =
        ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    intro x
    have hx : detNorm E j (leftMul E j a x) = detNorm E j a * detNorm E j x := detNorm_mul E j a x
    rw [hx, mul_inv, mul_pow, ENNReal.ofReal_mul hpos.le]
  have hV : Measure.map (leftMul E j a)
      ((volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
        fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) =
      (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
        fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, withDensity_apply _ (hemb.measurable hs),
      withDensity_apply _ hs]
    calc ∫⁻ x in ⇑(leftMul E j a) ⁻¹' s, ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)
        = (ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j))⁻¹ *
            ∫⁻ x in ⇑(leftMul E j a) ⁻¹' s,
              ENNReal.ofReal ((detNorm E j (leftMul E j a x))⁻¹ ^ j) := by
          simp_rw [hρf]
          rw [lintegral_const_mul' _ _ hctop, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop,
            one_mul]
      _ = (ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j))⁻¹ *
            ∫⁻ y in s, ENNReal.ofReal ((detNorm E j y)⁻¹ ^ j) ∂(Measure.map (leftMul E j a) volume) := by
          rw [setLIntegral_map hs hρ hemb.measurable]
      _ = ∫⁻ y in s, ENNReal.ofReal ((detNorm E j y)⁻¹ ^ j) := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  exact ⟨hemb, hemb.measurable, hV⟩

end GlobalTheory.HaarLeftInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingTriangularShear
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem measurePreserving_layer_shear (d : ℕ) (p : Fin d → Prop) [DecidablePred p]
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, ¬ p i → (∀ k, p k → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i)
      (volume : Measure (Fin d → ℝ)) volume := by
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p with he
  have he_mp : MeasurePreserving e volume volume :=
    volume_preserving_piEquivPiSubtypeProd (fun _ : Fin d => ℝ) p

  let G : (Subtype p → ℝ) → ({i // ¬ p i} → ℝ) := fun a i => f (e.symm (a, 0)) i
  have hG : Measurable G := by
    refine Measurable.of_eval (fun i => ?_)
    exact (measurable_pi_apply (i : Fin d)).comp
      (hf.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const)))

  have hΨ : MeasurePreserving
      (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1))
      (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.skew_product (f := id) (g := fun a b => b + G a)
      (MeasurePreserving.id volume) (measurable_snd.add (hG.comp measurable_fst))
      (Filter.Eventually.of_forall fun a => (measurePreserving_add_right volume (G a)).map_eq)
  have key : (fun (x : Fin d → ℝ) i => if p i then x i else x i + f x i) =
      e.symm ∘ (fun q : (Subtype p → ℝ) × ({i // ¬ p i} → ℝ) => (q.1, q.2 + G q.1)) ∘ e := by
    funext x i
    have hx : ∀ k, p k → x k = e.symm ((e x).1, 0) k := fun k hk => by simp [e, hk]
    by_cases hi : p i
    · simp [e, hi]
    · simp [e, G, hi, h x _ i hi hx]
  rw [key]
  exact (MeasurePreserving.symm e he_mp).comp (hΨ.comp he_mp)

theorem measurePreserving_triangular_shear (d : ℕ) (deg : Fin d → ℕ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (hf : Measurable f)
    (h : ∀ x y i, (∀ k, deg k < deg i → x k = y k) → f x i = f y i) :
    MeasurePreserving (fun x => x + f x) (volume : Measure (Fin d → ℝ)) volume := by

  let U : ℕ → (Fin d → ℝ) → (Fin d → ℝ) := fun n x i => if n ≤ deg i then x i + f x i else x i
  have hS : ∀ n, MeasurePreserving
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) volume volume :=
    fun n => measurePreserving_layer_shear d (fun i => deg i ≠ n) f hf
      (fun x y i hi hxy => h x y i (fun k hk => hxy k (by omega)))
  have hstep : ∀ n, U n =
      (fun (x : Fin d → ℝ) i => if deg i ≠ n then x i else x i + f x i) ∘ U (n + 1) := by
    intro n
    funext x i
    by_cases hin : deg i = n
    · have hfx : f (U (n + 1) x) i = f x i :=
        h _ _ i (fun k hk => by simp only [U]; rw [if_neg (by omega)])
      simp only [Function.comp_apply, hfx]
      simp only [U]
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    · simp only [Function.comp_apply, U]
      rw [if_pos hin]
      by_cases h2 : n ≤ deg i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have hN : ∀ n, Finset.univ.sup deg < n → U n = id := by
    intro n hn
    funext x i
    have hi : deg i ≤ Finset.univ.sup deg := Finset.le_sup (Finset.mem_univ i)
    simp only [U, id]
    rw [if_neg (by omega)]
  have hU : ∀ k n, Finset.univ.sup deg < n + k → MeasurePreserving (U n) volume volume := by
    intro k
    induction k with
    | zero =>
      intro n hn
      rw [hN n (by omega)]
      exact MeasurePreserving.id _
    | succ k ih =>
      intro n hn
      rw [hstep n]
      exact (hS n).comp (ih (n + 1) (by omega))
  have h0 : U 0 = fun x => x + f x := by
    funext x i
    simp [U]
  rw [← h0]
  exact hU (Finset.univ.sup deg + 1) 0 (by omega)

end GlobalTheory
end

