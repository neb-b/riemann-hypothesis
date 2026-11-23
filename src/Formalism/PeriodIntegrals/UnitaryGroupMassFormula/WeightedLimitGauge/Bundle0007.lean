module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Unimod
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.UnimodS
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.MBaseMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle0006

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.BallConj
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim HU

variable {m : ℕ}

def realE (X : Matrix (Fin m) (Fin m) ℂ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  (WithLp.equiv 2 _).symm (realifyFun X)

theorem realE_apply (X : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m × Bool) :
    realE X p = realifyFun X p := rfl

theorem unr_realE (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (realE X) = X := by
  funext i j
  simp only [unrealify, realE_apply, realifyFun]
  simp

theorem realE_unr (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : realE (unrealify x) = x := by
  ext ⟨i, j, b⟩
  rw [realE_apply]
  cases b <;> simp [realifyFun, unrealify]

theorem unr_add (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

theorem unr_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

theorem realE_add (X Y : Matrix (Fin m) (Fin m) ℂ) : realE (X + Y) = realE X + realE Y := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realE_apply, realifyFun]

theorem realE_smul (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : realE ((c : ℂ) • X) = c • realE X := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realE_apply, realifyFun]

def conjL (q : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := realE (q * unrealify x * q⁻¹)
  map_add' x y := by rw [unr_add, Matrix.mul_add, Matrix.add_mul, realE_add]
  map_smul' c x := by
    rw [unr_smul, Matrix.mul_smul, Matrix.smul_mul, realE_smul]; rfl

theorem conjL_apply (q : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    conjL q x = realE (q * unrealify x * q⁻¹) := rfl

theorem norm_realE (X : Matrix (Fin m) (Fin m) ℂ) :
    ‖realE X‖ = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [realE_apply, realifyFun, Real.norm_eq_abs, sq_abs, if_true, Bool.false_eq_true, if_false,
    Complex.normSq_apply]
  ring

theorem frob_trace (X : Matrix (Fin m) (Fin m) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (X i j) : ℝ) : ℂ) = (X * Xᴴ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj]

theorem frob_conj (q X : Matrix (Fin m) (Fin m) ℂ) (hq : qᴴ * q = 1) :
    ∑ i, ∑ j, Complex.normSq ((q * X * q⁻¹) i j) = ∑ i, ∑ j, Complex.normSq (X i j) := by
  have hqi : q⁻¹ = qᴴ := Matrix.inv_eq_left_inv hq
  apply Complex.ofReal_injective
  rw [frob_trace, frob_trace, hqi]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (q * X * qᴴ * (q * (Xᴴ * qᴴ))).trace = (q * (X * (qᴴ * q) * Xᴴ) * qᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (X * Xᴴ * (qᴴ * q)).trace := by
        rw [hq, Matrix.mul_one, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hq, Matrix.one_mul]
    _ = (X * Xᴴ).trace := by rw [hq, Matrix.mul_one]

theorem conj_lieOf {k r : ℕ} (q : Mat k r) (hq : q ∈ UWb k r) (X : Mat k r) (hX : X ∈ lieOf (UWb k r)) :
    q * X * q⁻¹ ∈ lieOf (UWb k r) := by
  intro t
  have hu := uwb_unit hq
  have e : (t : ℂ) • (q * X * q⁻¹) = q * ((t : ℂ) • X) * q⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu)]
  exact uwb_mul (uwb_mul hq (hX t)) (uwb_inv hq)

theorem ballConj : BallConj := by
  intro k r ρ q hq hqu x hx
  have hu := uwb_unit hq
  obtain ⟨v, hv, hvx⟩ := hx

  have hmap : Submodule.map (conjL q) (lieE (UWb k r)) ≤ lieE (UWb k r) := by
    rw [lieE, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨q * X * q⁻¹, conj_lieOf q hq X hX, ?_⟩
    show realE (q * X * q⁻¹) = conjL q (realE X)
    rw [conjL_apply, unr_realE]
  have hmem : conjL q (v : EuclideanSpace ℝ _) ∈ lieE (UWb k r) :=
    hmap ⟨v, v.2, rfl⟩
  refine ⟨⟨conjL q v, hmem⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    show ‖conjL q (v : EuclideanSpace ℝ _)‖ < ρ
    rw [conjL_apply, norm_realE, frob_conj q _ hqu, ← norm_realE, realE_unr]
    exact hv
  · have hx' : (Matrix.of x : Mat k r) * q = NormedSpace.exp (unrealify (v : EuclideanSpace ℝ _)) := by
      have := congrArg (fun f : Mt k r => (Matrix.of f : Mat k r)) hvx
      exact this.symm
    show (fun i j => NormedSpace.exp (unrealify (conjL q (v : EuclideanSpace ℝ _))) i j) =
      q * Matrix.of x
    rw [conjL_apply, unr_realE, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu), ← hx']
    funext i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushC
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def hq (k : ℕ) (T' : ℝ) (y : Fin k → ℂ) (θ : ℝ) : (Fin k → ℂ) × ℂ :=
  (y, (Real.sqrt (∑ i, Complex.normSq (y i) + T') : ℂ) * Complex.exp (θ * Complex.I))

def hqI (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) : ℝ≥0∞ :=
  ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ∫⁻ y, E.indicator 1 (hq k T' y θ)

def HypTh : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → hypM k T' E = c * hqI k T' E

def ConeVol : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → volume (coneSh k T' E) = c * hqI k T' E

theorem coneForm_of (hH : HypTh) (hV : ConeVol) : ConeForm := by
  intro k T' hT'
  obtain ⟨c1, h10, h1t, h1⟩ := hH k T' hT'
  obtain ⟨c2, h20, h2t, h2⟩ := hV k T' hT'
  refine ⟨c1 / c2, ENNReal.div_pos h10 h2t |>.ne', ENNReal.div_ne_top h1t h20, fun E hE => ?_⟩
  rw [h1 E hE, h2 E hE, ← mul_assoc, ENNReal.div_mul_cancel h20 h2t]

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushL
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def wEquiv (k : ℕ) : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun := toW k
  invFun := ofW k
  map_add' p q := by
    funext j
    unfold toW
    by_cases h : j.val < k
    · simp only [dif_pos h, Prod.fst_add, Pi.add_apply]
    · simp only [dif_neg h, Prod.snd_add, Pi.add_apply]
  map_smul' c p := by
    funext j
    unfold toW
    by_cases h : j.val < k
    · simp only [dif_pos h, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg h, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
  left_inv := ofW_toW
  right_inv := toW_ofW

def blkLin (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ((Fin k → ℂ) × ℂ) →ₗ[ℂ] ((Fin k → ℂ) × ℂ) :=
  (((wEquiv k).symm : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] ((Fin k → ℂ) × ℂ)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] ((Fin k → ℂ) × ℂ)) ∘ₗ
    Matrix.toLin' μ ∘ₗ (((wEquiv k).symm.symm : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
      ((Fin k → ℂ) × ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ))

theorem blkLin_apply {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) :
    blkLin k μ p = blkAct k μ p := by
  simp [blkLin, blkAct, wEquiv, Matrix.toLin'_apply]

theorem det_blkLin {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : LinearMap.det (blkLin k μ) = μ.det := by
  unfold blkLin
  rw [LinearMap.det_conj, LinearMap.det_toLin']

theorem normSq_det_hb {k : ℕ} {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) :
    Complex.normSq μ.det = 1 := by
  have h := congrArg Matrix.det hμ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hb : (Hb k).det ≠ 0 := by
    unfold Hb
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by split_ifs <;> norm_num
  have h2 : star μ.det * μ.det = 1 := by
    have e : (star μ.det * μ.det) * (Hb k).det = 1 * (Hb k).det := by
      rw [show (star μ.det * μ.det) * (Hb k).det = star μ.det * (Hb k).det * μ.det by ring, h, one_mul]
    exact mul_right_cancel₀ hb e
  have h3 : (Complex.normSq μ.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3

theorem lebInvB : LebInvB := by
  intro k μ hμ
  have h1 : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  have h2 : (volume : Measure (Fin k → ℂ)).IsAddHaarMeasure := inferInstance
  have h3 : (volume : Measure ((Fin k → ℂ) × ℂ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set f : ((Fin k → ℂ) × ℂ) →ₗ[ℝ] ((Fin k → ℂ) × ℂ) := (blkLin k μ).restrictScalars ℝ with hfdef
  have hdet : LinearMap.det f = 1 := by
    rw [hfdef, LinearMap.det_restrictScalars, det_blkLin, Algebra.norm_complex_apply, normSq_det_hb hμ]
  have hf : blkAct k μ = ⇑f := by
    funext p
    rw [hfdef, LinearMap.coe_restrictScalars, blkLin_apply]
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ((Fin k → ℂ) × ℂ)))
    (by rw [hdet]; norm_num), hdet]
  simp

end PI.RhsWLim.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvF
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ}

section Form

variable {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)

theorem herm_add_left (x y w : Fin n → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  unfold herm
  rw [Matrix.mulVec_add, dotProduct_add]

theorem herm_sub_left (x y w : Fin n → ℂ) : herm H (x - y) w = herm H x w - herm H y w := by
  unfold herm
  rw [Matrix.mulVec_sub, dotProduct_sub]

theorem herm_smul_left (c : ℂ) (x w : Fin n → ℂ) : herm H (c • x) w = c * herm H x w := by
  unfold herm
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem herm_add_right (x w y : Fin n → ℂ) : herm H x (w + y) = herm H x w + herm H x y := by
  unfold herm
  rw [star_add, add_dotProduct]

theorem herm_sub_right (x w y : Fin n → ℂ) : herm H x (w - y) = herm H x w - herm H x y := by
  unfold herm
  rw [star_sub, sub_dotProduct]

theorem herm_smul_right (c : ℂ) (x w : Fin n → ℂ) : herm H x (c • w) = star c * herm H x w := by
  unfold herm
  rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem herm_symm (hH : Hᴴ = H) (x w : Fin n → ℂ) : herm H w x = star (herm H x w) := by
  unfold herm
  conv_lhs => rw [Matrix.star_dotProduct]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]

theorem herm_conj (g : Matrix (Fin n) (Fin n) ℂ) (x w : Fin n → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ w) = herm (gᴴ * H * g) x w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem herm_single (i j : Fin n) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by
  unfold herm
  rw [Matrix.mulVec_single_one]
  simp [dotProduct, Pi.single_apply]

theorem unit_of_form (g : Matrix (Fin n) (Fin n) ℂ) (h : ∀ x w, herm H (g *ᵥ x) (g *ᵥ w) = herm H x w) :
    gᴴ * H * g = H := by
  ext i j
  have e := h (Pi.single j 1) (Pi.single i 1)
  rw [herm_conj, herm_single, herm_single] at e
  exact e

def tmat (κ : ℂ) (d : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + Matrix.of fun i j => κ * d i * (star d ᵥ* H) j

theorem tmat_mulVec (κ : ℂ) (d x : Fin n → ℂ) : tmat H κ d *ᵥ x = x + (κ * herm H x d) • d := by
  ext i
  simp only [tmat, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  unfold herm
  rw [Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

end Form

theorem herm_wb {x w : Fin (2 * r + k + 1) → ℂ} (hx : inWb k r x) (hw : inWb k r w) :
    herm (Hpk k r) x w = herm (Hb k) (wbPart k r x) (wbPart k r w) := by
  conv_lhs => rw [← inWb_eq hx, ← inWb_eq hw]
  unfold herm
  rw [Matrix.mulVec_mulVec, MB.Hpk_Em, ← Matrix.mulVec_mulVec, em_dot]

theorem herm_hb (x w : Fin (k + 1) → ℂ) :
    herm (Hb k) x w = (∑ j : Fin k, star (w (Fin.castSucc j)) * x (Fin.castSucc j)) - star (w (Fin.last k)) * x (Fin.last k) := by
  unfold herm Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply]
  simp only [Fin.castSucc_ne_last, if_false, one_mul, if_true, neg_one_mul, mul_neg]
  ring

theorem herm_self_hb (x : Fin (k + 1) → ℂ) :
    herm (Hb k) x x = ((∑ j : Fin k, Complex.normSq (x (Fin.castSucc j)) - Complex.normSq (x (Fin.last k)) : ℝ) : ℂ) := by
  rw [herm_hb]
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self]
  rfl

theorem wb_posdef {z d : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hd : inWb k r d)
    (hdz : herm (Hpk k r) d z = 0) (hdd : herm (Hpk k r) d d = 0) : d = 0 := by
  rw [herm_wb hd hz, herm_hb] at hdz
  rw [herm_wb hd hd, herm_self_hb] at hdd
  have hT' : 0 < Complex.normSq (wbPart k r z (Fin.last k)) -
      ∑ j : Fin k, Complex.normSq (wbPart k r z (Fin.castSucc j)) := by
    unfold Tz at hT
    rw [herm_wb hz hz, herm_self_hb, Complex.ofReal_re] at hT
    linarith
  set X : Fin k → ℂ := fun j => wbPart k r d (Fin.castSucc j)
  set Z : Fin k → ℂ := fun j => wbPart k r z (Fin.castSucc j)
  set xk := wbPart k r d (Fin.last k)
  set zk := wbPart k r z (Fin.last k)
  have hX : ∑ j, Complex.normSq (X j) = Complex.normSq xk := by
    have := Complex.ofReal_injective (hdd.trans Complex.ofReal_zero.symm)
    linarith
  have hdz' : star zk * xk = ∑ j, star (Z j) * X j := by
    rw [sub_eq_zero] at hdz
    exact hdz.symm
  have hxk : xk = 0 := by
    by_contra hne
    have h1 : ‖zk‖ * ‖xk‖ ≤ ∑ j, ‖Z j‖ * ‖X j‖ := by
      calc ‖zk‖ * ‖xk‖ = ‖star zk * xk‖ := by rw [norm_mul, norm_star]
        _ = ‖∑ j, star (Z j) * X j‖ := by rw [hdz']
        _ ≤ ∑ j, ‖star (Z j) * X j‖ := norm_sum_le _ _
        _ = ∑ j, ‖Z j‖ * ‖X j‖ := by simp only [norm_mul, norm_star]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖Z j‖) (fun j => ‖X j‖)
    have h3 : (‖zk‖ * ‖xk‖) ^ 2 ≤ (∑ j, ‖Z j‖ ^ 2) * (∑ j, ‖X j‖ ^ 2) :=
      (pow_le_pow_left₀ (by positivity) h1 2).trans h2
    simp only [← Complex.normSq_eq_norm_sq] at h3
    rw [hX, mul_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h3
    have hpos : 0 < Complex.normSq xk := Complex.normSq_pos.2 hne
    nlinarith
  have hX0 : ∀ j, X j = 0 := by
    intro j
    rw [hxk, map_zero] at hX
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (X j))).1 hX j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  have hb : wbPart k r d = 0 := by
    ext m
    induction m using Fin.lastCases with
    | last => exact hxk
    | cast j => exact hX0 j
  rw [← inWb_eq hd, hb, Matrix.mulVec_zero]

theorem herm_e_wb {d : Fin (2 * r + k + 1) → ℂ} (hd : inWb k r d) {j : Fin (2 * r + k + 1)}
    (hj : j.val < r ∨ r + k < j.val) : herm (Hpk k r) (bvec j) d = 0 := by
  unfold herm bvec
  rw [Matrix.mulVec_single_one]
  refine Finset.sum_eq_zero fun i _ => ?_
  show star (d i) * Hpk k r i j = 0
  rw [HU.hpk_row]
  split_ifs with h
  · by_cases hi : i.val < r ∨ r + k < i.val
    · rw [hd i hi, star_zero, zero_mul]
    · exfalso
      rw [Fin.ext_iff] at h
      unfold HU.tau at h
      simp only [hi, if_false] at h
      omega
  · exact mul_zero _

theorem uwset_one (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat k r) ∈ UWset k r z :=
  ⟨HU.uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

theorem fibTrans : FibTrans := by
  intro k r z v v' hz hv hv' hT h1 h2
  by_cases hvv : v = v'
  · exact ⟨1, uwset_one z, by rw [hvv, Matrix.one_mulVec]⟩
  have hsym := herm_symm (Hpk k r) MB.hpk_herm
  set d := v - v' with hddef
  have hd : inWb k r d := fun i hi => by simp only [hddef, Pi.sub_apply, hv i hi, hv' i hi, sub_zero]
  have hdz : herm (Hpk k r) d z = 0 := by rw [herm_sub_left, h2, sub_self]
  have hN : herm (Hpk k r) d d = herm (Hpk k r) v d + star (herm (Hpk k r) v d) := by
    simp only [hddef, herm_sub_left, herm_sub_right, star_sub]
    rw [← hsym v v, ← hsym v v', ← h1]
    ring
  have hne : herm (Hpk k r) v d ≠ 0 := by
    intro h0
    have : herm (Hpk k r) d d = 0 := by rw [hN, h0, star_zero, add_zero]
    exact hvv (sub_eq_zero.1 (wb_posdef hz hT hd hdz this))
  have hne' : star (herm (Hpk k r) v d) ≠ 0 := star_ne_zero.2 hne
  set κ : ℂ := -(herm (Hpk k r) v d)⁻¹ with hκ
  have hTx := tmat_mulVec (Hpk k r) κ d
  have hfix : ∀ x, herm (Hpk k r) x d = 0 → tmat (Hpk k r) κ d *ᵥ x = x := by
    intro x hx
    rw [hTx, hx, mul_zero, zero_smul, add_zero]
  have hbr : κ + star κ + κ * star κ * herm (Hpk k r) d d = 0 := by
    rw [hN, hκ, star_neg, star_inv₀]
    field_simp
    ring
  have hunit : ∀ x w, herm (Hpk k r) (tmat (Hpk k r) κ d *ᵥ x) (tmat (Hpk k r) κ d *ᵥ w) = herm (Hpk k r) x w := by
    intro x w
    rw [hTx, hTx, herm_add_left, herm_add_right, herm_add_right, herm_smul_left, herm_smul_left,
      herm_smul_right, herm_smul_right, hsym w d, star_mul']
    linear_combination (herm (Hpk k r) x d * star (herm (Hpk k r) w d)) * hbr
  have hzd : herm (Hpk k r) z d = 0 := by rw [hsym d z, hdz, star_zero]
  refine ⟨tmat (Hpk k r) κ d, ⟨unit_of_form _ _ hunit, fun a => ⟨hfix _ (herm_e_wb hd ?_), hfix _ (herm_e_wb hd ?_)⟩,
    hfix z hzd⟩, ?_⟩
  · left
    exact a.isLt
  · right
    show r + k < 2 * r + k - a.val
    omega
  · rw [hTx, hκ, neg_mul, inv_mul_cancel₀ hne, neg_one_smul, hddef]
    abel

end PI.RhsWLim.W.RI
end
end

