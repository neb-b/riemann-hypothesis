module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCactA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCactB
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology Metric Set
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cact

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.LengthGL (isOpen_GLs contDiffOn_inv mem_GLs_val isCompact_G lg_mul_le fderiv_inv_mul
  differentiableAt_inv contDiffOn_lg)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem inv_mem {a : Mat n} (ha : a ∈ GLs n) : a⁻¹ ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at *
  exact inv_ne_zero ha

theorem mul_mem {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : a * b ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero ha hb

theorem isUnit_det {a : Mat n} (ha : a ∈ GLs n) : IsUnit a.det := isUnit_iff_ne_zero.2 ha

def mulR (z : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => w * z, map_add' := fun a b => Matrix.add_mul a b z,
      map_smul' := fun c a => Matrix.smul_mul c a z }

def mulL (x : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => x * w, map_add' := fun a b => Matrix.mul_add x a b,
      map_smul' := fun c a => Matrix.mul_smul x c a }

theorem cdo_mul {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X} {A B : X → Mat n}
    (hA : ContDiffOn ℝ ∞ A s) (hB : ContDiffOn ℝ ∞ B s) : ContDiffOn ℝ ∞ (fun x => A x * B x) s := by
  have hAe : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) s := fun i j =>
    (GlobalTheory.CompanionTheory.LengthGL.ent i j).contDiff.comp_contDiffOn hA
  have hBe : ∀ i j, ContDiffOn ℝ ∞ (fun x => B x i j) s := fun i j =>
    (GlobalTheory.CompanionTheory.LengthGL.ent i j).contDiff.comp_contDiffOn hB
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun c _ => (hAe i c).mul (hBe c j)

def Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (k : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (p : Mat n × Mat n) : V :=
  k (p.1⁻¹ * p.2) (f p.2)

theorem contDiffOn_Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    {f : Mat n → V} (hk : ContDiffOn ℝ ∞ k (GLs n)) (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Psi k f) (GLs n ×ˢ GLs n) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) :=
    cdo_mul (contDiffOn_inv.comp contDiffOn_fst fun p hp => hp.1) contDiffOn_snd
  have h2 : MapsTo (fun p : Mat n × Mat n => p.1⁻¹ * p.2) (GLs n ×ˢ GLs n) (GLs n) :=
    fun p hp => mul_mem (inv_mem hp.1) hp.2
  have h3 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => k (p.1⁻¹ * p.2)) (GLs n ×ˢ GLs n) := hk.comp h1 h2
  have h4 : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => f p.2) (GLs n ×ˢ GLs n) :=
    hf.comp contDiffOn_snd fun (p : Mat n × Mat n) (hp : p ∈ GLs n ×ˢ GLs n) => hp.2
  have h3' : ContDiffOn ℝ ∞ (fun p : Mat n × Mat n => (k (p.1⁻¹ * p.2)).restrictScalars ℝ) (GLs n ×ˢ GLs n) :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.comp_contDiffOn h3
  exact h3'.clm_apply h4

theorem locSupp_Psi {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    (f : Mat n → V) (hkc : Cpt k) : LocSupp (GLs n) (fun y : G n => y.val) (Psi k f) := by
  obtain ⟨R, hR⟩ := hkc
  intro x₀ hx₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 isOpen_GLs x₀ hx₀
  have hcb : closedBall x₀ (r / 2) ⊆ GLs n := (closedBall_subset_ball (by linarith)).trans hrU
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℝ (Mat n)
  obtain ⟨M, hM⟩ := (isCompact_closedBall x₀ (r / 2)).exists_bound_of_continuousOn
    (contDiffOn_lg.continuousOn.mono hcb)
  refine ⟨ball x₀ (r / 2), isOpen_ball, mem_ball_self (by linarith), ball_subset_closedBall.trans hcb,
    {y : G n | lg y.val ≤ R + M}, isCompact_G _, fun x hx y hy => ?_⟩
  have hxG : x ∈ GLs n := hcb (ball_subset_closedBall hx)
  have hlx : lg x ≤ M := (le_abs_self _).trans (by simpa using hM x (ball_subset_closedBall hx))
  have hy' : R + M < lg y.val := lt_of_not_ge hy
  have hsub : lg y.val ≤ lg x + lg (x⁻¹ * y.val) := by
    have := lg_mul_le x (x⁻¹ * y.val)
    rwa [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det hxG)] at this
  have hz : k (x⁻¹ * y.val) = 0 := hR _ (mul_mem (inv_mem hxG) (mem_GLs_val y)) (by linarith)
  simp [Psi, hz]

section Int

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem act_eq_Psi (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (f : Mat n → E.V) {x : Mat n} (hx : x ∈ GLs n) :
    act μ E k f x = ∫ y : G n, Psi k f (x, y.val) ∂μ := by
  let u : G n := Matrix.nonsingInvUnit x (isUnit_det hx)
  have hu : (u : Mat n) = x := rfl
  rw [← integral_mul_left_eq_self (fun y : G n => Psi k f (x, y.val)) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Psi, Units.val_mul, hu, Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det hx)]

theorem hasFDerivAt_Psi_slice {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {k : Mat n → (V →L[ℂ] V)}
    (f : Mat n → V) (hk : ContDiffOn ℝ ∞ k (GLs n)) {x z : Mat n} (hx : x ∈ GLs n) (hz : z ∈ GLs n) :
    HasFDerivAt (fun x' => Psi k f (x', z))
      (((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ).comp
        ((fderiv ℝ k (x⁻¹ * z)).comp ((mulR z).comp (fderiv ℝ (fun y : Mat n => y⁻¹) x)))) x := by
  have hg : HasFDerivAt (fun x' : Mat n => x'⁻¹ * z) ((mulR z).comp (fderiv ℝ (fun y : Mat n => y⁻¹) x)) x :=
    (mulR z).hasFDerivAt.comp x (differentiableAt_inv hx).hasFDerivAt
  have hk' : HasFDerivAt k (fderiv ℝ k (x⁻¹ * z)) (x⁻¹ * z) :=
    ((hk.differentiableOn (by simp)).differentiableAt
      (isOpen_GLs.mem_nhds (mul_mem (inv_mem hx) hz))).hasFDerivAt
  have hev : HasFDerivAt (fun L : V →L[ℂ] V => L (f z)) ((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ)
      (k (x⁻¹ * z)) :=
    ((ContinuousLinearMap.apply ℂ V (f z)).restrictScalars ℝ).hasFDerivAt
  exact hev.comp x (hk'.comp x hg)

theorem pd_Psi_apply (E : KMod n) {k : Mat n → (E.V →L[ℂ] E.V)} (f : Mat n → E.V) (hk : ContDiffOn ℝ ∞ k (GLs n))
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {x z : Mat n} (hx : x ∈ GLs n) (hz : z ∈ GLs n) (X : Mat n) :
    pd (Psi k f) (x, z) (x * X) = Ld X k (x⁻¹ * z) (f z) := by
  have h1 := hasFDerivAt_pd isOpen_GLs isOpen_GLs (contDiffOn_Psi hk hf) hx hz
  have key : pd (Psi k f) (x, z) (x * X) =
      (fderiv ℝ k (x⁻¹ * z) (mulR z (fderiv ℝ (fun y : Mat n => y⁻¹) x (x * X)))) (f z) := by
    rw [h1.unique (hasFDerivAt_Psi_slice f hk hx hz)]
    rfl
  rw [key, fderiv_inv_mul hx X]
  have : mulR z (-(X * x⁻¹)) = -(X * (x⁻¹ * z)) := by
    show -(X * x⁻¹) * z = -(X * (x⁻¹ * z))
    rw [neg_mul, Matrix.mul_assoc]
  rw [this, map_neg]
  rfl

theorem actDer : ActDer := by
  intro _hU n _ _ μ _ E k f hk hkc hf
  have hΦ := contDiffOn_Psi hk hf
  have hS := locSupp_Psi f hkc
  have hιc : Continuous fun y : G n => y.val := Units.continuous_val
  have hι : ∀ y : G n, (fun y : G n => y.val) y ∈ GLs n := mem_GLs_val
  have hI := contDiffOn_int μ isOpen_GLs isOpen_GLs hιc hι hΦ hS
  refine ⟨hI.congr fun x hx => act_eq_Psi μ E k f hx, fun X x hx => ?_⟩
  have heq : act μ E k f =ᶠ[𝓝 x] fun x => ∫ y : G n, Psi k f (x, y.val) ∂μ :=
    eventually_of_mem (isOpen_GLs.mem_nhds hx) fun x' hx' => act_eq_Psi μ E k f hx'
  have hD : HasFDerivAt (fun x => ∫ y : G n, Psi k f (x, y.val) ∂μ)
      (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) x := hasFDerivAt_int μ isOpen_GLs isOpen_GLs hιc hι hΦ hS hx
  have hint : Integrable (fun y : G n => pd (Psi k f) (x, y.val)) μ :=
    integrable_pd μ isOpen_GLs isOpen_GLs hιc hι hΦ hS hx
  have hA : HasFDerivAt (act μ E k f) (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) x := hD.congr_of_eventuallyEq heq
  have h1 : Rd X (act μ E k f) x = (∫ y : G n, pd (Psi k f) (x, y.val) ∂μ) (x * X) :=
    congrArg (fun L => L (x * X)) hA.fderiv
  rw [h1, ContinuousLinearMap.integral_apply hint]
  let u : G n := Matrix.nonsingInvUnit x (isUnit_det hx)
  have hu : (u : Mat n) = x := rfl
  rw [← integral_mul_left_eq_self (fun y : G n => pd (Psi k f) (x, y.val) (x * X)) u]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Units.val_mul, hu]
  rw [pd_Psi_apply E f hk hf hx (mul_mem hx (mem_GLs_val y)) X,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det hx)]

end Int

end PositivityTheory.RgBcC.LfSt.ChainPf.Cact
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCdcA
section
noncomputable section

open Matrix Finset

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cdc

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem hb_herm (p : Fin n × Fin n) : (hb p : Mat n).IsHermitian := by
  obtain ⟨a, b⟩ := p
  unfold hb
  split_ifs with h1 h2
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_single]
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single]
    simp [add_comm]
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    simp [star_mul', Complex.conj_I]
    rw [← smul_neg, neg_sub]

theorem hb_apply (p : Fin n × Fin n) (i j : Fin n) : (hb p : Mat n) i j =
    if p.1 = p.2 then (if p.1 = i ∧ p.1 = j then 1 else 0)
    else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) * ((if p.1 = i ∧ p.2 = j then 1 else 0) + (if p.2 = i ∧ p.1 = j then 1 else 0))
    else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) * ((if p.1 = i ∧ p.2 = j then 1 else 0) - (if p.2 = i ∧ p.1 = j then 1 else 0)) := by
  obtain ⟨a, b⟩ := p
  unfold hb
  dsimp only
  by_cases hab : a = b
  · subst hab
    simp only [if_true, Matrix.single_apply]
  · rw [if_neg hab, if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt, if_pos hlt]
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
    · rw [if_neg hlt, if_neg hlt]
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply, smul_eq_mul]

theorem hb_tr (H : Mat n) (p : Fin n × Fin n) : (H * hb p).trace =
    if p.1 = p.2 then H p.1 p.1
    else if p.1 < p.2 then ((Real.sqrt 2)⁻¹ : ℂ) * (H p.2 p.1 + H p.1 p.2)
    else (((Real.sqrt 2)⁻¹ : ℂ) * Complex.I) * (H p.2 p.1 - H p.1 p.2) := by
  obtain ⟨a, b⟩ := p
  unfold hb
  dsimp only
  by_cases hab : a = b
  · subst hab
    simp [Matrix.trace_mul_single]
  · rw [if_neg hab, if_neg hab]
    by_cases hlt : a < b
    · rw [if_pos hlt, if_pos hlt]
      simp [Matrix.mul_add, Matrix.trace_add, Matrix.trace_mul_single]
      ring
    · rw [if_neg hlt, if_neg hlt]
      simp [Matrix.mul_sub, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_mul_single]

theorem key_pair (h : ℂ) (s : ℝ) (hs : s * s = 2) :
    (((((s : ℂ))⁻¹ * (star h + h)).re : ℝ) : ℂ) * ((s : ℂ))⁻¹ +
      (((((s : ℂ))⁻¹ * Complex.I * (h - star h)).re : ℝ) : ℂ) * (-((s : ℂ))⁻¹ * Complex.I) = h := by
  rw [← Complex.ofReal_inv]
  have hc2 : s⁻¹ * s⁻¹ = 1 / 2 := by rw [← mul_inv, hs]; norm_num
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.re) * hc2
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.im) * hc2

theorem key_pair2 (h : ℂ) (s : ℝ) (hs : s * s = 2) :
    (((((s : ℂ))⁻¹ * Complex.I * (star h - h)).re : ℝ) : ℂ) * (((s : ℂ))⁻¹ * Complex.I) +
      (((((s : ℂ))⁻¹ * (h + star h)).re : ℝ) : ℂ) * ((s : ℂ))⁻¹ = h := by
  rw [← Complex.ofReal_inv]
  have hc2 : s⁻¹ * s⁻¹ = 1 / 2 := by rw [← mul_inv, hs]; norm_num
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.re) * hc2
  · simp [Complex.mul_re, Complex.mul_im]
    linear_combination (2 * h.im) * hc2

theorem hb_expand (H : Mat n) (hH : H.IsHermitian) : ∑ p, ((H * hb p).trace.re : ℝ) • (hb p : Mat n) = H := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  have hji : H j i = star (H i j) := (hH.apply j i).symm
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  by_cases hij : i = j
  · subst hij
    have him : (H i i).im = 0 := by
      have := congrArg Complex.im (hH.apply i i)
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    rw [Finset.sum_eq_single (i, i)]
    · rw [hb_tr, hb_apply]
      simp only [if_true, and_self, Complex.real_smul, mul_one]
      apply Complex.ext <;> simp [him]
    · intro p _ hp
      obtain ⟨a, b⟩ := p
      have hne : ¬(a = i ∧ b = i) := fun h => hp (by rw [h.1, h.2])
      have hne' : ¬(b = i ∧ a = i) := fun h => hne ⟨h.2, h.1⟩
      rw [hb_apply]
      dsimp only
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl, if_neg hne, smul_zero]
      · rw [if_neg hab, if_neg hne, if_neg hne']
        split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hne : (i, j) ≠ (j, i) := fun h => hij (Prod.mk.inj h).1
    rw [Finset.sum_eq_add (i, j) (j, i) hne]
    · rw [hb_tr, hb_tr, hb_apply, hb_apply]
      dsimp only
      rw [if_neg hij, if_neg (Ne.symm hij)]
      simp only [hji, Complex.real_smul]
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · rw [if_pos hlt, if_pos hlt, if_neg (not_lt.mpr hlt.le), if_neg (not_lt.mpr hlt.le)]
        simp only [and_self, if_true, hij, Ne.symm hij, false_and, if_false, add_zero, zero_sub, mul_one, mul_neg]
        have := key_pair (H i j) (Real.sqrt 2) hs
        convert this using 1
        ring
      · simp only [hlt, not_lt.mpr hlt.le, if_true, if_false]
        simp only [and_self, if_true, hij, Ne.symm hij, false_and, and_false, if_false, add_zero, zero_add, sub_zero,
          zero_sub, mul_one, mul_neg]
        have := key_pair2 (H i j) (Real.sqrt 2) hs
        convert this using 1
    · intro p _ hp
      obtain ⟨a, b⟩ := p
      have h1 : ¬(a = i ∧ b = j) := fun h => hp.1 (by rw [h.1, h.2])
      have h2 : ¬(b = i ∧ a = j) := fun h => hp.2 (by rw [h.1, h.2])
      rw [hb_apply]
      dsimp only
      by_cases hab : a = b
      · subst hab
        have h3 : ¬(a = i ∧ a = j) := fun h => hij (h.1.symm.trans h.2)
        rw [if_pos rfl, if_neg h3, smul_zero]
      · rw [if_neg hab, if_neg h1, if_neg h2]
        split_ifs <;> simp
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h

theorem unit_mul_star (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 * (k.1)ᴴ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

theorem unit_star_mul (k : Matrix.unitaryGroup (Fin n) ℂ) : (k.1)ᴴ * k.1 = 1 := by
  have := Matrix.mem_unitaryGroup_iff'.mp k.2
  rwa [Matrix.star_eq_conjTranspose] at this

theorem conj_herm (k : Mat n) (H : Mat n) (hH : H.IsHermitian) : (k * H * kᴴ).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

theorem expand_conj (k : Matrix.unitaryGroup (Fin n) ℂ) (H : Mat n) (hH : H.IsHermitian) :
    ∑ p, ((H * (k.1 * hb p * (k.1)ᴴ)).trace.re : ℝ) • (k.1 * hb p * (k.1)ᴴ) = H := by
  have h1 := hb_expand ((k.1)ᴴ * H * k.1) (by
    have := conj_herm (k.1)ᴴ H hH
    rwa [Matrix.conjTranspose_conjTranspose] at this)
  have h2 : ∀ p, ((k.1)ᴴ * H * k.1 * hb p).trace = (H * (k.1 * hb p * (k.1)ᴴ)).trace := by
    intro p
    rw [show (k.1)ᴴ * H * k.1 * hb p = (k.1)ᴴ * (H * k.1 * hb p) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, show H * k.1 * hb p * (k.1)ᴴ = H * (k.1 * hb p * (k.1)ᴴ) by simp only [Matrix.mul_assoc]]
  simp only [h2] at h1
  have h3 := congrArg (fun M => k.1 * M * (k.1)ᴴ) h1
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul] at h3
  rw [h3, ← Matrix.mul_assoc, ← Matrix.mul_assoc, unit_mul_star, Matrix.one_mul, Matrix.mul_assoc, unit_mul_star,
    Matrix.mul_one]

theorem basis_inv {W : Type} [AddCommGroup W] [Module ℝ W] (B : Mat n →ₗ[ℝ] Mat n →ₗ[ℝ] W)
    (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ∑ p, B (k.1 * hb p * (k.1)ᴴ) (k.1 * hb p * (k.1)ᴴ) = ∑ p, B (hb p) (hb p) := by
  set Y : Fin n × Fin n → Mat n := fun p => k.1 * hb p * (k.1)ᴴ with hYdef
  have hY : ∀ p, (Y p).IsHermitian := fun p => conj_herm k.1 (hb p) (hb_herm p)
  calc ∑ p, B (Y p) (Y p) = ∑ p, B (Y p) (∑ q, ((Y p * hb q).trace.re : ℝ) • (hb q : Mat n)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hb_expand _ (hY p)]
    _ = ∑ p, ∑ q, ((Y p * hb q).trace.re : ℝ) • B (Y p) (hb q) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul]
    _ = ∑ q, ∑ p, ((hb q * Y p).trace.re : ℝ) • B (Y p) (hb q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
        rw [Matrix.trace_mul_comm]
    _ = ∑ q, B (∑ p, ((hb q * Y p).trace.re : ℝ) • Y p) (hb q) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ q, B (hb q) (hb q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [expand_conj k (hb q) (hb_herm q)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Cdc
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfCwaveB
section
noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Cwave

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

def pX {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (Φ : ℝ × H → W) : ℝ × H → (H →L[ℝ] W) :=
  fun q => (fderiv ℝ Φ q).comp (ContinuousLinearMap.inr ℝ ℝ H)

def Good {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (O : Set H) (Φ : ℝ × H → W) (T : ℝ) : Prop :=
  ContDiffOn ℝ ∞ Φ (Set.univ ×ˢ O) ∧ ∀ t x, T < |t| → Φ (t, x) = 0

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {O : Set H}

theorem Good.deriv (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) : Good O (pX Φ) T := by
  refine ⟨(h.1.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)).clm_comp contDiffOn_const, fun t x ht => ?_⟩
  have hO' : IsOpen {q : ℝ × H | T < |q.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : Φ =ᶠ[𝓝 (t, x)] fun _ => 0 :=
    Filter.eventuallyEq_of_mem (hO'.mem_nhds ht) fun q hq => h.2 q.1 q.2 hq
  show (fderiv ℝ Φ (t, x)).comp _ = 0
  rw [hev.fderiv_eq]
  simp

theorem Good.cont_line {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H} (hx : x ∈ O) :
    Continuous fun t => Φ (t, x) :=
  h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hx⟩

theorem Good.integrable {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H} (hx : x ∈ O) :
    Integrable (fun t => Φ (t, x)) := by
  refine (h.cont_line hx).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_)
  refine h.2 t x ?_
  by_contra hc
  exact ht (abs_le.1 (not_lt.1 hc))

theorem Good.hasFDerivAt [CompleteSpace W] (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x₀ : H}
    (hx₀ : x₀ ∈ O) : HasFDerivAt (fun x => ∫ t, Φ (t, x)) (∫ t, pX Φ (t, x₀)) x₀ := by
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hO x₀ hx₀
  have hsub : closedBall x₀ (ε / 2) ⊆ O := (closedBall_subset_ball (by linarith)).trans hε
  have hK : IsCompact (Icc (-T) T ×ˢ closedBall x₀ (ε / 2)) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKsub : Icc (-T) T ×ˢ closedBall x₀ (ε / 2) ⊆ Set.univ ×ˢ O := fun q hq => ⟨mem_univ _, hsub hq.2⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((h.deriv hO).1.continuousOn.mono hKsub)
  have hdiff : ∀ t, ∀ x ∈ O, HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x := fun t x hx =>
    ((h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right t x)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => Φ (t, x)) (F' := fun x t => pX Φ (t, x)) (s := closedBall x₀ (ε / 2))
    (bound := (Icc (-T) T).indicator fun _ => C) (closedBall_mem_nhds _ (by linarith)) ?_ (h.integrable hx₀)
    ((h.deriv hO).cont_line hx₀).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [hO.mem_nhds hx₀] with x hx using (h.cont_line hx).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun t x hx => ?_
    by_cases ht : t ∈ Icc (-T) T
    · rw [indicator_of_mem ht]
      exact hC (t, x) ⟨ht, hx⟩
    · rw [indicator_of_notMem ht, (h.deriv hO).2 t x ?_, norm_zero]
      by_contra hc
      exact ht (abs_le.1 (not_lt.1 hc))
  · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  · exact Filter.Eventually.of_forall fun t x hx => hdiff t x (hsub hx)

theorem integral_good_contDiffOn (hO : IsOpen O) (k : ℕ) : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (Φ : ℝ × H → W) (T : ℝ), Good O Φ T → ContDiffOn ℝ k (fun x => ∫ t, Φ (t, x)) O := by
  induction k with
  | zero =>
    intro W _ _ _ Φ T h
    exact contDiffOn_zero.2 fun x hx => (h.hasFDerivAt hO hx).continuousAt.continuousWithinAt
  | succ k ih =>
    intro W _ _ _ Φ T h
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast, contDiffOn_succ_iff_fderiv_of_isOpen hO]
    refine ⟨fun x hx => (h.hasFDerivAt hO hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih (pX Φ) T (h.deriv hO)).congr fun x hx => (h.hasFDerivAt hO hx).fderiv

theorem good_smooth [CompleteSpace W] (hO : IsOpen O) (Φ : ℝ × H → W) (T : ℝ) (h : Good O Φ T) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, Φ (t, x)) O :=
  contDiffOn_infty.2 fun k => integral_good_contDiffOn hO k Φ T h

theorem good_fderiv_apply [CompleteSpace W] (hO : IsOpen O) {Φ : ℝ × H → W} {T : ℝ} (h : Good O Φ T) {x : H}
    (hx : x ∈ O) (v : H) : fderiv ℝ (fun x => ∫ t, Φ (t, x)) x v = ∫ t, fderiv ℝ (fun y => Φ (t, y)) x v := by
  rw [(h.hasFDerivAt hO hx).fderiv, ContinuousLinearMap.integral_apply (((h.deriv hO).integrable hx))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hd : DifferentiableAt ℝ Φ (t, x) :=
    (h.1.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨mem_univ t, hx⟩)).differentiableAt (by simp)
  have e : HasFDerivAt (fun y => Φ (t, y)) (pX Φ (t, x)) x := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  show pX Φ (t, x) v = fderiv ℝ (fun y => Φ (t, y)) x v
  rw [e.fderiv]

end PositivityTheory.RgBcC.LfSt.ChainPf.Cwave
end
end

