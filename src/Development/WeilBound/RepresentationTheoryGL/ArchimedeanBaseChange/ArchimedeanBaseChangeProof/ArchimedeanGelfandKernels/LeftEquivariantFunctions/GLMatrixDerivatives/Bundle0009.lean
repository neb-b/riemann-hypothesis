module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.ChainOfKer
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff

namespace PositivityTheory.RgBcC.LfSt.ChainPf.Ker

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)
open PositivityTheory.RgBcC.LfSt.ChainPf PositivityTheory.RgBcC.LfSt.ChainPf.Eq PositivityTheory.RgBcC.LfSt.ChainPf.Loc
  PositivityTheory.RgBcC.LfSt.ChainPf.DCc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem int_of_cpt (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt f) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem act_one [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V))
    (F : Mat n → E.V) : act μ E k F 1 = ∫ y : G n, k y.val (F y.val) ∂μ := by
  simp only [act, one_mul]

theorem gamma_of_comm (hKZ : KerZero) (hL : LgFacts) {E : KMod n} (Γ : E.V →L[ℂ] E.V)
    (hΓρ : ∀ k, Γ * E.ρ k = E.ρ k * Γ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hkc : ContinuousOn k (GLs n))
    (hke : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (y * k₂.1) = k y * E.ρ k₂)
    (hΓ : ∀ f ∈ CE E, act μ E k (fun x => Γ (f x)) 1 = Γ (act μ E k f 1)) :
    ∀ y ∈ GLs n, Γ * k y = k y * Γ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have hz := hKZ n μ E (fun y => k y * Γ - Γ * k y) ((hkc.clm_comp continuousOn_const).sub
      (continuousOn_const.clm_comp hkc)) (fun y hy k₂ => by
        simp only [hke y hy k₂, mul_assoc, ← hΓρ, sub_mul]) (fun f hf hfc => by
      have hfcont : ContinuousOn f (GLs n) := hf.1.continuousOn
      have i1 := int_of_cpt hL μ (fun y => k y * Γ) f (hkc.clm_comp continuousOn_const) hfcont hfc
      have i2 := int_of_cpt hL μ (fun y => Γ * k y) f (continuousOn_const.clm_comp hkc) hfcont hfc
      simp only [ContinuousLinearMap.sub_apply]
      rw [integral_sub i1 i2]
      have e1 : ∫ y : G n, (k y.val * Γ) (f y.val) ∂μ = act μ E k (fun x => Γ (f x)) 1 := by
        rw [act_one]; rfl
      have e2 : ∫ y : G n, (Γ * k y.val) (f y.val) ∂μ = Γ (act μ E k f 1) := by
        rw [act_one]
        exact ContinuousLinearMap.integral_comp_comm Γ
          (int_of_cpt hL μ k f hkc hfcont hfc)
      rw [e1, e2, hΓ f hf, sub_self])
  intro y hy
  have := hz y hy
  exact (sub_eq_zero.1 this).symm

theorem rd_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Rd X f) (GLs n) :=
  (hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_id.matrix_mul continuous_const).continuousOn

theorem ld_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (X : Mat n) : ContinuousOn (Ld X f) (GLs n) :=
  ((hf.continuousOn_fderiv_of_isOpen (isOpen_GLs n) (by simp)).clm_apply
    (continuous_const.matrix_mul continuous_id).continuousOn).neg

def mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (A : V →L[ℂ] V) : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V) :=
  (ContinuousLinearMap.mul ℂ (V →L[ℂ] V)).flip A

theorem rd_mr {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (k : Mat n → (V →L[ℂ] V))
    (hk : ContDiffOn ℝ ∞ k (GLs n)) (A : V →L[ℂ] V) (X : Mat n) (y : Mat n) (hy : y ∈ GLs n) :
    Rd X (fun y => k y * A) y = Rd X k y * A := by
  have hd : DifferentiableAt ℝ k y := (hk.differentiableOn (by simp)).differentiableAt ((isOpen_GLs n).mem_nhds hy)
  have e : (fun y => k y * A) = ⇑((mr A).restrictScalars ℝ) ∘ k := rfl
  have hd2 := (((mr A).restrictScalars ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  simp only [Rd]
  rw [e]
  exact congrArg (fun L => L (y * X)) hd2

theorem kapL_int (hA : ActDer) (hU : Unimod) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    DC ε Fr (act μ E k f) 1 = ∫ y : G n, kapL ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hD := (hA hU n μ E k f hks hkc hf).2
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have iL : ∀ p, Integrable (fun y : G n => Ld (hb p) k y.val (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f (ld_cont k hks _) hfc' hfc
  have iK : Integrable (fun y : G n => k y.val (f y.val)) μ := int_of_cpt hL μ _ f hks.continuousOn hfc' hfc
  have iP : ∀ p, Integrable (fun y : G n => (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val)))) μ := fun p =>
    ContinuousLinearMap.integrable_comp _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have ek : ∀ y : G n, kapL ε Fr k y.val (f y.val) = ∑ p, (ε (hb p)) (Ld (hb p) k y.val (f y.val) +
      ((fderiv ℝ Fr 1) (hb p)) (k y.val (f y.val))) := by
    intro y
    simp [kapL]
  simp_rw [ek]
  rw [integral_finsetSum _ fun p _ => iP p]
  simp only [DC]
  refine Finset.sum_congr rfl fun p _ => ?_
  have e1 : ∫ a : G n, (ε (hb p)) ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (ε (hb p)) (∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ ((iL p).add (ContinuousLinearMap.integrable_comp _ iK))
  have e2 : ∫ a : G n, ((Ld (hb p) k a.val) (f a.val) + ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val))) ∂μ =
      (∫ a : G n, (Ld (hb p) k a.val) (f a.val) ∂μ) + ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ :=
    integral_add (iL p) (ContinuousLinearMap.integrable_comp _ iK)
  have e3 : ∫ a : G n, ((fderiv ℝ Fr 1) (hb p)) ((k a.val) (f a.val)) ∂μ =
      ((fderiv ℝ Fr 1) (hb p)) (∫ a : G n, (k a.val) (f a.val) ∂μ) :=
    ContinuousLinearMap.integral_comp_comm _ iK
  rw [e1, e2, e3, hD _ 1 h1, act_one]
  simp only [one_mul]

theorem int_of_cptK (hL : LgFacts) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (K : Mat n → (V →L[ℂ] V)) (f : Mat n → V)
    (hK : ContinuousOn K (GLs n)) (hf : ContinuousOn f (GLs n)) (hc : Cpt K) :
    Integrable (fun y : G n => K y.val (f y.val)) μ := by
  refine integrable_cpt hL μ (fun y => K y (f y)) (hK.clm_apply hf) ?_
  obtain ⟨R, hR⟩ := hc
  exact ⟨R, fun y hy h => by simp [hR y hy h]⟩

theorem kapR_int (hI : IBPAct) (hU : Unimod) (hR : RCalc) (hL : LgFacts) {E : KMod n} (Fr : Mat n → (E.V →L[ℂ] E.V))
    (ε : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (k : Mat n → (E.V →L[ℂ] E.V)) (hks : ContDiffOn ℝ ∞ k (GLs n)) (hkc : Cpt k)
    (f : Mat n → E.V) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hfc : Cpt f) :
    act μ E k (DC ε Fr f) 1 = ∫ y : G n, kapR ε Fr k y.val (f y.val) ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hfc' : ContinuousOn f (GLs n) := hf.continuousOn
  have hk' : ∀ p, ContDiffOn ℝ ∞ (fun y => k y * ε (hb p)) (GLs n) := fun p => by
    have e : (fun y => k y * ε (hb p)) = ⇑((mr (ε (hb p))).restrictScalars ℝ) ∘ k := rfl
    rw [e]
    exact ((mr (ε (hb p))).restrictScalars ℝ).contDiff.comp_contDiffOn hks
  have hkc' : ∀ p, Cpt fun y => k y * ε (hb p) := fun p => by
    obtain ⟨R, hR⟩ := hkc
    exact ⟨R, fun y hy h => by simp [hR y hy h]⟩
  have iA : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p)) (Rd (hb p) f y.val)) μ := fun p =>
    int_of_cptK hL μ _ _ ((hk' p).continuousOn) (rd_cont f hf _) (hkc' p)
  have iB : ∀ p, Integrable (fun y : G n => (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((hk' p).continuousOn.clm_comp continuousOn_const) hfc' hfc
  have iC : ∀ p, Integrable (fun y : G n => (Rd (hb p) k y.val * ε (hb p)) (f y.val)) μ := fun p =>
    int_of_cpt hL μ _ f ((rd_cont k hks _).clm_comp continuousOn_const) hfc' hfc
  have eL : ∀ y : G n, k y.val (DC ε Fr f y.val) = ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      simp [DC, map_sum, map_add (f := _)]
  have eR : ∀ y : G n, kapR ε Fr k y.val (f y.val) = ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) := by
    intro y
    simp [kapR]
  rw [act_one]
  simp_rw [eL, eR]
  have sL : ∫ y : G n, ∑ p, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finsetSum _ fun p _ => (iA p).add (iB p)
  have sR : ∫ y : G n, ∑ p, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = ∑ p, ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ :=
    integral_finsetSum _ fun p _ => (iC p).neg.add (iB p)
  rw [sL, sR]
  refine Finset.sum_congr rfl fun p _ => ?_
  have a1 : ∫ y : G n, ((k y.val * ε (hb p)) (Rd (hb p) f y.val) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, (k y.val * ε (hb p)) (Rd (hb p) f y.val) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iA p) (iB p)
  have a2 : ∫ y : G n, (-((Rd (hb p) k y.val * ε (hb p)) (f y.val)) +
      (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val)) ∂μ = (∫ y : G n, -((Rd (hb p) k y.val * ε (hb p)) (f y.val)) ∂μ) +
      ∫ y : G n, (k y.val * ε (hb p) * (fderiv ℝ Fr 1) (hb p)) (f y.val) ∂μ := integral_add (iC p).neg (iB p)
  rw [a1, a2, integral_neg]
  congr 1
  have hibp := hI hU hR n μ E (fun y => k y * ε (hb p)) f (hk' p) (hkc' p) hf (hb p) 1 h1
  simp only [one_mul] at hibp
  rw [hibp]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show (Rd (hb p) (fun y => k y * ε (hb p)) y.val) (f y.val) = (Rd (hb p) k y.val * ε (hb p)) (f y.val)
  rw [rd_mr k hks _ _ _ (mem_GLs_of y)]

end PositivityTheory.RgBcC.LfSt.ChainPf.Ker
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.DetMulConjTNe
section
noncomputable section

open Matrix Finset Filter
open scoped ContDiff Topology

namespace PositivityTheory.RgBcC.LfSt.Kchain.KbDer2

open PositivityTheory.RgBcC PositivityTheory.RgBcC.LfSt PositivityTheory.RgBcC.LfSt.Kchain PositivityTheory.RgBcC.LfSt.Kchain.KbBase
  PositivityTheory.RgBcC.LfSt.Kchain.KbCurve PositivityTheory.RgBcC.LfSt.Kchain.KbFr PositivityTheory.RgBcC.LfSt.Kchain.KbDer
open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem det_mul_conjT_ne {y : Mat n} (hy : y ∈ GLs n) : (y * yᴴ).det ≠ 0 := mul_mem hy (conjT_mem hy)

theorem contDiffAt_wt (c : ℝ) {y : Mat n} (hy : y ∈ GLs n) : ContDiffAt ℝ ∞ (fun y' : Mat n => wt c y') y := by
  unfold wt
  have h1 : ContDiffAt ℝ ∞ (fun y' : Mat n => (y' * y'ᴴ).det) y :=
    contDiff_det.contDiffAt.comp y (contDiffAt_matmul contDiffAt_id contDiff_conjT.contDiffAt)
  exact contDiffAt_const.mul ((h1.pow n).inv (pow_ne_zero _ (det_mul_conjT_ne hy)))

theorem wt_line (c : ℝ) (y : Mat n) {X : Mat n} (hX : X.IsHermitian) (t : ℝ) :
    wt c (y * (1 + t • X)) = (c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ * (((1 + t • X).det ^ (2 * n))⁻¹) := by
  unfold wt
  have e : (y * (1 + t • X)) * (y * (1 + t • X))ᴴ = y * ((1 + t • X) * (1 + t • X)) * yᴴ := by
    rw [Matrix.conjTranspose_mul, conjT_line hX, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  rw [show y.det * ((1 + t • X).det * (1 + t • X).det) * yᴴ.det = (y.det * yᴴ.det) * (1 + t • X).det ^ 2 by ring,
    mul_pow, ← pow_mul, mul_inv, mul_assoc]

section

variable {lam : Fin n → ℤ} {E : KMod n} {Fr : Mat n → (E.V →L[ℂ] E.V)} {ε ι : Mat n →ₗ[ℝ] (E.V →L[ℂ] E.V)}
  {S : ℝ → (E.V →L[ℂ] E.V)} {Γ T : E.V →L[ℂ] E.V}

theorem derTwo_at (h : CxData lam E Fr ε ι S Γ T) {k : Mat n → (E.V →L[ℂ] E.V)} (hk : ContDiffOn ℝ ∞ k (GLs n)) (c : ℝ)
    {d x : Mat n} (hd : d ∈ GLs n) (hx : x ∈ GLs n) {y : Mat n} (hy : y ∈ GLs n) {X : Mat n} (hX : X.IsHermitian) :
    fderiv ℝ (fun y' => wt c y' • Kf Fr k Γ T d x y') y (y * X) =
      wt c y • (Fr x * (((-(2 * n : ℂ)) * X.trace) • k (x⁻¹ * d * yᴴ⁻¹) * Γ * T -
        Rd X k (x⁻¹ * d * yᴴ⁻¹) * Γ * T - k (x⁻¹ * d * yᴴ⁻¹) * Γ * T * fderiv ℝ Fr 1 X) * Fr y⁻¹) := by
  set w := x⁻¹ * d * yᴴ⁻¹ with hwdef
  have hw : w ∈ GLs n := mul_mem (mul_mem (inv_mem hx) hd) (inv_mem (conjT_mem hy))
  have hkw : DifferentiableAt ℝ k w := diffAt_of hk hw
  have hg : ContDiffAt ℝ ∞ (fun y' : Mat n => x⁻¹ * d * y'ᴴ⁻¹) y :=
    contDiffAt_matmul contDiffAt_const ((contDiffAt_inv (conjT_mem hy)).comp y contDiff_conjT.contDiffAt)
  have hdiff : DifferentiableAt ℝ (fun y' => wt c y' • Kf Fr k Γ T d x y') y := by
    unfold Kf
    have h1 : DifferentiableAt ℝ (fun y' : Mat n => k (x⁻¹ * d * y'ᴴ⁻¹)) y :=
      hkw.comp y (hg.differentiableAt (by simp))
    have h2 : DifferentiableAt ℝ (fun y' : Mat n => Fr y'⁻¹) y :=
      (diffAt_of h.smooth (inv_mem hy)).comp y ((contDiffAt_inv hy).differentiableAt (by simp))
    exact ((contDiffAt_wt c hy).differentiableAt (by simp)).smul
      ((((h1.const_mul (Fr x)).mul_const Γ).mul_const T).mul h2)
  have h1 := hasDerivAt_fderiv_line hdiff (y * X)
  have hq := (hasDerivAt_detLine X).fun_pow (2 * n)
  have hq0 : ((1 + (0 : ℝ) • X).det) ^ (2 * n) ≠ 0 := by simp
  have hW := (hq.fun_inv hq0).const_mul ((c : ℂ) * ((y * yᴴ).det ^ n)⁻¹)
  have hc : HasDerivAt (fun t : ℝ => w * (1 + t • X)⁻¹) (w * (-X)) 0 :=
    (hasDerivAt_matmul (hasDerivAt_const (0 : ℝ) w) (hasDerivAt_lineInv X)).congr_deriv (by simp)
  have hK : HasDerivAt (fun t : ℝ => k (w * (1 + t • X)⁻¹)) (fderiv ℝ k w (w * (-X))) 0 :=
    hkw.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hP : HasDerivAt (fun t : ℝ => Fr (1 + t • X)⁻¹) (fderiv ℝ Fr 1 (-X)) 0 :=
    (diffAt_of h.smooth one_mem).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (hasDerivAt_lineInv X) (by simp)
  have hB := (((hK.const_mul (Fr x)).mul_const Γ).mul_const T).fun_mul (hP.mul_const (Fr y⁻¹))
  have h2 := hW.fun_smul hB
  have e : ∀ᶠ t : ℝ in 𝓝 0, wt c (y + t • (y * X)) • Kf Fr k Γ T d x (y + t • (y * X)) =
      ((c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ * (((1 + t • X).det ^ (2 * n))⁻¹)) •
        (Fr x * k (w * (1 + t • X)⁻¹) * Γ * T * (Fr (1 + t • X)⁻¹ * Fr y⁻¹)) := by
    filter_upwards [line_mem X] with t ht
    have e1 : y + t • (y * X) = y * (1 + t • X) := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [e1, wt_line c y hX t]
    congr 1
    unfold Kf
    rw [Matrix.conjTranspose_mul, conjT_line hX, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      h.mul _ (inv_mem ht) _ (inv_mem hy)]
    simp only [hwdef, Matrix.mul_assoc, _root_.mul_assoc]
  have h2' := h2.congr_of_eventuallyEq e
  rw [h1.unique h2']
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul, h.one, _root_.one_mul, Matrix.det_one,
    one_pow, inv_one, _root_.mul_one, map_neg, Matrix.mul_neg, Rd]
  have ew : (c : ℂ) * ((y * yᴴ).det ^ n)⁻¹ = wt c y := rfl
  rw [ew]
  simp only [smul_sub, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_neg, mul_neg, neg_mul, smul_add, mul_add,
    add_mul, _root_.mul_assoc, smul_smul]
  push_cast
  ring_nf
  abel_nf

theorem derTwo : DerTwo := fun _ _ _ _ _ _ _ _ _ h _ hk c _ _ hd hx _ hy _ hX => derTwo_at h hk c hd hx hy hX

end

end PositivityTheory.RgBcC.LfSt.Kchain.KbDer2
end
end

