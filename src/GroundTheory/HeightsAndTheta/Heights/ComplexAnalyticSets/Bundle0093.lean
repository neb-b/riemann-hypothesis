module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0076
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace TubeDeepRankOne

theorem mdisc_vecMulVec {D : ℕ} (u : Fin D → Fin D → ℂ) :
    mdisc (fun k => vecMulVec (u k) (star (u k))) =
      (1 / (D.factorial : ℂ)) * (Complex.normSq (Matrix.of u).det : ℂ) := by
  rw [mdisc_eq_sum_perm]
  congr 1
  have hterm : ∀ σ : Equiv.Perm (Fin D),
      (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j).det =
        (Matrix.of u).det * ((Equiv.Perm.sign σ : ℤ) * ∏ j, star (u (σ j) j)) := by
    intro σ
    have h1 : (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j) =
        Matrix.of fun i j => (fun j => star (u (σ j) j)) j * ((Matrix.of u)ᵀ.submatrix id σ) i j := by
      ext i j
      simp [vecMulVec_apply, mul_comm]
    rw [h1, det_mul_row, det_permute', det_transpose]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hconj : ∑ σ : Equiv.Perm (Fin D), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, star (u (σ j) j) =
      starRingEnd ℂ (Matrix.of u).det := by
    rw [RingHom.map_det, det_apply']
    rfl
  rw [hconj, Complex.mul_conj]

theorem mdisc_cons_sum {d n : ℕ} (A₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (B : Fin n → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    mdisc (Fin.cons A₀ (fun _ => ∑ m, B m) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      ∑ I : Fin d → Fin n,
        mdisc (Fin.cons A₀ (fun i => B (I i)) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
  obtain ⟨L, hL⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin (d + 1) => Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  rw [← hL]
  have h := (L.curryLeft A₀).map_sum (fun (_ : Fin d) m => B m)
  simpa [MultilinearMap.curryLeft_apply] using h

theorem hessC_euclPot_eq_one {N : ℕ} (z : Fin N → ℂ) : hessC (euclPot : (Fin N → ℂ) → ℝ) z = 1 := by
  have h : (euclPot : (Fin N → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
    funext w
    simp [euclPot, Complex.normSq_eq_norm_sq]
  rw [h]
  exact hessC_sum_normSq z

theorem hessC_euclPot_comp {n D : ℕ} (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ)
    (hs : AnalyticAt ℂ s y) :
    hessC (euclPot ∘ s) y = ∑ m, vecMulVec (fun j => jacC s y m j) (star fun j => jacC s y m j) := by
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [hessC_comp _ s y hs hE2, hessC_euclPot_eq_one, Matrix.mul_one]
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]

theorem analyticAt_eval_poly {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    AnalyticAt ℂ (fun z => eval z P) y := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (f := fun z : Fin m → ℂ => z) (z := y)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) i).analyticAt y) P
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

theorem dz_logAbsSq {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0)
    (j : Fin m) :
    dz j (cplx (logAbsSq P)) y = fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P := by
  have hg := analyticAt_eval_poly P y
  have hgd : HasFDerivAt (fun z => eval z P) (fderiv ℂ (fun z => eval z P) y) y :=
    hg.differentiableAt.hasFDerivAt
  have h1 := (hgd.restrictScalars ℝ).norm_sq
  have hne : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  have h2 := h1.log hne
  have hf : fderiv ℝ (logAbsSq P) y = _ := h2.fderiv
  set c := fderiv ℂ (fun z => eval z P) y (Pi.single j 1) with hc
  set p := eval y P with hp
  set w := c * (starRingEnd ℂ) p with hw
  have hI : fderiv ℂ (fun z => eval z P) y (Complex.I • Pi.single j 1) = Complex.I * c := by
    rw [map_smul, smul_eq_mul]
  have hN : Complex.normSq p ≠ 0 := (Complex.normSq_pos.2 hP).ne'
  have e1 : fderiv ℝ (logAbsSq P) y (Pi.single j 1) = 2 * w.re / Complex.normSq p := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [← hc, hw]
    ring
  have e2 : fderiv ℝ (logAbsSq P) y (Complex.I • Pi.single j 1) = -(2 * w.im / Complex.normSq p) := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [hI, hw]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hcp : c / p = w / (Complex.normSq p : ℂ) := by
    rw [← Complex.mul_conj, hw, mul_div_mul_right _ _ ((map_ne_zero _).2 hP)]
  rw [dz_cplx, e1, e2, hcp]
  conv_rhs => rw [← Complex.re_add_im w]
  have hN' : (Complex.normSq p : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp
  ring

theorem hessC_logAbsSq_sq_half {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0) :
    hessC (fun z => logAbsSq P z ^ 2 / 2) y =
      vecMulVec (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (star fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P) := by
  have hg := analyticAt_eval_poly P y
  have hv : ContDiffAt ℝ 2 (logAbsSq P) y := by
    have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) y :=
      ((hg.contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
    exact h1.log (by positivity)
  have hv0 : hessC (logAbsSq P) y = 0 := by
    have h : logAbsSq P = fun z => (2 : ℝ) * Real.log ‖eval z P‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      norm_num
    rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul', hessC_log_norm _ y hg hP, smul_zero]
  rw [MaDensLeibniz.hessC_sq_half _ y hv, hv0, smul_zero, zero_add, gradMat_eq_vecMulVec]
  have ha : (fun j => dz j (cplx (logAbsSq P)) y) =
      fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P :=
    funext fun j => dz_logAbsSq P y hP j
  rw [ha]

theorem fderiv_apply_coord {D m : ℕ} (F : (Fin D → ℂ) → Fin m → ℂ) (y h : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F y) (a : Fin m) :
    fderiv ℂ F y h a = fderiv ℂ (fun x => F x a) y h := by
  have e := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a).hasFDerivAt.comp y
    hF.hasFDerivAt).fderiv
  have e' : (fun x => F x a) = (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a) ∘ F := rfl
  rw [e', e]
  rfl

theorem det_rows_eq_deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ)
    (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (hs : DifferentiableAt ℂ s y)
    (I : Fin d → Fin n) :
    (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
      (eval y P)⁻¹ * deepJacDet P s I y := by
  have hg := (analyticAt_eval_poly P y).differentiableAt
  have hF : DifferentiableAt ℂ (deepMap P s I) y := by
    refine differentiableAt_pi.2 fun k => ?_
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa [deepMap] using hg
    · simpa [deepMap] using differentiableAt_pi.1 hs (I i)
  set J := jacC (deepMap P s I) y with hJdef
  have hJ : (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)) =
      J.updateRow 0 ((eval y P)⁻¹ • J 0) := by
    ext k j
    refine Fin.cases ?_ (fun i => ?_) k
    · have h0 : (fun x => deepMap P s I x 0) = fun z => eval z P := by
        funext x
        simp [deepMap]
      simp only [Matrix.of_apply, Fin.cons_zero, updateRow_self, Pi.smul_apply, smul_eq_mul, hJdef,
        jacC, fderiv_apply_coord _ _ _ hF, h0]
      rw [div_eq_inv_mul]
    · have hi : (fun x => deepMap P s I x i.succ) = fun x => s x (I i) := by
        funext x
        simp [deepMap]
      simp only [Matrix.of_apply, Fin.cons_succ, updateRow_ne (Fin.succ_ne_zero i), hJdef, jacC,
        fderiv_apply_coord _ _ _ hF, hi, fderiv_apply_coord _ _ _ hs]
  rw [hJ, det_updateRow_smul, updateRow_eq_self, hJdef, det_jacC]
  rfl

theorem proof : TubeDeepRankOne.Statement := by
  intro n d A P U s y hU hy hsd hAs hP
  have hsa : AnalyticAt ℂ s y := analyticAt_pi_iff.2 fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood (d + 1) U (fun y => s y j) hU (differentiableOn_pi.1 hsd j) y hy
  set a : Fin (d + 1) → ℂ := fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P with ha
  set b : Fin n → Fin (d + 1) → ℂ := fun m j => jacC s y m j with hb
  have h0 : hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) y = vecMulVec a (star a) := by
    have hev : ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) =ᶠ[𝓝 y] fun z => logAbsSq P z ^ 2 / 2 := by
      filter_upwards [hU.mem_nhds hy] with z hz
      simp only [Function.comp_apply, hAs z hz]
    rw [hessC_congr' hev, hessC_logAbsSq_sq_half P y hP]
  have h1 : hessC (euclPot ∘ s) y = ∑ m, vecMulVec (b m) (star (b m)) := hessC_euclPot_comp s y hsa
  have hH : (fun k => hessC (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y) =
      (Fin.cons (vecMulVec a (star a)) (fun _ => ∑ m, vecMulVec (b m) (star (b m))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using h0
    · simpa using h1
  have hI : ∀ I : Fin d → Fin n,
      (Fin.cons (vecMulVec a (star a)) (fun i => vecMulVec (b (I i)) (star (b (I i)))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      fun k => vecMulVec ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)
        (star ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)) := by
    intro I
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hdet : ∀ I : Fin d → Fin n,
      (Matrix.of (Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
        (eval y P)⁻¹ * deepJacDet P s I y := fun I =>
    det_rows_eq_deepJacDet P s y (hsd.differentiableAt (hU.mem_nhds hy)) I
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH, mdisc_cons_sum]
  simp_rw [hI, mdisc_vecMulVec, hdet]
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hf : ((d + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (d + 1).factorial_ne_zero
  have hre : ((1 / ((d + 1).factorial : ℂ)) *
      (Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) : ℂ)).re =
      Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) / ((d + 1).factorial : ℝ) := by
    rw [show (1 / ((d + 1).factorial : ℂ)) = (((1 / ((d + 1).factorial : ℝ)) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hre, map_mul, map_inv₀, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hp : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  field_simp

end TubeDeepRankOne

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarMassNearSmall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ENNReal NNReal

noncomputable section

namespace VarMassNearSmall

variable {n d : ℕ}

theorem abs_sheetSum_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {F G : (Fin n → ℂ) → ((Fin d → ℂ) → Fin n → ℂ) → ℝ} (hFG : ∀ x s, |F x s| ≤ G x s)
    {y : Fin d → ℂ} (hfin : (fibre J A y).Finite) :
    |sheetSum J A F y| ≤ sheetSum J A G y := by
  classical
  unfold sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs with h
  · exact hFG x _
  · simp

theorem volume_eq_zero_of_hausdorff {S : Set (Fin d → ℂ)} (hS : μH[((2 * d : ℕ) : ℝ)] S = 0) :
    volume S = 0 := by
  let E : ((Σ _ : Fin d, Fin 2) → ℝ) ≃L[ℝ] (Fin d → ℂ) :=
    (Pi.basis (fun _ : Fin d => Complex.basisOneI)).equivFun.symm.toContinuousLinearEquiv
  have hcard : Fintype.card (Σ _ : Fin d, Fin 2) = 2 * d := by
    simp [Fintype.card_sigma, mul_comm]
  have hT : volume (E ⁻¹' S) = 0 := by
    rw [← hausdorffMeasure_pi_real, hcard]
    have h := E.symm.lipschitzWith.hausdorffMeasure_image_le (d := ((2 * d : ℕ) : ℝ)) (by positivity) S
    rw [hS, mul_zero, nonpos_iff_eq_zero, ContinuousLinearEquiv.image_symm_eq_preimage] at h
    exact h
  have : (Measure.map E volume).IsAddHaarMeasure := E.isAddHaarMeasure_map volume
  have hac : (volume : Measure (Fin d → ℂ)) ≪ Measure.map E volume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  apply hac
  exact (E.toHomeomorph.toMeasurableEquiv.map_apply S).trans hT

theorem volume_image_eq_zero (W I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hI : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < d) :
    volume (A.mulVec '' (zeroSet W ∩ zeroSet I)) = 0 := by
  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (W ⊔ I)) < d :=
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective le_sup_right)).trans_lt hI
  have h0 := NullSmaller.proof n d (W ⊔ I) hdim
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin d → ℂ) :=
    (Matrix.mulVecLin A).toContinuousLinearMap.comp (EuclideanSpace.equiv (Fin n) ℂ).toContinuousLinearMap
  have hsub : A.mulVec '' (zeroSet W ∩ zeroSet I) ⊆ L '' zeroSetEuc (W ⊔ I) := by
    rintro _ ⟨x, ⟨hxW, hxI⟩, rfl⟩
    refine ⟨(EuclideanSpace.equiv (Fin n) ℂ).symm x, fun q hq => ?_, by simp only [L, ContinuousLinearMap.comp_apply]; rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    have hx : (fun i => ((EuclideanSpace.equiv (Fin n) ℂ).symm x) i) = x := rfl
    rw [hx, map_add (f := _), hxW a ha, hxI b hb, add_zero]
  refine volume_eq_zero_of_hausdorff (le_antisymm ?_ bot_le)
  calc μH[((2 * d : ℕ) : ℝ)] (A.mulVec '' (zeroSet W ∩ zeroSet I))
      ≤ μH[((2 * d : ℕ) : ℝ)] (L '' zeroSetEuc (W ⊔ I)) := measure_mono hsub
    _ ≤ _ := L.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [h0, mul_zero]

end VarMassNearSmall


open VarMassNearSmall in
theorem VarMassNearSmall.proof (hCMC : ChartMassCompact.Statement) : VarMassNearSmall.Statement := by
  classical
  intro n d W I φ f hW hdim hφ hI hf hfc δ hδ
  by_cases hA : ∃ A : Matrix (Fin d) (Fin n) ℂ, IsFiniteProjection W A
  swap
  · refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun χ _ _ _ => ?_⟩
    unfold varInt
    rw [dite_eq_right hA, abs_zero]
    exact hδ.le
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection W A := hA.choose_spec
  have hvar : ∀ g, varInt W d g φ = ∫ y, chartDens W A g φ y := fun g => by
    unfold varInt chartInt
    rw [dite_eq_left hA]
  have hfin : ∀ y, (fibre W A y).Finite := fun y => (FibreBound.proof n d W A hW hdim hAf y).2.1
  have hS : IsClosed (zeroSet I) := SheetSumMeasurable.isClosed_zeroSet I
  set U : ℕ → Set (Fin n → ℂ) := fun k => Metric.thickening (1 / ((k : ℝ) + 1)) (zeroSet I) with hU
  set F : ℕ → (Fin d → ℂ) → ℝ := fun k => chartAbsDens W A ((U k).indicator fun x => |f x|) φ with hF
  set G := chartAbsDens W A (fun x => |f x|) φ with hG
  have hGi : Integrable G := hCMC n d W A _ φ hW hdim hAf (continuous_abs.comp hf).continuousOn hφ
    (Or.inl (hfc.comp_left abs_zero))
  have hFm : ∀ k, Measurable (F k) := fun k => (SheetSumMeasurable.proof n d W A _ φ hW hdim hAf
    ((continuous_abs.comp hf).measurable.indicator Metric.isOpen_thickening.measurableSet) hφ).2
  have hFG : ∀ k y, ‖F k y‖ ≤ G y := by
    intro k y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    rw [abs_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hx : x ∈ U k
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, abs_zero]
      exact abs_nonneg _
  have hlim : ∀ᵐ y, Tendsto (fun k => F k y) atTop (𝓝 0) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_image_eq_zero W I A hI)] with y hy
    have hx : ∀ x ∈ fibre W A y, ∀ᶠ k in atTop, x ∉ U k := by
      intro x hxf
      have hxS : x ∉ zeroSet I := fun h => hy ⟨x, ⟨hxf.1, h⟩, hxf.2⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl x hxS
      obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
      filter_upwards [eventually_ge_atTop K] with k hk hxU
      obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.1 hxU
      have hKk : (K : ℝ) + 1 ≤ (k : ℝ) + 1 := by
        have : (K : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hle : 1 / ((k : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hKk
      exact hball (show dist z x < ε by rw [dist_comm]; linarith) hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(eventually_all_finite (hfin y)).2 hx] with k hk
    symm
    show sheetSum W A _ y = 0
    unfold sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
    refine Finset.sum_eq_zero fun x hxm => ?_
    rw [Set.Finite.mem_toFinset] at hxm
    split_ifs <;> simp [Set.indicator_of_notMem (hk x hxm)]
  have hT := tendsto_integral_of_dominated_convergence G (fun k => (hFm k).aestronglyMeasurable) hGi
    (fun k => Eventually.of_forall (hFG k)) hlim
  simp only [integral_zero] at hT
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hT).2 δ hδ).exists
  refine ⟨U k, Metric.isOpen_thickening, Metric.self_subset_thickening (by positivity) _,
    fun χ hχ hχ1 hχU => ?_⟩
  have hFi : Integrable (F k) := hGi.mono' (hFm k).aestronglyMeasurable (Eventually.of_forall (hFG k))
  have hpt : ∀ y, ‖chartDens W A (fun x => χ x * f x) φ y‖ ≤ F k y := by
    intro y
    rw [Real.norm_eq_abs]
    refine abs_sheetSum_le W A (fun x s => ?_) (hfin y)
    by_cases hx : x ∈ U k
    · rw [Set.indicator_of_mem hx, abs_mul, abs_mul, abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) (hχ1 x)) (abs_nonneg _)
    · have h0 : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)
      simp only [h0, zero_mul, abs_zero]
      positivity
  have h1 := norm_integral_le_of_norm_le hFi (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs, ← hvar] at h1
  exact h1.trans hk.le

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroDimIsolated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem ZeroDimIsolated.proof : ZeroDimIsolated.Statement := by
  intro n I q hdim
  classical
  have : Ring.KrullDimLE 0 (curveLocalRing I q) := Ring.krullDimLE_iff.2 (by simpa using hdim)
  have hnil : ∀ i : Fin n, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧
      ∃ k : ℕ, s * (X i - C (q i)) ^ k ∈ I := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i - C (q i)) ∈
        Ring.jacobson (curveLocalRing I q) := by
      rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
      intro P hP
      have hP' : Ideal.IsMaximal P := hP
      let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
      have hPm : (Ideal.comap π P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective (H := hP')
      have hL : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
          (X i - C (q i)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q))) := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker (eval q))]
        simp [RingHom.mem_ker]
      rw [← IsLocalRing.eq_maximalIdeal hPm] at hL
      exact hL
    rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero, mem_nilradical] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [← map_pow] at hk
    have hmap : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
        ((X i - C (q i)) ^ k) ∈
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hk
    obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) I _).1 hmap
    exact ⟨m, fun h ↦ hm (RingHom.mem_ker.2 h), k, hmI⟩
  choose s hs k hk using hnil
  refine ⟨{x | eval x (∏ i, s i) ≠ 0}, ?_, ?_⟩
  · apply (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).mem_nhds
    simp [map_prod, Finset.prod_ne_zero_iff, hs]
  · rintro x ⟨hxZ, hxN⟩
    simp only [Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff] at hxN
    rw [Set.mem_singleton_iff]
    funext i
    have h := hxZ _ (hk i)
    simp only [map_mul, map_pow, map_sub, eval_X, eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (hxN i (Finset.mem_univ i))
    · exact sub_eq_zero.1 h

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def BranchInComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (q : Fin n → ℂ) (c : VarBranch I k q),
    ∃ J ∈ I.minimalPrimes, Set.MapsTo c.toFun (Metric.ball 0 c.radius) (zeroSet J)

end

end GroundTheory.Heights₂.Heights
end

