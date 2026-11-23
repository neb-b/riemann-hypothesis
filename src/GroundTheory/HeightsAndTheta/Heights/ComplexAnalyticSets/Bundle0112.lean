module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0110
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0028

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegFormCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace RegularizedFormComparison

open TubeFormComparison

theorem posSemidef_hessC_logReg_comp {n D : ℕ} (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ) (hs : AnalyticAt ℂ s y) :
    (hessC (logReg u ε ∘ s) y).PosSemidef := by
  set τ : (Fin D → ℂ) → Fin 1 → ℂ := fun z _ => ((√ε : ℝ) : ℂ)⁻¹ * linEval u (s z) with hτ
  have hτa : AnalyticAt ℂ τ y := by
    refine analyticAt_pi_iff.2 fun _ => analyticAt_const.mul ?_
    unfold linEval
    exact Finset.analyticAt_fun_sum (f := fun j z => u j * s z j) _ fun j _ =>
      analyticAt_const.mul (analyticAt_pi_iff.1 hs j)
  have hsq : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hε).ne'
  have he : logReg u ε ∘ s =
      fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ε / 2 := by
    funext z
    have h1 : HilbertSamuel.ProjFS.logPot (τ z) = Real.log (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      show Real.log (1 + euclPot (τ z)) = _
      congr 2
      simp only [euclPot, hτ, Finset.univ_unique, Finset.sum_singleton, norm_mul, norm_inv, mul_pow,
        inv_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ε),
        Real.sq_sqrt hε.le]
      ring
    have h2 : ‖linEval u (s z)‖ ^ 2 + ε = ε * (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      field_simp
      ring
    simp only [Function.comp_apply, logReg]
    rw [h1, h2, Real.log_mul hε.ne' (by positivity)]
    ring
  have hconst : ∀ (F : (Fin D → ℂ) → ℝ) (c : ℝ), hessC (fun z => F z + c) y = hessC F y := by
    intro F c
    have h : fderiv ℝ (fun z => F z + c) = fderiv ℝ F := funext fun z => fderiv_add_const c
    unfold hessC
    rw [h]
  have hL2 : ContDiffAt ℝ 2 (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y) :=
    ((SheetFormComparison.contDiff_logPot 1).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [he, hconst (fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z)),
    ReciprocityTheory.AnForm.M.hessC_const_mul']
  have hcomp : hessC (fun z => HilbertSamuel.ProjFS.logPot (τ z)) y =
      hessC (HilbertSamuel.ProjFS.logPot ∘ τ) y := rfl
  rw [hcomp, ReciprocityTheory.AnForm.A.hessC_comp _ τ y hτa hL2]
  have hP : (hessC (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y)).PosSemidef :=
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ hL2 fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w
  set B := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ := by
    ext a b
    simp [hB]
  rw [← hBJ]
  exact (hP.conjTranspose_mul_mul_same B).smul (Complex.zero_le_real.2 (by norm_num))

theorem maDens_euclPot_nonneg {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hM : (hessC (g ∘ s) y).PosSemidef) :
    0 ≤ maDens (fun k => vecCons g (fun _ : Fin d => euclPot) k ∘ s) y := by
  have hE2 : ∀ _ : Fin d, ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) := fun _ =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hb : ∀ _ : Fin d, (hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef ∧
      (-hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef := fun _ => by
    rw [hessC_euclPot]
    refine ⟨?_, ?_⟩
    · simpa using Matrix.PosSemidef.one.add Matrix.PosSemidef.one
    · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  have key := abs_maDens_cons_le g (fun _ : Fin d => euclPot) s y hs hE2 hb hM
  have h0 := (abs_nonneg _).trans key
  rw [one_pow, mul_one] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

end RegularizedFormComparison


open TubeFormComparison RegularizedFormComparison in
theorem RegFormCompare.proof : RegFormCompare.Statement := by
  intro n d J A φ f _hJ _hdim hA hφ hfc hfs
  set K := zeroSet J ∩ tsupport f with hKdef
  have hK : IsCompact K := hfs.isCompact.inter_left (isClosed_zeroSet J)
  choose U hU hZU hφU using hφ
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound φ K hK U hU
    (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC : 0 ≤ max M 0 * (3 ^ (d + 1) * c ^ d) := by positivity
  refine ⟨max M 0 * (3 ^ (d + 1) * c ^ d), hC, fun u ε hε v w hw hvw y => ?_⟩
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', -, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hMs := posSemidef_hessC_logReg_comp u hε s (A *ᵥ x) hsa
  have hE := maDens_euclPot_nonneg (logReg u ε) s (A *ᵥ x) hsa hMs
  by_cases hxf : x ∈ tsupport f
  · have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
      rw [hsx']
      exact ((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)
    have hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧
        (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef := fun i => by
      rw [hsx']
      exact hb i x ⟨hxZ, hxf⟩
    have key := abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hMs
    have hfx : |f x| ≤ max M 0 := (Real.norm_eq_abs (f x) ▸ hM x).trans (le_max_left _ _)
    have hvx : |v x| ≤ w x := hvw x hxf
    rw [abs_mul, abs_mul]
    calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
        ≤ w x * max M 0 * (3 ^ (d + 1) * c ^ d *
            maDens (fun k => vecCons (logReg u ε) (fun _ => euclPot) k ∘ s) (A *ᵥ x)) := by
          have hwx := hw x
          have hK0 : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d := by positivity
          have h1 : |v x| * |f x| ≤ w x * max M 0 := mul_le_mul hvx hfx (abs_nonneg _) (hw x)
          calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
              ≤ w x * max M 0 * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hwx hM0)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg hC (mul_nonneg (hw x) hE)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceAbsIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets

open scoped ENNReal

noncomputable section

theorem finsum_const_mul_ofReal {α : Type*} (c : ℝ≥0∞) (hc : c ≠ 0) (g : α → ℝ) (hg : ∀ x, 0 ≤ g x) :
    ∑ᶠ x, c * ENNReal.ofReal (g x) = c * ENNReal.ofReal (∑ᶠ x, g x) := by
  have hsupp : (Function.support fun x => c * ENNReal.ofReal (g x)) = Function.support g := by
    ext x
    simp only [Function.mem_support, ne_eq, mul_eq_zero, hc, false_or, ENNReal.ofReal_eq_zero, not_le]
    exact ⟨fun h => h.ne', fun h => lt_of_le_of_ne (hg x) (Ne.symm h)⟩
  by_cases hfin : (Function.support g).Finite
  · rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp [hsupp]),
      ← Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun i _ => hg i]
  · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support (by rwa [hsupp]),
      ENNReal.ofReal_zero, mul_zero]

theorem gramVol_zero_map {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by
  have hw : (Fin.cons (0 : Fin n → ℂ) (fun _ : Fin e => (0 : Fin n → ℂ)) : Fin (e + 1) → Fin n → ℂ) = 0 := by
    ext a i
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  have hM0 : (Matrix.of fun _ _ => (0 : ℂ) : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) = 0 := rfl
  simp [gramVol, hw, hM0, Matrix.det_zero]

theorem lintegral_line_gram_abs {n : ℕ} (e : ℕ) (h : HermNorm n) (w : (Fin n → ℂ) → ℝ)
    (hw : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) (x : Fin n → ℂ) (hx : x ≠ 0) (G : ℝ)
    (hG : 0 ≤ G) :
    ∫⁻ t : ℂ, ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
          (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x))) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * G) =
      ENNReal.ofReal (Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
        (|w x| * ((e.factorial : ℝ) / Real.pi ^ e * G / h.dualNorm x ^ (2 * (e + 1))))) := by
  have hg : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → (fun x => |w x|) (t • x) = (fun x => |w x|) x :=
    fun t x ht => by simp only [hw t x ht]
  have key := integral_line_gram e h (fun x => |w x|) hg x hx G
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  have hinv : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  set ρ := ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ with hρ_def
  have hρ : 0 < ρ := by
    rw [hρ_def, norm_pos_iff]
    intro h0
    apply hx
    rw [← hinv, show (h.matᵀ)⁻¹ *ᵥ x = 0 by simpa using congrArg WithLp.ofLp h0, Matrix.mulVec_zero]
  have hpt : ∀ t : ℂ, h.pointOf (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) = t • x := by
    intro t
    have : (fun i => (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) i) = t • ((h.matᵀ)⁻¹ *ᵥ x) := by
      ext i
      simp
    simp only [HermNorm.pointOf, this, Matrix.mulVec_smul, hinv]
  have hae : (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) =ᵐ[volume]
      fun t => (|w x| * G) * (ball (0 : ℂ) (1 / ρ)).indicator (fun t => ‖t‖ ^ (2 * e)) t := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht
    have hiff : ‖t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)‖ < 1 ↔ ‖t‖ < 1 / ρ := by
      rw [norm_smul, lt_div_iff₀ hρ]
    by_cases hb : ‖t‖ < 1 / ρ
    · rw [indicator_of_mem (mem_ball_zero_iff.2 (hiff.2 hb)),
        indicator_of_mem (mem_ball_zero_iff.2 hb), hpt, hw t x ht]
      ring
    · rw [indicator_of_notMem (fun h => hb (hiff.1 (mem_ball_zero_iff.1 h))),
        indicator_of_notMem (fun h => hb (mem_ball_zero_iff.1 h))]
      ring
  have hint : Integrable (fun t : ℂ => (ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) := by
    refine (((integrable_indicator_iff measurableSet_ball).2 ?_).const_mul (|w x| * G)).congr hae.symm
    exact ((continuous_norm.pow _).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) (1 / ρ))).mono_set ball_subset_closedBall
  have hfun : (fun t : ℂ => ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator
        (fun z => |w (h.pointOf z)|) (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x))) *
        ENNReal.ofReal (‖t‖ ^ (2 * e) * G)) = fun t => ENNReal.ofReal
        ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
          (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ x)) * (‖t‖ ^ (2 * e) * G)) :=
    funext fun t => (ENNReal.ofReal_mul (indicator_nonneg (fun _ _ => abs_nonneg _) _)).symm
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t =>
    mul_nonneg (indicator_nonneg (fun _ _ => abs_nonneg _) _) (by positivity))]
  exact congrArg ENNReal.ofReal key

theorem sheetSum_lintegral_eq {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin (e + 1)) (Fin n) ℂ) (w : (Fin n → ℂ) → ℝ)
    (hw : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) (y : Fin (e + 1) → ℂ) :
    (∑ᶠ x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y, ∫⁻ t : ℂ,
      ENNReal.ofReal ((ball (0 : EuclideanSpace ℂ (Fin n)) 1).indicator (fun z => |w (h.pointOf z)|)
        (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y))) *
      ENNReal.ofReal (‖t‖ ^ (2 * (e + 1)) * gramVol (fun y' =>
        (h.matᵀ)⁻¹ *ᵥ sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x y') y)) =
    ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) *
      ENNReal.ofReal (chartAbsDens (J ⊔ Ideal.span {linForm ℓ - 1}) A w
        (fun _ x => Real.log (h.dualNorm x)) y) := by
  have hc : ENNReal.ofReal (Real.pi ^ (e + 1 + 1) / ((e + 1 + 1).factorial : ℝ)) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  unfold chartAbsDens sheetSum
  rw [finsum_mem_def, finsum_mem_def, ← finsum_const_mul_ofReal _ hc _
    (fun x => indicator_nonneg (fun x _ => by dsimp only; split_ifs; exacts [abs_nonneg _, le_rfl]) x)]
  refine finsum_congr fun x => ?_
  by_cases hx : x ∈ ComplexSets.fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y
  · rw [indicator_of_mem hx, indicator_of_mem hx]
    by_cases hs : ∃ s, IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s
    · have hsT : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x = hs.choose := by
        unfold sheetThrough; rw [dite_eq_left hs]
      obtain ⟨-, -, -, -, hsx, -⟩ := hs.choose_spec
      have hy : hs.choose y = x := by rw [← hx.2]; exact hsx
      have hx0 : x ≠ 0 := by
        rintro rfl
        have hmem := hx.1 (linForm ℓ - 1) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        simp [linForm] at hmem
      have hG := gramVol_nonneg (fun y' => (h.matᵀ)⁻¹ *ᵥ hs.choose y') y
      have hd : 0 ≤ h.dualNorm x ^ (2 * (e + 1 + 1)) :=
        pow_nonneg (by unfold HermNorm.dualNorm; positivity) _
      have hm := maDens_log_dualNorm_sheet h J ℓ A y x hs.choose hx hs.choose_spec
      beta_reduce at hm
      rw [dite_eq_left hs, hsT, hy, lintegral_line_gram_abs (e + 1) h w hw x hx0 _ hG]
      beta_reduce
      rw [hm, abs_mul,
        abs_of_nonneg (div_nonneg (mul_nonneg (by positivity) hG) hd),
        ← ENNReal.ofReal_mul (by positivity)]
    · have hsT : sheetThrough (J ⊔ Ideal.span {linForm ℓ - 1}) A x = 0 := by
        unfold sheetThrough; rw [dite_eq_right hs]
      rw [dite_eq_right hs, hsT]
      simp only [Pi.zero_apply, Matrix.mulVec_zero, gramVol_zero_map, mul_zero, ENNReal.ofReal_zero,
        lintegral_zero]
  · simp [indicator_of_notMem hx]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveJacobian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurveJacobian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) →
      w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
        ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ) (D : MvPolynomial σ ℂ),
          k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
            LinearIndependent ℂ (fun j (i : σ) => eval w (pderiv i (f j))) ∧
            eval w D ≠ 0 ∧ ∀ p ∈ I, D * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMassFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def SliceMassFinite.Statement : Prop :=
  ∀ (n d : ℕ) (h : HermNorm n) (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin d) (Fin n) ℂ),
    I.IsPrime → linForm ℓ - 1 ∈ I → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = d →
    IsFiniteProjection I A →
      Integrable (chartAbsDens I A (fun _ => 1) (fun _ x => Real.log (h.dualNorm x)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUniformiserGradientIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def UniformiserGradientIndependent.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (t : MvPolynomial σ ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
    Irreducible (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) t) →
      ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ), k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
        LinearIndependent ℂ (Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) :
          Fin (k + 1) → σ → ℂ)

end

end GroundTheory.Heights₂.Heights
end

