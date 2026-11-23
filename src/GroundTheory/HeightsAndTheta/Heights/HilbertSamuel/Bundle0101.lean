module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0098
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0048
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionInterpIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem locDens_resPot_interp (d : HSMDatum D Ω κ) {m₁ : ConeMetric ℂ (Ix κ)} (hm₁ : IsSmoothMetric m₁)
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => resPot d (interp d.m m₁ t)) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y := by
  let x0 := (d.R.A.chart j).symm y
  let γ : (Fin D → ℂ) → Ix κ → ℂ := fun y' => d.R.lift x0 ((d.R.A.chart j).symm y')
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ γ y' ≠ 0 := by
    filter_upwards [hV.mem_nhds ⟨hy, d.R.mem_U x0⟩] with y' hy'
    exact ⟨differentiableAt_pi.2 fun p => (d.R.holo x0 p j y' hy').differentiableAt,
      gaamix_ne_zero_of_mcPts (d.R.mem x0 _ hy'.2)⟩
  have hL : locDens d.R.A (fun _ => resPot d (interp d.m m₁ t)) j y =
      maDensity (fun k y' => purePot (interp d.m m₁ t) D k (γ y')) y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y =
      maDensity (fun k y' => mixPot d.m m₁ D i k (γ y')) y := by
    intro i
    have e : (fun (k : Fin D) (y' : Fin D → ℂ) =>
        (if k.val < i then resPot d m₁ else resPot d d.m).φ x0 ((d.R.A.chart j).symm y')) =
        fun k y' => mixPot d.m m₁ D i k (γ y') := by
      funext k y'
      by_cases hk : k.val < i
      · simp only [hk, if_true, mixPot]
        rfl
      · simp only [hk, if_false, mixPot]
        rfl
    show ReciprocityTheory.AnForm.maDens _ y = _
    rw [e]
    rfl
  rw [hL, gbamix_maDensity_interp d.smooth hm₁ t hγ]
  exact Finset.sum_congr rfl fun i _ => by rw [hR i]

theorem mInt_resPot_interp (d : HSMDatum D Ω κ) {m₁ : ConeMetric ℂ (Ix κ)} (hm₁ : IsSmoothMetric m₁)
    (t : ℝ) :
    mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) (fun y => logRatio d.m m₁ (resPt d y)) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m)
          (fun y => logRatio d.m m₁ (resPt d y)) := by
  have hg : Continuous (fun y => logRatio d.m m₁ (resPt d y)) :=
    continuous_logRatio_resPt d d.smooth hm₁
  have hΦ : ∀ (i : ℕ) (k : Fin D),
      IsPotential d.R.A (if k.val < i then resPot d m₁ else resPot d d.m) := by
    intro i k
    split_ifs
    · exact isPotential_resPot d hm₁
    · exact isPotential_resPot d d.smooth
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) * logRatio d.m m₁ (resPt d ((d.R.A.chart j).symm y)) *
            locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              logRatio d.m m₁ (resPt d ((d.R.A.chart j).symm y)) *
              locDens d.R.A (fun k : Fin D => if k.val < i then resPot d m₁ else resPot d d.m) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_resPot_interp d hm₁ t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

namespace ResolutionInterpIntegral

theorem proof : ResolutionInterpIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  unfold resMetricInt
  simp only [mInt_resPot_interp d hm₁]
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end ResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSTopPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ScaledFSTopPos

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (a : Fin n → K → ℤ), (∀ j k, 0 ≤ a j k) →
    0 ≤ geoNum n V a
  | 0, V, a, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, a, ha => by
    unfold geoNum
    split_ifs with h
    · exact Finset.sum_nonneg fun k _ => mul_nonneg (ha _ _) (finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W _ fun j k => ha _ _))
    · exact le_rfl

theorem semipos_of_h_eq {P0 P : Ideal (MRing ι)} {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (h : A.h = B.h)
    (hA : IsSemipositiveRel P0 P A) : IsSemipositiveRel P0 P B := by
  unfold IsSemipositiveRel IsSmoothHerm at *
  rw [← h]
  exact hA

theorem semipos (P : Ideal (MRing ι)) : IsSemipositiveRel ⊥ P (scaledFSH ι) := by
  have hM : IsSemipositiveRel ⊥ P (constLine (ι := ι) 0) := by
    refine ⟨G5.isSmoothHerm_constLine 0, fun z _ w _ => ?_⟩
    simp [leviForm, constLine, HermLine.ofWeight]
  have hfs : IsSemipositiveRel ⊥ P (fsH ι) :=
    semipos_of_h_eq (funext fun z => by simp [HermLine.zcomb])
      (PerturbSemipos.proof K ι ⊥ P _ 0 1 hM le_rfl zero_le_one)
  exact semipos_of_h_eq rfl (Mono.semipos_constShift hfs (-1))

theorem logNorm_fsH_nonpos (c : ∀ k, ι k) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    logNorm (fsH ι) (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (fun _ : K => (1 : ℕ)) k) z ≤ 0 := by
  have hpos := (fsH ι).pos z hz
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  unfold logNorm
  apply Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
  rw [div_le_one hpos]
  simpa [map_prod, norm_prod] using hH

theorem step (II : IntersectionSystem) (hII : IsIntersectionSystem II) (hG : FSGeomDegPos.Statement) (n : ℕ)
    (hlow : ∀ W : Ideal (MRing ι), IsArithVar W n → IsHorizontal W → 0 ≤ II K ι W n (fun _ => scaledFSH ι))
    (P : Ideal (MRing ι)) (hP : IsArithVar P (n + 1)) :
    0 < II K ι P (n + 1) (fun _ => scaledFSH ι) := by
  classical
  have hF := hII K ι
  set L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun _ => scaledFSH ι with hLdef
  have hHs : IsSmoothHerm (scaledFSH ι) := (semipos (ι := ι) ⊥).1
  have hFs : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hCs : IsSmoothHerm (constLine (ι := ι) (-1)) := G5.isSmoothHerm_constLine (-1)
  have hLs : ∀ j, IsSmoothHerm (L j) := fun _ => hHs
  have e0 : (fun _ : Fin (n + 1) => scaledFSH ι) = Fin.snoc L ((fsH ι).tensor (constLine (-1))) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [L, scaledFSH]
  rw [e0, hF.2.1 P n L _ _ hP hLs hFs hCs]
  obtain ⟨c, hc⟩ : ∃ c : ∀ k, ι k, ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P :=
    ⟨fun k => (hP.2.1.2.2 k).choose, fun k => (hP.2.1.2.2 k).choose_spec⟩
  have hsH := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_coordMonomial c (fun _ : K => (1 : ℕ))
  have hsP := GroundTheory.Heights₂.Heights.Inter.ThmIUnique.coordMonomial_not_mem hP.2.1.1 c hc (fun _ : K => (1 : ℕ))
  have hfa : ∀ k, (fsH ι).a k = ((fun _ : K => (1 : ℕ)) k : ℤ) := fun k => by simp [fsH, HermLine.ofMetrics]

  have hA : 0 ≤ II K ι P (n + 1) (Fin.snoc L (fsH ι)) := by
    rw [hF.2.2 P n L (fsH ι) _ _ hP hLs hFs hfa hsH hsP, recR_eq]
    refine sub_nonneg.mpr (le_trans ?_ (finsum_nonneg fun W => finsum_nonneg fun hW =>
      mul_nonneg (Nat.cast_nonneg _) ?_))
    · exact IntegralAgainstPositive.proof K ι P ⊥ n L _ bot_le (fun _ => semipos P)
        fun z hz => logNorm_fsH_nonpos c hz.1
    · split_ifs with hh
      · exact hlow W ((divSuppArith K ι P n (fsH ι) _ W hP ⟨_, hfa, hsH, hsP⟩ hW).1 hh) hh
      · exact mul_nonneg (by exact_mod_cast geoNum_nonneg n W _ fun j k => by simp [L, scaledFSH_a])
          (Real.log_natCast_nonneg _)

  have hone : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hca : ∀ k, (constLine (ι := ι) (-1)).a k = ((0 : K → ℕ) k : ℤ) := fun k => by
    simp [constLine, HermLine.ofWeight]
  have hB : II K ι P (n + 1) (Fin.snoc L (constLine (-1))) = ptsIntegral P (pot L) (fun _ => 1) := by
    rw [hF.2.2 P n L _ 1 0 hP hLs hCs hca GroundTheory.Heights₂.Heights.Inter.ThmIUnique.isMultiHomog_one' hone, recR_eq]
    have hd : divSupp P (1 : MRing ι) = ∅ := by
      ext W
      simp only [divSupp, Ideal.span_singleton_one, le_top, sup_of_le_right, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h => (h.1.1.ne_top (top_le_iff.mp h.1.2)).elim
    have hl : logNorm (constLine (ι := ι) (-1)) 1 = fun _ => -1 := by
      funext z
      simp [logNorm, constLine, HermLine.ofWeight]
    rw [cycR, hd, finsum_mem_empty, arInt, hl, G5.ptsIntegral_const]
    simp only [zero_sub, neg_mul, one_mul, neg_neg]
    rfl
  have heq : ptsIntegral P (pot L) (fun _ => 1) = ptsIntegral P (pot fun _ : Fin n => fsH ι) (fun _ => 1) :=
    G5.ptsIntegral_eq_of_add_const P _ _ (fun j => ⟨1, fun z hz => by
      show Real.log ((scaledFSH ι).h z) = Real.log ((fsH ι).h z) + 1
      rw [show (1 : ℝ) = -(-1) by norm_num]
      exact G5.log_tensor_constLine (fsH ι) (-1) z hz.1⟩) _
  have hpos := hG K ι P n hP
  linarith
end ScaledFSTopPos

theorem ScaledFSTopPos.proof (hG : FSGeomDegPos.Statement) : ScaledFSTopPos.Statement := by
  intro K _ ι _ P d II hII hd hP
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  clear hd
  induction n generalizing P with
  | zero =>
    exact ScaledFSTopPos.step II hII hG 0
      (fun W hW _ => absurd hW (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι W)) P hP
  | succ m ih => exact ScaledFSTopPos.step II hII hG (m + 1) (fun W hW _ => (ih W hW).le) P hP

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftNefBig
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace ShiftedNefBig

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoNum_one_add (W : Ideal (MRing ι)) (a b : K → ℤ) (q : ℤ) :
    geoNum 1 W (fun _ => q • a + b) = q * geoNum 1 W (fun _ => a) + geoNum 1 W (fun _ => b) := by
  simp only [geoNum]
  split_ifs with h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc]
  · simp

theorem geoNum_one_one_nonneg (W : Ideal (MRing ι)) : 0 ≤ geoNum 1 W (fun _ => (1 : K → ℤ)) := by
  simp only [geoNum]
  split_ifs with h
  · refine Finset.sum_nonneg fun k _ => mul_nonneg zero_le_one ?_
    refine finsum_nonneg fun W' => finsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) ?_
    split_ifs <;> positivity
  · exact le_rfl

end ShiftedNefBig


open ShiftedNefBig in
theorem ShiftNefBig.proof (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement)
    (hB : NefPlusAmpleDegree.Statement) : ShiftNefBig.Statement := by
  intro K _ ι _ Ω _ y D A P0 _ har _ hP0 hs hnef hc q _
  have ha : (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a = (q : ℤ) • A.a + 1 := by
    show (q : ℤ) • A.a + (1 : ℤ) • (fsH ι).a = _
    rw [one_smul]
    rfl
  refine ⟨hP0, PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hs (Nat.cast_nonneg q) zero_le_one,
    HermLine.zcomb_isConjInvariantH hc (fsH_isConjInvariantH ι) _ _, ?_, ?_⟩
  · rw [ha]
    intro W hW hPW hch hdim
    rw [geoNum_one_add]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg q) (hnef W hW hPW hch hdim)) (geoNum_one_one_nonneg W)
  · rw [ha]
    exact hB K ι (mCoordIdeal y) D A.a har (nefOnGenericDeg_of_semipos NefOnGenericOfSemipos.proof hD hP0 hs) q

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

