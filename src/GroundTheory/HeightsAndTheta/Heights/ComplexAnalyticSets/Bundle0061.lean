module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0055
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0017
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem CutOffLimit.proof (hC : CutOff.Statement) (hM : ChartMassCompact.Statement)
    (hD : CutOffDominated.Statement) (hB : CutOffBoundaryBound.Statement) :
    CutOffLimit.Statement := by
  intro n d J A P hJ hdim hA hP
  obtain ⟨χ, hχs, hχI, hχU, hχ1, hχE, hχM⟩ := hC n d J A P hJ hdim hA hP
  refine ⟨χ, hχs, hχU, fun F G φ hF hG hφ hc => ?_⟩
  have hcont : ∀ f, SmoothNear (zeroSet J) f → ContinuousOn f (zeroSet J) := by
    rintro f ⟨U, -, hU, hf⟩
    exact hf.continuousOn.mono hU
  have hcons : ∀ f, SmoothNear (zeroSet J) f → ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := by
    intro f hf i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hφ i
  have hmeas : ∀ k, Measurable (χ k) := fun k => (hχs k).continuous.measurable
  refine ⟨hD n (d + 1) J A P χ F (vecCons G φ) hJ hdim hA hP hmeas hχI hχ1 (hcont F hF) (hcons G hG)
    (hM n (d + 1) J A F (vecCons G φ) hJ hdim hA (hcont F hF) (hcons G hG) (Or.inl hc)), ?_⟩
  have h1 := hD n (d + 1) J A P χ G (vecCons F φ) hJ hdim hA hP hmeas hχI hχ1 (hcont G hG) (hcons F hF)
    (hM n (d + 1) J A G (vecCons F φ) hJ hdim hA (hcont G hG) (hcons F hF) (Or.inr ⟨0, by simpa using hc⟩))
  obtain ⟨R, C, hRC⟩ := hB n d J A F G φ hJ hdim hA hF hG hφ hc
  have h0 : Tendsto (fun k => C * ((∫ y, chartAbsDens J A ((Metric.closedBall 0 R).indicator fun _ => 1)
      (vecCons (χ k) φ) y) + Real.sqrt (energyInt J A (Metric.closedBall 0 R) (χ k)))) atTop (𝓝 0) := by
    simpa using ((hχM R φ hφ).add (hχE R).sqrt).const_mul C
  refine h1.congr_dist (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) h0)
  rw [Real.dist_eq, abs_sub_comm]
  exact hRC (χ k) (hχs k)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffShape
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology
open scoped ContDiff

noncomputable section

private def cutProfile (k : ℕ) (w : ℝ) : ℝ :=
  if w = 0 then 0 else if 1 ≤ w then 1 else cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))

private theorem cutStep_small (k : ℕ) {w : ℝ} (h0 : w ≠ 0) (hw : |w| < cutLevel k) :
    cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 0 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : Real.log w < -Real.exp ((k : ℝ) + 1) := by
    rw [← Real.log_abs, ← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (abs_pos.2 h0) hw
  have h2 : (k : ℝ) + 1 < Real.log (-Real.log w) := by
    rw [← Real.log_exp ((k : ℝ) + 1)]
    exact Real.log_lt_log (Real.exp_pos _) (by linarith)
  have h3 : 1 < Real.log (-Real.log w) / ((k : ℝ) + 1) := (one_lt_div hk).2 h2
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

private theorem cutStep_large (k : ℕ) {w : ℝ} (hw : Real.exp (-Real.exp (((k : ℝ) + 1) / 2)) < w)
    (h1 : w < 1) : cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1)) = 1 := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hw0 : 0 < w := (Real.exp_pos _).trans hw
  have hl : -Real.exp (((k : ℝ) + 1) / 2) < Real.log w := by
    rw [← Real.log_exp (-Real.exp _)]
    exact Real.log_lt_log (Real.exp_pos _) hw
  have hneg : 0 < -Real.log w := neg_pos.2 (Real.log_neg hw0 h1)
  have h2 : Real.log (-Real.log w) < ((k : ℝ) + 1) / 2 := by
    rw [← Real.log_exp (((k : ℝ) + 1) / 2)]
    exact Real.log_lt_log hneg (by linarith)
  have h3 : Real.log (-Real.log w) / ((k : ℝ) + 1) < 1 / 2 := by
    rw [div_lt_iff₀ hk]; linarith
  exact Real.smoothTransition.one_of_one_le (by linarith)

private theorem cutProfile_contDiffOn (k : ℕ) :
    ContDiffOn ℝ ∞ (cutProfile k) (Set.Ioi (-cutLevel k)) := by
  obtain ⟨hc0, hc1⟩ := cutLevel_mem k
  set c' := Real.exp (-Real.exp (((k : ℝ) + 1) / 2))
  have hc'1 : c' < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos (Real.exp_pos _))
  refine (isOpen_Ioi.contDiffOn_iff).2 fun x hx => ?_
  rcases lt_or_ge x (cutLevel k) with hxc | hxc
  ·
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (Set.mem_Ioi.1 hx) hxc] with w hw
    have hwa : |w| < cutLevel k := abs_lt.2 hw
    unfold cutProfile
    split_ifs with h0 h1
    · rfl
    · exact absurd (h1.trans_lt (hw.2.trans hc1)) (lt_irrefl _)
    · exact cutStep_small k h0 hwa
  rcases lt_or_ge c' x with hxc' | hxc'
  ·
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hxc'] with w hw
    have hw0 : 0 < w := (Real.exp_pos _).trans hw
    unfold cutProfile
    split_ifs with h0 h1
    · exact absurd h0 hw0.ne'
    · rfl
    · exact cutStep_large k hw (not_le.1 h1)
  ·
    have hx0 : 0 < x := hc0.trans_le hxc
    have hx1 : x < 1 := hxc'.trans_lt hc'1
    have hform : ContDiffAt ℝ ∞ (fun w => cutStep (Real.log (-Real.log w) / ((k : ℝ) + 1))) x := by
      have hlog : ContDiffAt ℝ ∞ (fun w => Real.log (-Real.log w)) x :=
        ((Real.contDiffAt_log.2 hx0.ne').neg).log (neg_ne_zero.2 (Real.log_neg hx0 hx1).ne)
      exact Real.smoothTransition.contDiffAt.comp x
        (contDiffAt_const.sub (contDiffAt_const.mul (hlog.div_const _)))
    refine hform.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hx0 hx1] with w hw
    simp [cutProfile, hw.1.ne', not_le.2 hw.2]

theorem CutOffShape.proof : CutOffShape.Statement := by
  intro m Q
  have hF : ∀ k, logLogCut Q k = cutProfile k ∘ fun y => ‖eval y Q‖ ^ 2 := fun k => rfl
  have hstep : ∀ t, cutStep t ∈ Set.Icc (0 : ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨fun k => ⟨?_, fun y => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
  · rw [hF]
    have hw : ContDiff ℝ ∞ fun y : Fin m → ℂ => ‖eval y Q‖ ^ 2 :=
      contDiff_norm_sq ℝ |>.comp
        (((AnalyticOnNhd.eval_mvPolynomial Q).contDiff (n := ∞)).restrict_scalars ℝ)
    exact (cutProfile_contDiffOn k).comp_contDiff hw fun y =>
      (neg_neg_of_pos (cutLevel_mem k).1).trans_le (by exact sq_nonneg ‖eval y Q‖)
  · unfold logLogCut; split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hstep _
  · have h1 := (cutLevel_mem k).2
    unfold logLogCut logAbsSq; split_ifs with h0 h1'
    · rfl
    · exact absurd (h1'.trans_lt (hy.trans h1)) (lt_irrefl _)
    · exact cutStep_small k h0 (by rwa [abs_of_nonneg (by positivity)])
  · have hw0 : ‖eval y Q‖ ^ 2 ≠ 0 := by positivity
    by_cases hw1 : 1 ≤ ‖eval y Q‖ ^ 2
    · simp [logLogCut, hw0, hw1]
    refine tendsto_const_nhds.congr' ?_
    set L := Real.log (-Real.log (‖eval y Q‖ ^ 2))
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * |L|)
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
    have h3 : L / ((k : ℝ) + 1) < 1 / 2 := by
      rw [div_lt_iff₀ hk']; linarith [le_abs_self L]
    simp only [logLogCut, logAbsSq, hw0, hw1, if_false]
    exact (Real.smoothTransition.one_of_one_le (by linarith)).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDerivationMinorOfDetection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem DerivationMinorOfDetection.proof : DerivationMinorOfDetection.Statement := by
  intro T _ P _ h f hfP hind hdet
  let A := Localization.AtPrime P
  let K := ResidueField A
  let π : T →+* K := (residue A).comp (algebraMap T A)
  have hπ : ∀ x, π x = 0 ↔ x ∈ P := fun x => by
    show residue A (algebraMap T A x) = 0 ↔ x ∈ P
    rw [residue_eq_zero_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff A P x
  let v : Derivation ℤ T T → Fin h → K := fun D i => π (D (f i))
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφv : ∀ w : Fin h → K, φ w = ∑ i, w i * φ (Pi.single i 1) := fun w => by
      conv_lhs => rw [pi_eq_sum_univ w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    choose a ha using fun i => residue_surjective (R := A) (φ (Pi.single i 1))
    obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples P.primeCompl Finset.univ a
    choose b hb using fun i => hs i (Finset.mem_univ i)
    have hπb : ∀ i, π (b i) = π s * φ (Pi.single i 1) := fun i => by
      simp only [π, RingHom.comp_apply, hb i, Algebra.smul_def, map_mul, ha]
    have hsq := hdet (∑ i, b i * f i) (Ideal.sum_mem _ fun i _ => P.mul_mem_left _ (hfP i)) fun D => by
      have h1 : ∑ i, b i * D (f i) ∈ P := by
        have hD : φ (v D) = 0 := hφ (Submodule.subset_span ⟨D, rfl⟩)
        rw [hφv] at hD
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hπ, map_sum]
        simp only [map_mul, hπb]
        rw [show ∑ i, π s * φ (Pi.single i 1) * π (D (f i)) = π s * ∑ i, v D i * φ (Pi.single i 1) by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [v]; ring, hD, mul_zero]
      have hl : ∀ i, D (b i * f i) = b i * D (f i) + f i * D (b i) := fun i => by
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [hl, Finset.sum_add_distrib]
      exact P.add_mem h1 (Ideal.sum_mem _ fun i _ => P.mul_mem_right _ (hfP i))
    have hbP : ∀ i, b i ∈ P := fun i => (IsLocalization.AtPrime.to_map_mem_maximal_iff A P _).1
      (hind (fun i => algebraMap T A (b i)) (by simpa only [map_sum, map_mul] using hsq) i)
    have hsP : π s ≠ 0 := fun h0 => s.2 ((hπ s).1 h0)
    have he : ∀ i, φ (Pi.single i 1) = 0 := fun i => by
      have := (hπ (b i)).2 (hbP i)
      rw [hπb] at this
      exact (mul_eq_zero.1 this).resolve_left hsP
    exact hφ0 (LinearMap.ext fun w => by simp [hφv w, he])
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent'.{0} K v
  let bas := Module.Basis.mk hli (by rw [hsp, hspan])
  have hfin : Finite κ := Module.Finite.finite_basis bas
  have hκ : Nat.card κ = h := by rw [← Module.finrank_eq_nat_card_basis bas, Module.finrank_fin_fun]
  let e : Fin h ≃ κ := (finCongr hκ.symm).trans (Finite.equivFin κ).symm
  refine ⟨fun j => a (e j), fun hmem => ?_⟩
  have hunit : IsUnit (Matrix.of fun i j => v (a (e j)) i) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli.comp e e.injective
  have hne : π (Matrix.of fun i j => a (e j) (f i)).det ≠ 0 := by
    rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hunit).ne_zero
  exact hne ((hπ _).2 hmem)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteFibreCentredEquation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable def FiniteFibreCentredEquation.centredPoly (a : ℂ) {k : ℕ} (c : Fin k → ℂ) : ℂ[X] :=
  (X - C a) ^ k + ∑ j : Fin k, C (c j) * (X - C a) ^ (j : ℕ)

theorem FiniteFibreCentredEquation.centredPoly_eval (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (T : ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).eval T = (T - a) ^ k + ∑ j, c j * (T - a) ^ (j : ℕ) := by
  simp [FiniteFibreCentredEquation.centredPoly, eval_finsetSum]

theorem FiniteFibreCentredEquation.centredPoly_coeff (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (m : ℕ) :
    (FiniteFibreCentredEquation.centredPoly a c).coeff m =
      ((X - C a) ^ k).coeff m + ∑ j : Fin k, c j * ((X - C a) ^ (j : ℕ)).coeff m := by
  simp [FiniteFibreCentredEquation.centredPoly, finsetSum_coeff, coeff_C_mul]

theorem FiniteFibreCentredEquation.centredPoly_natDegree_lt (a : ℂ) {k : ℕ} (c : Fin k → ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).natDegree < k + 1 := by
  refine Nat.lt_succ_of_le (natDegree_add_le_of_degree_le ?_ ?_)
  · rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
  · refine natDegree_sum_le_of_forall_le _ _ fun j _ => (natDegree_C_mul_le _ _).trans ?_
    rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
    exact j.isLt.le

theorem FiniteFibreCentredEquation.centredPoly_coeff_top (a : ℂ) {k : ℕ} (c : Fin k → ℂ) : (FiniteFibreCentredEquation.centredPoly a c).coeff k = 1 := by
  rw [FiniteFibreCentredEquation.centredPoly_coeff]
  have h1 : ((X - C a) ^ k).coeff k = 1 := by
    have h := ((monic_X_sub_C a).pow k).coeff_natDegree
    rwa [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one] at h
  have h2 : ∀ j : Fin k, ((X - C a) ^ (j : ℕ)).coeff k = 0 := fun j =>
    coeff_eq_zero_of_natDegree_lt (by
      rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]; exact j.isLt)
  simp [h1, h2]

theorem FiniteFibreCentredEquation.centredPoly_eval_expand (a : ℂ) {k : ℕ} (c : Fin k → ℂ) (T : ℂ) :
    (FiniteFibreCentredEquation.centredPoly a c).eval T = T ^ k + ∑ m : Fin k, (FiniteFibreCentredEquation.centredPoly a c).coeff m * T ^ (m : ℕ) := by
  rw [eval_eq_sum_range' (FiniteFibreCentredEquation.centredPoly_natDegree_lt a c), Finset.sum_range_succ, FiniteFibreCentredEquation.centredPoly_coeff_top,
    Finset.sum_range (fun m => (FiniteFibreCentredEquation.centredPoly a c).coeff m * T ^ m)]
  ring

theorem FiniteFibreCentredEquation.proof (hI : FiniteFibreGermIntegral.Statement)
    (hW : WeierstrassPreparation.Statement) : FiniteFibreCentredEquation.Statement := by
  intro σ _ S w d A hS hfib g hg
  obtain ⟨N, a, ha, hrel⟩ := hI σ S w d A hS hfib (fun z => g z - g w) (hg.sub analyticAt_const)
  set f : (Option (Fin d) → ℂ) → ℂ := fun x =>
    x none ^ N + ∑ j, a j (A w + fun i => x (some i)) * x none ^ (j : ℕ) with hf_def
  have hlast : AnalyticAt ℂ (fun x : Option (Fin d) → ℂ => x none) 0 :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin d) => ℂ) none).analyticAt 0
  have hfirst : AnalyticAt ℂ (fun x : Option (Fin d) → ℂ => A w + fun i => x (some i)) 0 :=
    analyticAt_const.add ((ContinuousLinearMap.pi fun i : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option (Fin d) => ℂ) (some i)).analyticAt 0)
  have hfan : AnalyticAt ℂ f 0 := by
    refine (hlast.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp_of_eq hfirst (show A w + (0 : Fin d → ℂ) = A w from add_zero _)).mul (hlast.pow _)

  set p : ℂ[X] := X ^ N + ∑ j : Fin N, C (a j (A w)) * X ^ (j : ℕ) with hp_def
  have hpm : p.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hpe : (fun t => f (pointWithLast 0 t)) = fun t => p.eval t := by
    funext t
    have h0 : (fun i => pointWithLast (0 : Fin d → ℂ) t (some i)) = 0 := rfl
    simp only [hf_def, hp_def, h0, add_zero, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C]
    rfl
  have hne : analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 ≠ ⊤ := by
    rw [hpe]
    intro htop
    have hpan : AnalyticOnNhd ℂ (fun t => p.eval t) Set.univ := fun t _ =>
      (Polynomial.differentiable p).analyticAt t
    have hall : Set.EqOn (fun t => p.eval t) 0 Set.univ :=
      hpan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) (analyticOrderAt_eq_top.1 htop)
    exact hpm.ne_zero (Polynomial.funext fun t => by simpa using hall (Set.mem_univ t))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = k :=
    ⟨_, (Nat.cast_analyticOrderNatAt hne).symm⟩
  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hW (Fin d) k f hfan hk
  refine ⟨k, fun m y => (FiniteFibreCentredEquation.centredPoly (g w) fun j => c j (y - A w)).coeff m, fun m => ?_, fun T => ?_, ?_⟩
  · simp only [FiniteFibreCentredEquation.centredPoly_coeff]
    refine analyticAt_const.add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((hc j).comp_of_eq (f := fun y : Fin d → ℂ => y - A w) (analyticAt_id.sub analyticAt_const)
      (sub_self _)).mul analyticAt_const
  · rw [← FiniteFibreCentredEquation.centredPoly_eval_expand, FiniteFibreCentredEquation.centredPoly_eval]
    simp [hc0]
  ·
    set φ : (σ → ℂ) → (Option (Fin d) → ℂ) := fun z => pointWithLast (A z - A w) (g z - g w) with hφ_def
    have hφc : ContinuousAt φ w := by
      refine continuousAt_pi.2 fun o => ?_
      cases o with
      | none => exact hg.continuousAt.sub continuousAt_const
      | some i => exact ((continuous_apply i).comp A.continuous).continuousAt.sub continuousAt_const
    have hφw : φ w = 0 := by
      funext o; cases o <;> simp [hφ_def, pointWithLast]
    have hφt : Tendsto φ (𝓝 w) (𝓝 0) := hφw ▸ hφc.tendsto
    filter_upwards [hφt.eventually hfe, hφt.eventually (he.continuousAt.eventually_ne he0), hrel]
      with z h1 h2 h3 hzX
    have hf0 : f (φ z) = 0 := by
      show (g z - g w) ^ N + ∑ j, a j (A w + (A z - A w)) * (g z - g w) ^ (j : ℕ) = 0
      rw [add_sub_cancel]
      exact h3 hzX
    have hω : (g z - g w) ^ k + ∑ j, c j (A z - A w) * (g z - g w) ^ (j : ℕ) = 0 := by
      rw [hf0] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left h2
    rw [← FiniteFibreCentredEquation.centredPoly_eval_expand, FiniteFibreCentredEquation.centredPoly_eval]
    exact hω

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermGeneralCoordinates
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem exists_lastCoord_ne_zero_of_mem_nhds {σ : Type} {U : Set (Option σ → ℂ)} {w : Option σ → ℂ}
    (hU : U ∈ 𝓝 w) : ∃ v ∈ U, v none ≠ 0 := by
  classical
  let g : ℂ → Option σ → ℂ := fun s => Function.update w none s
  have hg : Continuous g := by
    refine continuous_pi fun o => ?_
    cases o with
    | none => simpa [g] using continuous_id'
    | some i => simpa [g] using continuous_const
  have hgw : g (w none) = w := Function.update_eq_self none w
  have hev : ∀ᶠ s in 𝓝 (w none), g s ∈ U := by
    have := hg.tendsto (w none)
    rw [hgw] at this
    exact this hU
  have hne : ∀ᶠ s in 𝓝[≠] (w none), s ≠ 0 := by
    by_cases h0 : w none = 0
    · rw [h0]; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (isOpen_ne.mem_nhds h0)
  obtain ⟨s, hs1, hs2⟩ := (((hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ s in 𝓝[≠] (w none), g s ∈ U).and hne).exists
  exact ⟨g s, hs1, by simpa [g] using hs2⟩

theorem GeneralLinearCoordinates.proof : GeneralLinearCoordinates.Statement := by
  classical
  intro σ _ f hf hnz
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd

  obtain ⟨w, hwb, hfw⟩ : ∃ w ∈ Metric.ball (0 : Option σ → ℂ) r, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hnz (Filter.mem_of_superset (Metric.ball_mem_nhds _ hr) fun x hx => h x hx)
  have hUopen : IsOpen (Metric.ball (0 : Option σ → ℂ) r ∩ f ⁻¹' {z | z ≠ 0}) :=
    hfr.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_ne
  obtain ⟨v, ⟨hvb, hfv⟩, hvt⟩ := exists_lastCoord_ne_zero_of_mem_nhds (hUopen.mem_nhds ⟨hwb, hfw⟩)
  replace hfv : f v ≠ 0 := hfv

  let e : Option σ → ℂ := Pi.single none 1
  let L : (Option σ → ℂ) →ₗ[ℂ] (Option σ → ℂ) :=
    LinearMap.id + (LinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).smulRight (v - e)
  have hL : ∀ x, L x = x + x none • (v - e) := fun x => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 : (L x) none = 0 := by rw [hx]; rfl
    have hnone : x none = 0 := by
      rw [hL] at h1
      simp [e] at h1
      have h2 : x none * v none = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_right hvt
    rw [hL, hnone, zero_smul, add_zero] at hx
    exact hx
  let A : (Option σ → ℂ) ≃L[ℂ] (Option σ → ℂ) :=
    (LinearEquiv.ofInjectiveEndo L hLinj).toContinuousLinearEquiv
  have hA : ∀ t : ℂ, A (pointWithLast 0 t) = t • v := by
    intro t
    show L (pointWithLast 0 t) = t • v
    rw [hL]
    funext o
    cases o with
    | none => simp [pointWithLast, e]; ring
    | some i => simp [pointWithLast, e]
  refine ⟨A, ?_⟩
  have hfun : (fun t => f (A (pointWithLast 0 t))) = fun t : ℂ => f (t • v) := by
    funext t; rw [hA]
  rw [hfun]

  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr fun h => hvt (by rw [h]; rfl)
  have hvr : ‖v‖ < r := by simpa using hvb
  set R := r / ‖v‖
  have hR1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right, norm_one]
    exact (one_lt_div hv0).mpr hvr
  have hR0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) R := Metric.mem_ball_self (lt_trans one_pos
    ((one_lt_div hv0).mpr hvr))
  have han : AnalyticOnNhd ℂ (fun t : ℂ => f (t • v)) (Metric.ball (0 : ℂ) R) := by
    intro t ht
    have htv : t • v ∈ Metric.ball (0 : Option σ → ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul]
      rw [Metric.mem_ball, dist_zero_right] at ht
      calc ‖t‖ * ‖v‖ < R * ‖v‖ := mul_lt_mul_of_pos_right ht hv0
        _ = r := div_mul_cancel₀ r hv0.ne'
    have hs : AnalyticAt ℂ (fun s : ℂ => s • v) t := analyticAt_id.smul analyticAt_const
    show AnalyticAt ℂ (f ∘ fun s : ℂ => s • v) t
    exact AnalyticAt.comp (f := fun s : ℂ => s • v) (x := t) (hfr _ htv) hs
  have hnot : ¬ (∀ᶠ t in 𝓝 (0 : ℂ), f (t • v) = 0) := by
    intro h
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hR0 h hR1
    simp at this
    exact hfv this
  have hne : analyticOrderAt (fun t : ℂ => f (t • v)) 0 ≠ ⊤ := fun h =>
    hnot (analyticOrderAt_eq_top.mp h)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hne
  exact ⟨d, hd.symm⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGeneratorsClearDenominators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem LocalGeneratorsClearDenominators.proof : LocalGeneratorsClearDenominators.Statement :=
  _root_.UpperTheory.Reformulated.B.Qe31.proof

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

