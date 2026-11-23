module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ProjectiveLineZeroFormHolds
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.ContDiffOfContDiffOnZeroOff
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0112
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0110
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolydiscLelongLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open scoped ContDiff

noncomputable section

namespace PolydiscLelongLimit

theorem hypIncl_mem_ball {d : ℕ} {r : ℝ} (w : Fin d → ℂ) :
    hypIncl w ∈ Metric.ball (0 : Fin (d + 1) → ℂ) r ↔ w ∈ Metric.ball 0 r := by
  rcases le_or_gt r 0 with hr | hr
  · simp [Metric.ball_eq_empty.2 hr]
  · simp only [mem_ball_zero_iff, pi_norm_lt_iff hr, Fin.forall_fin_succ, hypIncl, Fin.cons_zero,
      Fin.cons_succ, norm_zero, hr, true_and]

theorem extend_by_zero {D : ℕ} {r ρ : ℝ} {χ : (Fin D → ℂ) → ℝ} (hρ : ρ < r)
    (hχ : ContDiffOn ℝ ∞ χ (Metric.ball 0 r))
    (hsupp : ∀ τ ∈ Metric.ball (0 : Fin D → ℂ) r, χ τ ≠ 0 → τ ∈ Metric.ball 0 ρ) :
    ContDiff ℝ ∞ ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      HasCompactSupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ∧
      tsupport ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) ⊆ Metric.closedBall 0 ρ ∧
      Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) := by
  have h0 : ∀ τ ∉ Metric.closedBall (0 : Fin D → ℂ) ρ,
      (Metric.ball (0 : Fin D → ℂ) r).indicator χ τ = 0 := by
    intro τ hτ
    by_cases hU : τ ∈ Metric.ball (0 : Fin D → ℂ) r
    · rw [Set.indicator_of_mem hU]
      by_contra h
      exact hτ (Metric.ball_subset_closedBall (hsupp τ hU h))
    · exact Set.indicator_of_notMem hU _
  have heq : Set.EqOn ((Metric.ball (0 : Fin D → ℂ) r).indicator χ) χ (Metric.ball 0 r) :=
    fun τ hτ => Set.indicator_of_mem hτ _
  exact ⟨contDiff_of_contDiffOn_zero_off Metric.isOpen_ball Metric.isClosed_closedBall
    (Metric.closedBall_subset_ball hρ) (hχ.congr heq) h0,
    HasCompactSupport.intro (isCompact_closedBall 0 ρ) h0,
    closure_minimal (fun τ hτ => by_contra fun h => (Function.mem_support.1 hτ) (h0 τ h))
      Metric.isClosed_closedBall, heq⟩

theorem logReg_contDiffOn {D : ℕ} {U : Set (Fin D → ℂ)} (hU : IsOpen U) {F : (Fin D → ℂ) → ℂ}
    (hF : DifferentiableOn ℂ F U) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := by
  intro z hz
  have h1 : ContDiffAt ℝ ∞ F z :=
    ((ReciprocityTheory.AnForm.Osgood.osgood D U F hU hF z hz).contDiffAt (n := ∞)).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ∞ (fun τ => ‖F τ‖ ^ 2 + ε) z := (h1.norm_sq ℝ).add contDiffAt_const
  exact ((h2.log (by positivity)).div_const 2).contDiffWithinAt

end PolydiscLelongLimit


open PolydiscLelongLimit in
theorem PolydiscLelongLimit.proof : PolydiscLelongLimit.Statement := by
  intro d m r ρ F χ ψ hρ hF hχ hsupp hψ
  obtain ⟨H, hHd, hH0, hFH⟩ := hF
  have h3 : (3 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  obtain ⟨hv, hvc, hvt, hvχ⟩ := extend_by_zero hρ hχ hsupp
  set U : Set (Fin (d + 1) → ℂ) := Metric.ball 0 r with hUdef
  set v := U.indicator χ with hvdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hvU : tsupport v ⊆ U := hvt.trans (Metric.closedBall_subset_ball hρ)
  have hFd : DifferentiableOn ℂ F U :=
    (((differentiable_apply 0).pow m).differentiableOn.mul hHd).congr fun t ht => hFH t ht
  have hFne : ∀ τ ∈ U, τ 0 ≠ 0 → F τ ≠ 0 := fun τ hτ h0 => by
    rw [hFH τ hτ]; exact mul_ne_zero (pow_ne_zero _ h0) (hH0 τ hτ)
  have hdens0 : ∀ τ, τ ∉ tsupport v → densV v ψ τ = 0 := fun τ hτ => maDens_cons_eq_zero ψ hτ
  have hIon : ∀ f : (Fin (d + 1) → ℂ) → ℝ, IntegrableOn (fun z => f z * densV v ψ z) U →
      Integrable (fun z => f z * densV v ψ z) := fun f h =>
    (integrableOn_iff_integrable_of_support_subset fun z hz => by_contra fun h' =>
      (Function.mem_support.1 hz) (mul_eq_zero_of_right _ (hdens0 z fun h'' => h' (hvU h'')))).1 h

  have hgood : ∀ ε : ℝ, 0 < ε →
      Integrable (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) ∧
      maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U =
        ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
    intro ε hε
    have hP := parts_thm d ψ v (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, (logReg_contDiffOn hU hFd hε).of_le h3,
        fun k => (hψ k).of_le h3⟩
    refine ⟨hIon _ hP.2.1, ?_⟩
    calc maInt (Matrix.vecCons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) χ U
        = maInt (Fin.cons (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) ψ) v U := by
          unfold maInt
          exact setIntegral_congr_fun hU.measurableSet fun τ hτ => by
            simp only [hvχ hτ]; try rfl
      _ = maInt (Fin.cons v ψ) (fun τ => Real.log (‖F τ‖ ^ 2 + ε) / 2) U := hP.2.2.2.2.symm
      _ = ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ := by
          unfold maInt
          exact setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ =>
            mul_eq_zero_of_right _ (hdens0 τ fun h => hτ (hvU h))

  have hL0 := log_norm_integral_formula_unit d (m : ℤ) U v ψ H ⟨hU, hv.of_le h3, hvc, hvU, hψ⟩ hHd hH0
  have hlogF : (fun z => Real.log ‖F z‖ * densV v ψ z) =
      fun z => Real.log ‖z 0 ^ (m : ℤ) * H z‖ * densV v ψ z := by
    funext z
    by_cases hz : z ∈ U
    · rw [hFH z hz, zpow_natCast]
    · rw [hdens0 z fun h => hz (hvU h), mul_zero, mul_zero]
  have hint : Integrable (fun τ => Real.log ‖F τ‖ * densV v ψ τ) := by rw [hlogF]; exact hL0.1
  have hdensI : Integrable (densV v ψ) := by
    have hP1 := parts_thm d ψ v (fun _ => (1 : ℝ)) U
      ⟨hU, (hv.of_le h3).contDiffOn, hvc, hvU, contDiffOn_const, fun k => (hψ k).of_le h3⟩
    exact (hIon (fun _ => 1) hP1.2.1).congr (Eventually.of_forall fun z => one_mul _)
  obtain ⟨C, hC⟩ : ∃ C, ∀ τ ∈ tsupport v, ‖(1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1)‖ ≤ C :=
    hvc.isCompact.exists_bound_of_continuousOn fun τ hτ =>
      (continuousAt_const.mul ((((hFd.continuousOn.continuousAt (hU.mem_nhds (hvU hτ))).norm.pow 2).add
        continuousAt_const).log (by positivity : ‖F τ‖ ^ 2 + 1 ≠ 0))).continuousWithinAt

  have hlim : Tendsto (fun ε : ℝ => ∫ τ, Real.log (‖F τ‖ ^ 2 + ε) / 2 * densV v ψ τ) (𝓝[>] 0)
      (𝓝 (∫ τ, Real.log ‖F τ‖ * densV v ψ τ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun τ => |Real.log ‖F τ‖ * densV v ψ τ| + C * |densV v ψ τ|)
      (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).1.aestronglyMeasurable) ?_
      (hint.abs.add (hdensI.abs.const_mul C)) ?_
    · filter_upwards [Ioc_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hε
      filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ tsupport v
      · have h1 := gReg_abs_le hε.1 hε.2 (hFne τ (hvU hτ) hτ0)
        have h2 := hC τ hτ
        rw [Real.norm_eq_abs] at h2
        have e : Real.log (‖F τ‖ ^ 2 + ε) / 2 = gReg ε (F τ) := by unfold gReg; ring
        have h4 : |gReg ε (F τ)| ≤ |Real.log ‖F τ‖| + C :=
          h1.trans (by linarith [le_abs_self ((1 / 2 : ℝ) * Real.log (‖F τ‖ ^ 2 + 1))])
        rw [Real.norm_eq_abs, abs_mul, abs_mul, e]
        calc |gReg ε (F τ)| * |densV v ψ τ| ≤ (|Real.log ‖F τ‖| + C) * |densV v ψ τ| :=
              mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
          _ = _ := by ring
      · rw [hdens0 τ hτ]; simp
    · filter_upwards [ae_coord_ne_zero (0 : Fin (d + 1))] with τ hτ0
      by_cases hτ : τ ∈ U
      · have hpos : 0 < ‖F τ‖ ^ 2 := pow_pos (norm_pos_iff.2 (hFne τ hτ hτ0)) 2
        have hc : Tendsto (fun ε : ℝ => ‖F τ‖ ^ 2 + ε) (𝓝[>] 0) (𝓝 (‖F τ‖ ^ 2 + 0)) :=
          (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
        rw [add_zero] at hc
        have e : Real.log ‖F τ‖ = Real.log (‖F τ‖ ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
        rw [e]
        exact (((Real.continuousAt_log hpos.ne').tendsto.comp hc).div_const 2).mul_const _
      · rw [hdens0 τ fun h => hτ (hvU h)]
        simp only [mul_zero]
        exact tendsto_const_nhds

  have hR : ∫ w in Metric.ball (0 : Fin d → ℂ) r, χ (hypIncl w) * densHyp ψ w =
      ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [setIntegral_congr_fun (g := fun w => v (hypIncl w) * densHyp ψ w)
      Metric.isOpen_ball.measurableSet fun w hw => by
      simp only [hvχ ((hypIncl_mem_ball w).2 hw)]]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw =>
      mul_eq_zero_of_left (Set.indicator_of_notMem (mt (hypIncl_mem_ball w).1 hw) _) _
  have hlimF : ∫ τ, Real.log ‖F τ‖ * densV v ψ τ = (m : ℝ) * ∫ w, v (hypIncl w) * densHyp ψ w := by
    rw [hlogF, hL0.2, Int.cast_natCast]
  rw [hR, ← hlimF]
  exact hlim.congr' (eventually_mem_nhdsWithin.mono fun ε hε => (hgood ε hε).2.symm)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets
open scoped nonZeroDivisors

noncomputable section

theorem SliceMassFinite.exists_projClosure {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (hI : I.IsPrime) (hℓ : linForm ℓ - 1 ∈ I)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (W : Ideal (MvPolynomial (Fin n) ℂ)) (F : MvPolynomial (Fin (e + 2) × Fin n) ℂ),
      IsProjPrime W ∧ IsChowForm W (e + 2) F ∧ linForm ℓ ∉ W ∧ W ⊔ Ideal.span {linForm ℓ - 1} = I := by
  obtain ⟨W, hW, hℓW, hWI, -⟩ := ChartHomogenise.proof ℂ n I ℓ hI hℓ
  have hP := hW.isPrime

  have hx : Ideal.Quotient.mk W (linForm ℓ - 1) ∈ (MvPolynomial (Fin n) ℂ ⧸ W)⁰ := by
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => hP.ne_top ?_
    have h00 := hW.isHomog _ (Ideal.Quotient.eq_zero_iff_mem.mp h0) 0
    rw [homogeneousComponent_zero] at h00
    have hc : AddMonoidAlgebra.coeff (linForm ℓ - 1) 0 = -1 := by
      simp [linForm, coeff_sum, coeff_C_mul, coeff_X]
    rw [hc, map_neg, map_one, Ideal.neg_mem_iff] at h00
    exact (Ideal.eq_top_iff_one W).mpr h00
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hx
  have eq := DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {linForm ℓ - 1})
  rw [Ideal.map_span, Set.image_singleton] at eq
  rw [ringKrullDim_eq_of_ringEquiv eq, hWI, hdim] at h1

  have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ (n : WithBot ℕ∞) := by
    have := ringKrullDim_quotient_le W
    rwa [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at this

  have hdimW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = ((e + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    generalize hD : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = D at h1 h2
    induction D using WithBot.recBotCoe with
    | bot => simp at h1
    | coe b =>
      induction b using ENat.recTopCoe with
      | top =>
        exfalso
        have h3 : (⊤ : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h2
        exact ENat.natCast_ne_top _ (top_le_iff.mp h3)
      | coe m =>
        have hm1 : e + 1 + 1 ≤ m := by exact_mod_cast h1
        obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have hA' : IndefiniteRowSideFullHecke.ComplexSets.IsAffVariety W (k + 1) := ⟨hP, by rw [hD]; rfl⟩
        have h3 := IndefiniteRowSideFullHecke.ComplexSets.le_ringKrullDim_slice hA' hW.isHomog hℓW
        rw [hWI, hdim] at h3
        have hk : k ≤ e + 1 := by exact_mod_cast h3
        have hke : k + 1 = e + 1 + 1 := by omega
        rw [hke]
        rfl
  obtain ⟨F, hFW⟩ := (IndefiniteRowSideFullHecke.ComplexSets.exists_isChowForm_iff (e := e + 1) hW).mpr ⟨hP, hdimW⟩
  exact ⟨W, F, hW, hFW, hℓW, hWI⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserGradientIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem UniformiserGradientIndependent.proof (hjac : NormalCurveJacobian.Statement)
    (hdvr : NormalCurvePointDVR.Statement) : UniformiserGradientIndependent.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, -, hk, hfI, hli, -, -⟩ := hjac σ I w hI hic hdim hw
  obtain ⟨_, _⟩ := hdvr σ I w hI hic hdim hw
  refine ⟨k, f, hk, hfI, hli.finCons fun hmem ↦ ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  set φ := algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) with hφ
  have hfw : ∀ j, eval w (f j) = 0 := fun j ↦ hw (f j) (hfI j)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  set p := t - ∑ j, C (c j) * f j with hp
  have hpm : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) := by
    simp [hp, RingHom.mem_ker, htw, hfw]
  have hpg : GradientAtPoint.grad w p = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hp, map_sub, map_sum]
    simp_rw [GradientAtPoint.grad_mul_of_eval_eq_zero w _ _ (hfw _), eval_C]
    have hg : ∀ q, GradientAtPoint.grad w q = fun i ↦ eval w (pderiv i q) :=
      fun q ↦ funext (GradientAtPoint.grad_apply w q)
    simp_rw [hg]
    exact sub_eq_zero.2 hc.symm
  have hp2 := GradientAtPoint.mem_sq_of_grad_eq_zero w hpm hpg
  have hφf : ∀ j, φ (f j) = 0 := fun j ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ (hfI j))
  have hφt : φ t = φ p := by simp [hp, hφf]
  have hmax : Ideal.map φ (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ≤
      IsLocalRing.maximalIdeal (pointLocalRing I w) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ pointLocalRing_eval_ne_zero_of_isUnit I w hw g hu (RingHom.mem_ker.1 hg)
  have ht2 : φ t ∈ IsLocalRing.maximalIdeal (pointLocalRing I w) ^ 2 := by
    rw [hφt]
    exact Ideal.pow_right_mono hmax 2 (Ideal.map_pow φ _ 2 ▸ Ideal.mem_map_of_mem φ hp2)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 ht, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at ht2
  obtain ⟨a, ha⟩ := ht2
  have h1 : φ t * (a * φ t) = φ t * 1 := by rw [mul_one]; nth_rewrite 3 [← ha]; ring
  exact ht.not_isUnit
    (IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact mul_left_cancel₀ ht.ne_zero h1))

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PUniformiserLocallyInjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem UniformiserLocallyInjective.proof (hgrad : UniformiserGradientIndependent.Statement)
    (hchart : PolynomialChartInjective.Statement) : UniformiserLocallyInjective.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, hk, hfI, hli⟩ := hgrad σ I w t hI hic hdim hw ht
  obtain ⟨U, hU, hinj⟩ := hchart σ k t f w hk hli
  refine ⟨U, hU, hinj.mono ?_⟩
  rintro z ⟨hz, hzU⟩
  exact ⟨hzU, fun j ↦ hz (f j) (hfI j)⟩

end GroundTheory.Heights₂.Heights
end

