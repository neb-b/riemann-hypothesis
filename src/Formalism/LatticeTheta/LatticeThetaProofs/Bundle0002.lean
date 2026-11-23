module

public import Formalism.LatticeTheta.LatticeSummableDecay

@[expose] public section

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.Assembly
section
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma norm_exp_two_pi_I_mul (r : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  rw [show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem poissonDecay_of (hD : DualIsLattice (V := V)) (h1 : LatticeSummableDecay V)
    (h2 : Periodization V) (h3 : UnfoldCoeff V) (h4 : LatticeFourierSeries V) :
    PoissonDecay (V := V) := by
  intro Λ _ _ f hf b hb hfO hFO x
  obtain ⟨hdd, hdz⟩ := hD Λ
  haveI := hdd
  haveI : IsZLattice ℝ (dual Λ) := hdz

  have hphase : (fun v : V => (𝓕 f : V → ℂ) v * Complex.exp (2 * Real.pi * Complex.I * (⟪v, x⟫ : ℝ)))
      =O[cocompact V] (fun v => ‖v‖ ^ (-b)) := by
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun v => ?_)).trans hFO
    rw [norm_mul, norm_exp_two_pi_I_mul, mul_one, one_mul]
  have hsum := h1 (dual Λ) _ b hb hphase
  refine ⟨hsum, ?_⟩
  obtain ⟨hint, hper, hcont, hinv⟩ := h2 Λ f hf b hb hfO

  let B := Module.Free.chooseBasis ℤ Λ
  have hD' := ZLattice.isAddFundamentalDomain B (volume : Measure V)
  have hcoef : ∀ μ : dual Λ,
      ∫ y in ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ Λ), (∑' l : Λ, f ((l : V) + y)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ :=
    fun μ => h3 Λ f hint _ hD' μ μ.2
  have hFs : Summable (fun μ : dual Λ => (𝓕 f : V → ℂ) μ) := h1 (dual Λ) _ b hb hFO
  have hG := h4 Λ (fun y => ∑' l : Λ, f ((l : V) + y)) hcont
    (fun l y => by simpa using hinv l y) _ hD' (by simpa only [hcoef] using hFs) x
  simp only [hcoef] at hG
  have hval : (ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ, (𝓕 f : V → ℂ) μ *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) = ∑' l : Λ, f ((l : V) + x) := by
    rw [← tsum_mul_left, ← hG.tsum_eq]
    congr 1; funext μ; ring
  rw [hval]
  exact (hper x).hasSum

theorem poissonSchwartz_of (hP : PoissonDecay (V := V)) (h6 : SchwartzDecay V) :
    PoissonSchwartz (V := V) := by
  intro Λ _ _ f x
  have hd : (Module.finrank ℝ V : ℝ) < Module.finrank ℝ V + 1 := by linarith
  exact hP Λ f f.continuous _ hd (h6 f _).1 (h6 f _).2 x

end Formalism.H
end
end

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.FundamentalDomainEqPreimage
section
open MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {ι : Type*} [Fintype ι]

abbrev boxIco (ι : Type*) : Set (ι → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1

theorem volume_boxIco : volume (boxIco ι) = 1 := by
  rw [volume_pi_pi]
  simp [Real.volume_Ico]

theorem fundamentalDomain_eq_preimage (e : Module.Basis ι ℝ V) :
    ZSpan.fundamentalDomain e = e.equivFunL ⁻¹' boxIco ι := by
  ext x
  simp [ZSpan.mem_fundamentalDomain, boxIco, Set.mem_pi]

theorem integral_fundamentalDomain_eq (e : Module.Basis ι ℝ V) (H : V → ℂ) :
    ∫ y in ZSpan.fundamentalDomain e, H y =
      (volume.real (ZSpan.fundamentalDomain e) : ℂ) * ∫ t in boxIco ι, H (e.equivFunL.symm t) := by
  let ψ : V ≃ᵐ (ι → ℝ) := e.equivFunL.toHomeomorph.toMeasurableEquiv
  have hψ : (ψ : V → ι → ℝ) = e.equivFunL := rfl
  set ν : Measure (ι → ℝ) := Measure.map ψ (volume : Measure V) with hνdef
  haveI : ν.IsAddHaarMeasure := by
    rw [hνdef, hψ]; exact e.equivFunL.isAddHaarMeasure_map volume
  have hν : ν = ν.addHaarScalarFactor volume • volume := Measure.isAddLeftInvariant_eq_smul ν volume
  have hbox : ν (boxIco ι) = volume (ZSpan.fundamentalDomain e) := by
    rw [hνdef, MeasurableEquiv.map_apply, hψ, fundamentalDomain_eq_preimage]
  have hc : ((ν.addHaarScalarFactor volume : ℝ≥0) : ℝ≥0∞) = volume (ZSpan.fundamentalDomain e) := by
    rw [← hbox]
    conv_rhs => rw [hν]
    simp [volume_boxIco]
  have hint : ∫ y in ZSpan.fundamentalDomain e, H y = ∫ t in boxIco ι, H (e.equivFunL.symm t) ∂ν := by
    rw [hνdef, MeasurableEquiv.restrict_map, integral_map_equiv, fundamentalDomain_eq_preimage]
    simp only [hψ, ContinuousLinearEquiv.symm_apply_apply]
  rw [hint, hν, Measure.restrict_smul, integral_smul_nnreal_measure, measureReal_def, ← hc,
    ENNReal.coe_toReal, NNReal.smul_def, Complex.real_smul]

end Formalism.H
end
end

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.GaussSchwartz
section
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem schwartz_decay_gaussian : SchwartzDecay V := by
  intro f b
  refine ⟨f.isBigO_cocompact_rpow (-b), ?_⟩
  have h := (FourierTransform.fourier f : 𝓢(V, ℂ)).isBigO_cocompact_rpow (-b)
  rwa [SchwartzMap.fourier_coe] at h

end Formalism.H
end
end

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.InnerDualVecBasis
section
open MeasureTheory Filter Complex
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem innerₗ_nondegenerate : (innerₗ V : LinearMap.BilinForm ℝ V).Nondegenerate := by
  constructor <;> intro m hm <;> simpa using hm m

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev dualB (e : Module.Basis ι ℝ V) : Module.Basis ι ℝ V :=
  LinearMap.BilinForm.dualBasis (innerₗ V) innerₗ_nondegenerate e

theorem inner_dualB (e : Module.Basis ι ℝ V) (i j : ι) :
    ⟪dualB e i, e j⟫ = if j = i then 1 else 0 := by
  have h := LinearMap.BilinForm.apply_dualBasis_left (innerₗ_nondegenerate (V := V)) e i j
  simpa using h

def dualVec (e : Module.Basis ι ℝ V) (m : ι → ℤ) : V := ∑ i, m i • dualB e i

theorem dualVec_eq (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m = ∑ i, (m i : ℝ) • dualB e i := by
  unfold dualVec
  exact Finset.sum_congr rfl fun i _ => (Int.cast_smul_eq_zsmul ℝ (m i) _).symm

theorem inner_dualVec_basis (e : Module.Basis ι ℝ V) (m : ι → ℤ) (j : ι) :
    ⟪dualVec e m, e j⟫ = m j := by
  rw [dualVec_eq, sum_inner]
  simp_rw [real_inner_smul_left, inner_dualB]
  simp

theorem dual_span_eq (e : Module.Basis ι ℝ V) :
    dual (Submodule.span ℤ (Set.range e)) = Submodule.span ℤ (Set.range (dualB e)) := by
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ V) innerₗ_nondegenerate e

theorem dualVec_mem (e : Module.Basis ι ℝ V) (m : ι → ℤ) :
    dualVec e m ∈ dual (Submodule.span ℤ (Set.range e)) := by
  rw [dual_span_eq]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem dualVec_injective (e : Module.Basis ι ℝ V) : Function.Injective (dualVec e) := by
  intro m n h
  funext j
  have h1 := congrArg (fun x => ⟪x, e j⟫) h
  simp only [inner_dualVec_basis] at h1
  exact_mod_cast h1

theorem dualVec_surjective (e : Module.Basis ι ℝ V) (μ : V)
    (hμ : μ ∈ dual (Submodule.span ℤ (Set.range e))) : ∃ m, dualVec e m = μ := by
  rw [dual_span_eq] at hμ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hμ
  exact ⟨c, hc⟩

def dualEquiv (e : Module.Basis ι ℝ V) : (ι → ℤ) ≃ dual (Submodule.span ℤ (Set.range e)) :=
  Equiv.ofBijective (fun m => ⟨dualVec e m, dualVec_mem e m⟩)
    ⟨fun m n h => dualVec_injective e (congrArg Subtype.val h),
     fun μ => by
      obtain ⟨m, hm⟩ := dualVec_surjective e μ μ.2
      exact ⟨m, Subtype.ext hm⟩⟩

end Formalism.H
end
end

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.LatticeSummableDecay
section
open MeasureTheory Filter Asymptotics Topology

noncomputable section

namespace Formalism.H

theorem lattice_summable_decay (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : LatticeSummableDecay V := by
  intro L _ _ g b hb hg
  obtain ⟨C, hC⟩ := hg.bound
  have hrank : Module.finrank ℤ L = Module.finrank ℝ V := ZLattice.rank ℝ L
  have hsum : Summable fun z : L => ‖z‖ ^ (-b) :=
    ZLattice.summable_norm_rpow L (-b) (by rw [hrank]; linarith)
  have ht : Tendsto (Subtype.val : L → V) cofinite (cocompact V) :=
    L.toAddSubgroup.tendsto_coe_cofinite_of_isDiscrete
      (isDiscrete_iff_discreteTopology.mpr inferInstance)
  refine Summable.of_norm_bounded_eventually (hsum.mul_left C) ?_
  filter_upwards [ht.eventually hC] with z hz
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hz
  exact hz

end Formalism.H
end
end

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.Periodization
section
open MeasureTheory Filter Asymptotics Complex Metric
open scoped RealInnerProductSpace

noncomputable section

namespace Formalism.H

namespace PoissonPeriodization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

lemma exists_global_bound {f : V → ℂ} (hf : Continuous f) {b : ℝ} (hb : 0 ≤ b)
    (hO : f =O[cocompact V] (fun v => ‖v‖ ^ (-b))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖f v‖ ≤ C * (1 + ‖v‖) ^ (-b) := by
  obtain ⟨c, hc⟩ := hO.bound
  first
    | rw [← cobounded_eq_cocompact] at hc
    | rw [← Metric.cobounded_eq_cocompact] at hc
  rw [← comap_norm_atTop, Filter.eventually_comap, Filter.eventually_atTop] at hc
  obtain ⟨r, hr⟩ := hc
  set r' := max r 1 with hr'
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : V) r').exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max (M * (1 + r') ^ b) (|c| * 2 ^ b), by positivity, fun v => ?_⟩
  by_cases hv : ‖v‖ ≤ r'
  · have h1 := hM v (by simpa using hv)
    have hpos : 0 < 1 + ‖v‖ := by positivity
    have hr1 : 0 < 1 + r' := by
      have : 1 ≤ r' := le_max_right _ _
      linarith
    have hone : 1 ≤ (1 + r') ^ b * (1 + ‖v‖) ^ (-b) := by
      rw [Real.rpow_neg hpos.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hpos b)]
      exact Real.rpow_le_rpow hpos.le (by linarith) hb
    calc ‖f v‖ ≤ M := h1
      _ ≤ M * ((1 + r') ^ b * (1 + ‖v‖) ^ (-b)) :=
          le_mul_of_one_le_right (le_trans (norm_nonneg _) h1) hone
      _ = M * (1 + r') ^ b * (1 + ‖v‖) ^ (-b) := by ring
      _ ≤ max (M * (1 + r') ^ b) (|c| * 2 ^ b) * (1 + ‖v‖) ^ (-b) := by
          gcongr
          exact le_max_left _ _
  · push_neg at hv
    have hv1 : 1 ≤ ‖v‖ := le_trans (le_max_right _ _) hv.le
    have hb' := hr ‖v‖ (le_trans (le_max_left _ _) hv.le) v rfl
    have hvpos : 0 < ‖v‖ := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] at hb'
    have hk : ‖v‖ ^ (-b) ≤ 2 ^ b * (1 + ‖v‖) ^ (-b) := by
      rw [Real.rpow_neg hvpos.le, Real.rpow_neg (by positivity),
        le_mul_inv_iff₀ (Real.rpow_pos_of_pos (by positivity) b),
        inv_mul_le_iff₀ (Real.rpow_pos_of_pos hvpos b),
        ← Real.mul_rpow hvpos.le (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hb
    have hnn : 0 ≤ ‖v‖ ^ (-b) := Real.rpow_nonneg (norm_nonneg _) _
    calc ‖f v‖ ≤ c * ‖v‖ ^ (-b) := hb'
      _ ≤ |c| * ‖v‖ ^ (-b) := mul_le_mul_of_nonneg_right (le_abs_self c) hnn
      _ ≤ |c| * (2 ^ b * (1 + ‖v‖) ^ (-b)) := mul_le_mul_of_nonneg_left hk (abs_nonneg c)
      _ = |c| * 2 ^ b * (1 + ‖v‖) ^ (-b) := by ring
      _ ≤ max (M * (1 + r') ^ b) (|c| * 2 ^ b) * (1 + ‖v‖) ^ (-b) := by
          gcongr
          exact le_max_right _ _

lemma shift_bound {b : ℝ} (hb : 0 ≤ b) {R : ℝ} (hR : 0 ≤ R) (y x : V) (hx : ‖x‖ ≤ R) :
    (1 + ‖y + x‖) ^ (-b) ≤ (1 + R) ^ b * (1 + ‖y‖) ^ (-b) := by
  have h1 : 0 < 1 + ‖y + x‖ := by positivity
  have h2 : 0 < 1 + ‖y‖ := by positivity
  have h3 : 0 < 1 + R := by linarith
  have key : 1 + ‖y‖ ≤ (1 + ‖y + x‖) * (1 + R) := by
    have hyx : ‖y‖ ≤ ‖y + x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y + x) - x‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖y + x‖ + ‖x‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (y + x)]
  have key' : (1 + ‖y‖) ^ b ≤ ((1 + ‖y + x‖) * (1 + R)) ^ b := Real.rpow_le_rpow h2.le key hb
  rw [Real.mul_rpow h1.le h3.le] at key'
  have hA := Real.rpow_pos_of_pos h1 b
  have hB := Real.rpow_pos_of_pos h2 b
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, le_mul_inv_iff₀ hB, inv_mul_le_iff₀ hA]
  exact key'

lemma summable_one_add_norm (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {b : ℝ} (hb : (Module.finrank ℝ V : ℝ) < b) :
    Summable (fun l : Λ => (1 + ‖(l : V)‖) ^ (-b)) := by
  classical
  have hb0 : 0 < b := lt_of_le_of_lt (Nat.cast_nonneg _) hb
  have hr : -b < -(Module.finrank ℤ Λ : ℝ) := by
    rw [ZLattice.rank ℝ Λ]
    linarith
  have hs := ZLattice.summable_norm_rpow Λ (-b) hr
  refine Summable.of_nonneg_of_le (fun l => by positivity) (fun l => ?_)
    (hs.add (hasSum_ite_eq (0 : Λ) (1 : ℝ)).summable)
  by_cases h : l = 0
  · subst h
    simp only [if_pos rfl, ZeroMemClass.coe_zero, norm_zero, add_zero, Real.one_rpow, if_true, ↓reduceIte]
    linarith [Real.rpow_nonneg (le_refl (0 : ℝ)) (-b)]
  · have hl : 0 < ‖(l : V)‖ := norm_pos_iff.mpr (by simpa using h)
    rw [if_neg h, add_zero]
    show (1 + ‖(l : V)‖) ^ (-b) ≤ ‖(l : V)‖ ^ (-b)
    rw [Real.rpow_neg (by positivity), Real.rpow_neg hl.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hl b) (Real.rpow_le_rpow hl.le (by linarith) hb0.le)

end PoissonPeriodization

open PoissonPeriodization in
theorem poisson_periodization (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : Periodization V := by
  unfold Periodization
  intro Λ _ _ f hf b hb hO
  have hb0 : 0 ≤ b := le_trans (Nat.cast_nonneg _) hb.le
  obtain ⟨C, hC0, hC⟩ := exists_global_bound hf hb0 hO
  have hS := summable_one_add_norm Λ hb
  have hbound : ∀ (R : ℝ), 0 ≤ R → ∀ (l : Λ) (x : V), ‖x‖ ≤ R →
      ‖f (↑l + x)‖ ≤ C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b) := by
    intro R hR l x hx
    calc ‖f (↑l + x)‖ ≤ C * (1 + ‖(l : V) + x‖) ^ (-b) := hC _
      _ ≤ C * ((1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b)) :=
          mul_le_mul_of_nonneg_left (shift_bound hb0 hR (l : V) x hx) hC0
      _ = C * (1 + R) ^ b * (1 + ‖(l : V)‖) ^ (-b) := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ((integrable_one_add_norm hb).const_mul C).mono' hf.aestronglyMeasurable ?_
    exact ae_of_all _ (fun v => hC v)
  · intro x
    first
      | exact Summable.of_norm_bounded (hS.mul_left (C * (1 + ‖x‖) ^ b))
          (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)
      | exact Summable.of_norm_bounded _ (hS.mul_left (C * (1 + ‖x‖) ^ b))
          (fun l => hbound ‖x‖ (norm_nonneg _) l x le_rfl)
  · refine continuous_iff_continuousAt.mpr (fun x₀ => ?_)
    have hcont : ContinuousOn (fun x => ∑' l : Λ, f (↑l + x)) (Metric.ball (0 : V) (‖x₀‖ + 1)) := by
      refine continuousOn_tsum (fun l => (hf.comp (continuous_const.add continuous_id)).continuousOn)
        (hS.mul_left (C * (1 + (‖x₀‖ + 1)) ^ b)) ?_
      intro l x hx
      exact hbound (‖x₀‖ + 1) (by positivity) l x (by simpa using (Metric.mem_ball.mp hx).le)
    exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))
  · intro l₀ x
    have h := (Equiv.addRight l₀).tsum_eq (fun l : Λ => f (↑l + x))
    simp only [Equiv.coe_addRight, Submodule.coe_add, add_assoc] at h
    exact h

end Formalism.H
end
end

-- bundled from Formalism.LatticeTheta.LatticeThetaProofs.UnfoldCoeff
section
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap

noncomputable section

namespace Formalism.H

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

lemma unfoldCoeff_char_periodic (Λ : Submodule ℤ V) {μ : V} (hμ : μ ∈ dual Λ) (l : Λ) (y : V) :
    Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, (l : V) + y⟫ : ℝ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) := by
  obtain ⟨k, hk⟩ := Submodule.mem_one.1 ((LinearMap.BilinForm.mem_dualSubmodule _).1 hμ l l.2)
  have hk' : ⟪μ, (l : V)⟫ = (k : ℝ) := by simpa using hk.symm
  rw [inner_add_right, hk']
  push_cast
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) + (⟪μ, y⟫ : ℂ))) =
      -(2 * (Real.pi : ℂ) * Complex.I * (⟪μ, y⟫ : ℂ)) + -(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_add, ← Int.cast_neg, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem unfoldCoeff_main (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (f : V → ℂ)
    (hf : Integrable f) (D : Set V) (hD : IsAddFundamentalDomain Λ D volume) (μ : V)
    (hμ : μ ∈ dual Λ) :
    ∫ y in D, (∑' l : Λ, f ((l : V) + y)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ := by
  haveI : VAddInvariantMeasure Λ V volume := ⟨fun l s _ => measure_preimage_add volume (l : V) s⟩
  set e : V → ℂ := fun x => Complex.exp (-(2 * Real.pi * Complex.I * (⟪μ, x⟫ : ℝ))) with he
  have hper : ∀ (l : Λ) (y : V), e ((l : V) + y) = e y := fun l y =>
    unfoldCoeff_char_periodic Λ hμ l y
  have hcont : Continuous e := by fun_prop
  have hnorm : ∀ x, ‖e x‖ = 1 := by
    intro x
    simp only [he, Complex.norm_exp]
    simp
  set g : V → ℂ := fun x => f x * e x with hg
  have hgi : Integrable g :=
    Integrable.mono' hf.norm (hf.aestronglyMeasurable.mul hcont.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by simp only [hg, norm_mul, hnorm, mul_one, le_refl])
  have hL : ∀ y, (∑' l : Λ, f ((l : V) + y)) * e y = ∑' l : Λ, g ((l : V) + y) := by
    intro y
    rw [← tsum_mul_right]
    refine tsum_congr fun l => ?_
    simp only [hg, hper]
  show ∫ y in D, (∑' l : Λ, f ((l : V) + y)) * e y = (𝓕 f : V → ℂ) μ
  simp_rw [hL]
  have h1 : (∑' l : Λ, ∫⁻ y in D, ‖g ((l : V) + y)‖ₑ) = ∫⁻ x, ‖g x‖ₑ :=
    (hD.lintegral_eq_tsum'' (fun x => ‖g x‖ₑ)).symm
  have hfin : (∑' l : Λ, ∫⁻ y in D, ‖g ((l : V) + y)‖ₑ) ≠ ⊤ := by
    rw [h1]
    exact hgi.2.ne
  have h2 : (∑' l : Λ, ∫ y in D, g ((l : V) + y)) = ∫ x, g x :=
    (hD.integral_eq_tsum'' g hgi).symm
  rw [integral_tsum (fun l : Λ => (hgi.comp_add_left (l : V)).aestronglyMeasurable.restrict) hfin, h2,
    Real.fourier_eq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hg, he, smul_eq_mul]
  rw [mul_comm (f x), real_inner_comm μ x]
  congr 2
  push_cast
  ring

theorem unfolding_fourier_coefficient (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] : UnfoldCoeff V := by
  intro Λ _ _ f hf D hD μ hμ
  exact unfoldCoeff_main Λ f hf D hD μ hμ

end Formalism.H
end
end

