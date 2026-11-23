module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsZhangLowerX
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0080

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuMeasureLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem ptsIntegral_div_two {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ}
    (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral (e := e) P φ (fun z => g z / 2) = ptsIntegral (e := e) P φ g / 2 := by
  classical
  let m : ℝ ≃+ ℝ :=
    { toFun := fun x => x / 2, invFun := fun x => 2 * x, left_inv := fun x => by ring,
      right_inv := fun x => by ring, map_add' := fun x y => add_div x y 2 }
  have hhalf : ∀ (s : Set (((k : K) → ι k) → ℂ)) (F : (((k : K) → ι k) → ℂ) → ℝ),
      ∑ᶠ w ∈ s, F w / 2 = (∑ᶠ w ∈ s, F w) / 2 := by
    intro s F
    show ∑ᶠ w, ∑ᶠ (_ : w ∈ s), m (F w) = m (∑ᶠ w, ∑ᶠ (_ : w ∈ s), F w)
    rw [m.map_finsum]
    congr 1
    funext w
    rw [m.map_finsum]
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_div]
    congr 1
    funext y
    have hs : ∀ w, sheetDensity P hΨ.choose φ (fun z => g z / 2) y w =
        sheetDensity P hΨ.choose φ g y w / 2 := by
      intro w
      unfold sheetDensity
      split_ifs <;> ring
    simp only [hs]
    exact hhalf _ _
  · simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PNbarSemipos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem NbarSemipos.proof (h : NbarChartSemipos.Statement) : NbarSemipos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp _
  obtain ⟨c, hc, hX⟩ := h II Ψ K ι Ω E D O Lt X
  have hpc : 0 < (p : ℝ) * c := mul_pos (by exact_mod_cast hp) hc
  have hlim : Tendsto (fun t => (q : ℝ) * (4 * X.S.Cη * X.S.e1 t)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (X.S_tied.e1_tendsto_zero.const_mul (4 * X.S.Cη)).const_mul (q : ℝ)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t) := by
    filter_upwards [X.S.eventually_chartLevi X.S_tied, hlim.eventually (eventually_le_nhds hpc)] with t ht hq
    exact hX B p q t _ ht.1 ht.2 hq
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hall
  exact ⟨u, hu, fun t ht0 ht1 => hsub ⟨ht0, ht1⟩⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsBddConv
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem PtsBddConv.maDensity_div_const {D : ℕ} (ψ : Fin D → (Fin D → ℂ) → ℝ) (r : ℝ) (z : Fin D → ℂ) :
    maDensity (fun j y => ψ j y / r) z = r⁻¹ ^ D * maDensity ψ z := by
  have hH : ∀ j, cxHessian (fun y => ψ j y / r) z = (((r⁻¹ : ℝ) : ℂ)) • cxHessian (ψ j) z := by
    intro j
    have h1 : (fun y => ψ j y / r) = r⁻¹ • ψ j := by
      funext y
      simp [div_eq_inv_mul]
    have h2 : fderiv ℝ (fderiv ℝ (fun y => ψ j y / r)) = r⁻¹ • fderiv ℝ (fderiv ℝ (ψ j)) := by
      rw [h1, fderiv_const_smul_field]
      exact fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ (ψ j)) r⁻¹
    ext a b
    simp only [cxHessian, h2, Pi.smul_apply, smul_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hS : ∀ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (fun y => ψ k y / r) z).det =
      ((r⁻¹ ^ D : ℝ) : ℂ) * ((-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) := by
    intro S
    simp only [hH, ← Finset.smul_sum, Matrix.det_smul, Fintype.card_fin]
    push_cast
    ring
  simp only [maDensity, mixedDisc, hS, ← Finset.mul_sum]
  rw [show (1 / (D.factorial : ℂ)) * (((r⁻¹ ^ D : ℝ) : ℂ) *
      ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) =
      ((r⁻¹ ^ D : ℝ) : ℂ) * ((1 / (D.factorial : ℂ)) *
      ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * (∑ k ∈ S, cxHessian (ψ k) z).det) by ring,
    Complex.re_ofReal_mul]
  ring

theorem PtsBddConv.proof (hAbs : Inter.PtsAbsIntegrable.Statement) : PtsBddConv.Statement := by
  intro K _ ι _ P e L r g g₀ N C s₀ hP hL hr hN hs₀ hg hlim
  classical

  have key : ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
      Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ y w) ∧
      Tendsto (fun s => ptsIntegralAt P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s)) (𝓝[>] 0)
        (𝓝 (ptsIntegralAt P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀)) := by
    intro Ψ hΨ
    have hfin : ∀ y, (ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y).Finite := fibreFinite K ι P e Ψ hP hΨ
    have hL' : ∀ j : Fin e, IsSmoothHerm ((fun _ => L) j) := fun _ => hL
    have hone : IsSectionOn P (oneLine (ι := ι)) 1 := by
      refine ⟨0, fun k => by simp [oneLine, HermLine.ofWeight], fun m hm k => ?_,
        fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
      rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp
    have hB := hAbs K ι P e Ψ (fun _ => L) oneLine 1 hP hΨ hL' isSmoothHerm_oneLine hone

    have hbd : ∀ (h : ((Σ k, ι k) → ℂ) → ℝ) y w, (∀ hγ : ∃ γ, IsSheet P Ψ y w γ, |h (hγ.choose y)| ≤ C) →
        |sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) h y w| ≤
          C * r⁻¹ ^ e * |sheetDensity P Ψ (pot fun _ => L) (logNorm oneLine 1) y w| := by
      intro h y w hh
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [sheetDensity, dif_pos hγ, logNorm_oneLine, one_mul, pot]
        rw [PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (hγ.choose y'))) r y, abs_mul, abs_mul,
          abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) e), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hh hγ)
          (pow_nonneg (inv_nonneg.mpr hr.le) e)) (abs_nonneg _)
      · simp only [sheetDensity, dif_neg hγ, abs_zero, mul_zero, le_refl]
    have hsum : ∀ (h : ((Σ k, ι k) → ℂ) → ℝ) y, (∀ w (hγ : ∃ γ, IsSheet P Ψ y w γ), |h (hγ.choose y)| ≤ C) →
        ‖∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) h y w‖ ≤
          C * r⁻¹ ^ e * ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, |sheetDensity P Ψ (pot fun _ => L) (logNorm oneLine 1) y w| := by
      intro h y hh
      rw [Real.norm_eq_abs, finsum_mem_eq_finite_toFinset_sum _ (hfin y),
        finsum_mem_eq_finite_toFinset_sum _ (hfin y), Finset.mul_sum]
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => hbd h y w (hh w))

    set S : Set (Fin e → ℂ) := {y | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} with hSdef
    have hS : volume S = 0 := hN Ψ hΨ
    have hSae : ∀ᵐ y, y ∉ S := measure_eq_zero_iff_ae_notMem.mp hS
    have hpt : ∀ y w (hγ : ∃ γ, IsSheet P Ψ y w γ), hγ.choose y ∈ mcPts P ∧ Ψ (segre (hγ.choose y)) = Fin.cons 1 y :=
      fun y w hγ => ⟨hγ.choose_spec.2.self_of_nhds.2.1, hγ.choose_spec.2.self_of_nhds.2.2⟩
    have hoff : ∀ y ∉ S, ∀ w (hγ : ∃ γ, IsSheet P Ψ y w γ), hγ.choose y ∉ N :=
      fun y hy w hγ hz => hy ⟨_, (hpt y w hγ).1, hz, (hpt y w hγ).2⟩

    have hmeas : ∀ s, 0 < s → s < s₀ → AEStronglyMeasurable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s) y w) volume := by
      intro s hs hs1
      obtain ⟨-, hgc, hgt⟩ := hg s hs hs1
      set M := toMeasurable volume S with hMdef
      have hMm : MeasurableSet M := measurableSet_toMeasurable _ _
      have hSM : S ⊆ M := subset_toMeasurable _ _
      have hM0 : volume M = 0 := by rw [hMdef, measure_toMeasurable]; exact hS
      obtain ⟨g', hg'⟩ : ∃ g' : ((Σ k, ι k) → ℂ) → ℝ, ∀ z,
          g' z = if ∃ y ∈ M, Ψ (segre z) = Fin.cons 1 y then 0 else g s z := ⟨_, fun _ => rfl⟩
      obtain ⟨B, γ, hBo, hlift, hcov⟩ := PtsSumMeasurable.exists_lift_family (P := P) (Ψ := Ψ) hfin
      have hγc : ∀ m, ContinuousOn (γ m) (B m) := fun m y hy =>
        (hlift m y hy).1.continuousAt.continuousWithinAt
      have hcons : ∀ {y y' : Fin e → ℂ}, (Fin.cons 1 y : Fin (e + 1) → ℂ) = Fin.cons 1 y' → y = y' := by
        intro y y' h
        simpa using congrArg Fin.tail h
      set v : ℕ → (Fin e → ℂ) → ℝ := fun m => (B m \ M).piecewise (fun y => g s (γ m y)) 0 with hvdef
      have hvm : ∀ m, Measurable (v m) := by
        intro m
        refine ContinuousOn.measurable_piecewise ?_ continuousOn_const ((hBo m).measurableSet.diff hMm)
        refine hgc.comp ((hγc m).mono Set.sdiff_subset) fun y hy => ⟨(hlift m y hy.1).2.1, fun hz => ?_⟩
        exact hy.2 (hSM ⟨_, (hlift m y hy.1).2.1, hz, (hlift m y hy.1).2.2⟩)
      have hind0 := sheetIndep K ι P e Ψ (fun _ => L) oneLine 1 hP hΨ hL' isSmoothHerm_oneLine hone
      have hae := PtsSumMeasurableWeight.aestronglyMeasurable_fibreSum_of_lifts
        (fun (_ : Fin e) z => Real.log (L.h z) / r) g' id measurable_id rfl hfin B γ hBo hlift hcov
        (fun m y => v m y * maDensity (fun j y' => (fun (_ : Fin e) z => Real.log (L.h z) / r) j (γ m y')) y)
        (fun m => (hvm m).mul (PtsSumMeasurable.measurable_maDensity _))
        (fun m y hy => by
          rw [hg']
          simp only [hvdef]
          by_cases hyM : y ∈ M
          · rw [if_pos ⟨y, hyM, (hlift m y hy).2.2⟩,
              Set.piecewise_eq_of_notMem _ _ _ (fun h : y ∈ B m \ M => h.2 hyM)]
            simp
          · have hne : ¬ ∃ y' ∈ M, Ψ (segre (γ m y)) = Fin.cons 1 y' := by
              rintro ⟨y', hy'M, h⟩
              obtain rfl := hcons (((hlift m y hy).2.2).symm.trans h)
              exact hyM hy'M
            rw [if_neg hne, Set.piecewise_eq_of_mem (B m \ M) _ _ (Set.mem_sdiff_of_mem hy hyM)])
        (by
          filter_upwards [hind0] with y hy w γ₁ γ₂ h₁ h₂
          have hd := hy w γ₁ γ₂ h₁ h₂
          simp only [logNorm_oneLine, one_mul, pot] at hd
          have hm₁ : γ₁ y ∈ mcPts P := h₁.2.self_of_nhds.2.1
          have hm₂ : γ₂ y ∈ mcPts P := h₂.2.self_of_nhds.2.1
          have hseg : segre (γ₁ y) = segre (γ₂ y) := h₁.1.trans h₂.1.symm
          choose i0 hi0 using hm₁.1
          obtain ⟨hc0, hc⟩ := eq_bsmul_of_segre_eq i0 hi0 hseg
          have hgg : g s (γ₂ y) = g s (γ₁ y) := by
            rw [hc]
            exact hgt _ (fun k => div_ne_zero (hc0 k) (hi0 k)) _ hm₁
          rw [PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (γ₁ y'))) r y,
            PtsBddConv.maDensity_div_const (fun _ y' => Real.log (L.h (γ₂ y'))) r y, hd, hg', hg', hseg, hgg])
      refine hae.congr ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hM0] with y hy
      refine finsum_mem_congr rfl fun w _ => ?_
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [id, sheetDensity, dif_pos hγ]
        have hne : ¬ ∃ y' ∈ M, Ψ (segre (hγ.choose y)) = Fin.cons 1 y' := by
          rintro ⟨y', hy'M, h⟩
          obtain rfl := hcons ((hpt y w hγ).2.symm.trans h)
          exact hy hy'M
        rw [hg', if_neg hne]
      · simp only [id, sheetDensity, dif_neg hγ]

    have hlimpt : ∀ᵐ y, Tendsto (fun s => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
        sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s) y w) (𝓝[>] 0)
        (𝓝 (∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ y w)) := by
      filter_upwards [hSae] with y hy
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
      simp only [finsum_mem_eq_finite_toFinset_sum _ (hfin y)]
      refine tendsto_finsetSum _ fun w _ => ?_
      by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
      · simp only [sheetDensity, dif_pos hγ]
        exact (hlim _ (hpt y w hγ).1 (hoff y hy w hγ)).mul_const _
      · simp only [sheetDensity, dif_neg hγ]
        exact tendsto_const_nhds
    have hbound := hB.const_mul (C * r⁻¹ ^ e)

    have hg₀ : ∀ z ∈ mcPts P, z ∉ N → |g₀ z| ≤ C := fun z hz hzN =>
      le_of_tendsto ((continuous_abs.tendsto _).comp (hlim z hz hzN))
        (by filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs using (hg s hs.1 hs.2).1 z hz)
    set u : ℕ → ℝ := fun n => s₀ / 2 * (1 / ((n : ℝ) + 1)) with hudef
    have hupos : ∀ n, 0 < u n := fun n => by positivity
    have hult : ∀ n, u n < s₀ := fun n => by
      have : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      calc u n ≤ s₀ / 2 * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ < s₀ := by linarith
    have hu : Tendsto u atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hupos⟩
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (s₀ / 2)
      rw [mul_zero] at h
      exact h
    have hmeas₀ := aestronglyMeasurable_of_tendsto_ae atTop (fun n => hmeas (u n) (hupos n) (hult n))
      (by filter_upwards [hlimpt] with y hy using hy.comp hu)
    refine ⟨hbound.mono' hmeas₀ ?_, ?_⟩
    · filter_upwards [hSae] with y hy
      exact hsum g₀ y fun w hγ => hg₀ _ (hpt y w hγ).1 (hoff y hy w hγ)
    · refine tendsto_integral_filter_of_dominated_convergence _
        (by filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs using hmeas s hs.1 hs.2) ?_ hbound hlimpt
      filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      exact Eventually.of_forall fun y => hsum (g s) y fun w hγ => (hg s hs.1 hs.2).1 _ (hpt y w hγ).1
  refine ⟨fun Ψ hΨ => (key Ψ hΨ).1, ?_⟩
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  · simp only [dif_pos hΨ]
    exact (key _ hΨ.choose_spec).2
  · simp only [dif_neg hΨ]
    exact tendsto_const_nhds

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitEps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace StokesLimitEps

open Matrix

theorem coeff_tendsto {N : ℕ} (c : ℕ → ℝ → ℝ) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ)
    (hf : ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ), f q t = ∑ i ∈ Finset.range N, c i t * (1 / (q : ℝ)) ^ i)
    (hg : ∀ q : ℕ, 1 ≤ q → Tendsto (f q) (𝓝[>] 0) (𝓝 (g q))) :
    ∃ ℓ : ℕ → ℝ, (∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i))) ∧
      ∀ q : ℕ, 1 ≤ q → g q = ∑ i ∈ Finset.range N, ℓ i * (1 / (q : ℝ)) ^ i := by

  let x : Fin N → ℝ := fun j => 1 / (((j : ℕ) + 1 : ℕ) : ℝ)
  have hinj : Function.Injective x := by
    intro j k h
    simp only [x, one_div, _root_.inv_inj, Nat.cast_inj] at h
    exact Fin.ext (by omega)
  have hdet : IsUnit (Matrix.vandermonde x).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_vandermonde_ne_zero_iff]
    exact hinj
  let F : ℝ → Fin N → ℝ := fun t j => f ((j : ℕ) + 1) t

  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun i : Fin N => c i t) = (Matrix.vandermonde x)⁻¹ *ᵥ F t := by
    filter_upwards [Filter.eventually_all.2 fun j : Fin N => hf ((j : ℕ) + 1) (by omega)] with t ht
    have hval : F t = Matrix.vandermonde x *ᵥ fun i : Fin N => c i t := by
      funext j
      simp only [F, ht j, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, x]
      rw [← Fin.sum_univ_eq_sum_range (fun i => c i t * (1 / (((j : ℕ) + 1 : ℕ) : ℝ)) ^ i)]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hF : Tendsto F (𝓝[>] 0) (𝓝 fun j : Fin N => g ((j : ℕ) + 1)) :=
    tendsto_pi_nhds.2 fun j => hg _ (by omega)
  have hC : Tendsto (fun t => fun i : Fin N => c i t) (𝓝[>] 0)
      (𝓝 ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1))) :=
    (((continuous_const.matrix_mulVec continuous_id).tendsto _).comp hF).congr' (hev.mono fun t ht => ht.symm)
  let ℓ : ℕ → ℝ := fun i => if h : i < N then
    ((Matrix.vandermonde x)⁻¹ *ᵥ fun j : Fin N => g ((j : ℕ) + 1)) ⟨i, h⟩ else 0
  have hℓ : ∀ i < N, Tendsto (c i) (𝓝[>] 0) (𝓝 (ℓ i)) := by
    intro i hi
    simpa only [ℓ, dif_pos hi] using tendsto_pi_nhds.1 hC ⟨i, hi⟩
  refine ⟨ℓ, hℓ, fun q hq => tendsto_nhds_unique (hg q hq) ?_⟩
  refine Tendsto.congr' ((hf q hq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun i hi => (hℓ i (Finset.mem_range.1 hi)).mul_const _

theorem tendsto_const_coeff {N : ℕ} (ℓ : ℕ → ℝ) (hN : 1 ≤ N) :
    Tendsto (fun m : ℕ => ∑ i ∈ Finset.range N, ℓ i * (1 / ((m + 1 : ℕ) : ℝ)) ^ i) atTop (𝓝 (ℓ 0)) := by
  have h0 : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hs := tendsto_finsetSum (Finset.range N) fun i _ => (h0.pow i).const_mul (ℓ i)
  have e : ∑ i ∈ Finset.range N, ℓ i * (0 : ℝ) ^ i = ℓ 0 := by
    rw [Finset.sum_eq_single 0 (fun b _ hb => by simp [zero_pow hb])
      (fun h => absurd (Finset.mem_range.2 hN) h)]
    simp
  rwa [e] at hs

end StokesLimitEps

theorem StokesLimitEps.proof (hT : StokesLimitT.Statement) (hTop : TopNPoly.Statement)
    (hOm : OmNPoly.Statement) (hMu : MuMeasureLimit.Statement) : StokesLimitEps.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII hAr
  have hTq := fun q (hq : 1 ≤ q) => hT II Ψ K ι Ω E D O Lt X B 1 q hII hAr le_rfl hq
  obtain ⟨c, hc0, hc⟩ := hTop II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨v, d, hv0, hd0, hvd⟩ := hOm II Ψ K ι Ω E D O Lt X B hII hAr
  obtain ⟨hmuV, hmuD⟩ := hMu II Ψ K ι Ω E D O Lt X B hII hAr
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto c (fun q => X.topN B 1 q) (X.topNLim B 1) hc
      fun q hq => (hTq q hq).1
    have h0 : ℓ 0 = arLim X.H X.S B := by
      obtain ⟨L, hL⟩ := hAr
      have e1 : arLim X.H X.S B = L := by unfold arLim; exact hL.limUnder_eq
      have h := hℓ 0 (by omega)
      rw [hc0] at h
      rw [e1]; exact tendsto_nhds_unique h hL
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 2) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto v (fun q => X.Vb B 1 q) (X.VbLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.1) fun q hq => (hTq q hq).2.1
    have h0 : ℓ 0 = meanU X.H X.Cd * degMu X.H / 2 := by
      have h := hℓ 0 (by omega)
      rw [hv0] at h
      exact tendsto_nhds_unique h hmuV
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm
  · obtain ⟨ℓ, hℓ, hg⟩ := StokesLimitEps.coeff_tendsto d (fun q => X.degN B 1 q) (X.degNLim B 1)
      (fun q hq => (hvd q hq).mono fun t h => h.2) fun q hq => (hTq q hq).2.2
    have h0 : ℓ 0 = degMu X.H := by
      have h := hℓ 0 (by omega)
      rw [hd0] at h
      exact tendsto_nhds_unique h hmuD
    rw [← h0]
    exact (StokesLimitEps.tendsto_const_coeff ℓ (N := D.n + 1) (by omega)).congr fun m =>
      (hg (m + 1) (by omega)).symm

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitT
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem StokesLimitT.proof (hG : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement)
    (hNs : NbarSemipos.Statement) (hTop : StokesLimitTTop.Statement) (hVb : StokesLimitTVb.Statement) :
    StokesLimitT.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  refine ⟨tendsto_nhds_limUnder (hTop II Ψ K ι Ω E D O Lt X B p q hII hAr hp hpq),
    tendsto_nhds_limUnder (hVb II Ψ K ι Ω E D O Lt X B p q hp hpq), ?_⟩
  obtain ⟨t₁, ht₁, hN⟩ := hNs II Ψ K ι Ω E D O Lt X B p q hp hpq

  have ha : ∀ t : ℝ, (X.NbarQ B p q t).a = (X.NbarQ B p q t₁).a := by
    intro t
    simp only [ComponentSetting.NbarQ, smoothRep_a]
    rfl
  have hconst : ∀ᶠ t in 𝓝[>] (0 : ℝ), X.degN B p q t₁ = X.degN B p q t := by
    filter_upwards [Ioc_mem_nhdsGT ht₁] with t ht
    unfold ComponentSetting.degN
    rw [hG K ι Ω D.y D.n _ D.arith (hN t ht.1 ht.2).1, hG K ι Ω D.y D.n _ D.arith (hN t₁ ht₁ le_rfl).1, ha t]
  exact tendsto_nhds_limUnder ⟨_, tendsto_const_nhds.congr' hconst⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PZhangLowerX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo HilbertSamuel.CurvePointsFinite

theorem degC_pos_of_isArithVar_one {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {W : Ideal (MRing ι)} (hW : IsArithVar W 1) : 0 < degC W := by
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  rw [hdeg]
  exact Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩

theorem ZhangLowerX.proof (h : SuccessiveMinimaLowerBound) : ZhangLowerX.Statement := by
  intro K _ ι _ P P0 n A e II hII hP hP0 hs hnef hc hh
  refine h K ι P P0 n A e II hII hP hP0 hs hnef hc fun W hW hPW ↦ ?_
  have hd : (0 : ℝ) < degC W := Nat.cast_pos.2 (degC_pos_of_isArithVar_one hW)
  have h1 := hh W hW hPW
  rwa [IndefiniteRowSideFullHecke.HeightsSet.height, le_div_iff₀ hd] at h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBoundaryPtsNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def BoundaryPtsNull.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E),
    IsPtsNull (mCoordIdeal D.y) D.n D.Bd

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

