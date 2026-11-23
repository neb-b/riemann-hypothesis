module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Jointrep
section
open MeasureTheory Filter Topology
open scoped ENNReal

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Jointrep

theorem geom : (∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ j) ^ 2) ≠ ⊤ := by
  have h2 : (∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ j) ≠ ⊤ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  refine ne_top_of_le_ne_top h2 (ENNReal.tsum_le_tsum fun j => ?_)
  exact pow_le_of_le_one (by simp) (pow_le_one₀ (by simp) (ENNReal.inv_le_one.2 one_le_two)) two_ne_zero

theorem ae_tendsto {S : Type} [MeasurableSpace S] {ν : Measure S} (h : Lp ℂ 2 ν) (v : ℕ → Lp ℂ 2 ν)
    (hv : ∀ j, edist h (v j) < (2⁻¹ : ℝ≥0∞) ^ j) :
    ∀ᵐ s ∂ν, Tendsto (fun j => (v j : S → ℂ) s) atTop (𝓝 (h s)) := by
  let g : ℕ → S → ℝ≥0∞ := fun j s => ‖(v j : S → ℂ) s - h s‖ₑ ^ (2:ℝ)
  have gm : ∀ j, Measurable (g j) := fun j =>
    (((Lp.stronglyMeasurable (v j)).measurable.sub (Lp.stronglyMeasurable h).measurable).enorm).pow_const _
  have hint : ∀ j, ∫⁻ s, g j s ∂ν ≤ ((2⁻¹ : ℝ≥0∞) ^ j) ^ 2 := by
    intro j
    have e1 : ∫⁻ s, g j s ∂ν = eLpNorm' (fun s => (v j : S → ℂ) s - h s) 2 ν ^ (2:ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' two_pos
    have e2 : eLpNorm' (fun s => (v j : S → ℂ) s - h s) 2 ν = edist (v j) h := by
      rw [Lp.edist_def, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      · rfl
      · exact (Lp.stronglyMeasurable (v j)).aestronglyMeasurable.sub (Lp.stronglyMeasurable h).aestronglyMeasurable
    rw [e1, e2, ENNReal.rpow_two]
    gcongr
    rw [edist_comm]; exact (hv j).le
  have hsum : ∫⁻ s, ∑' j, g j s ∂ν ≠ ⊤ := by
    rw [lintegral_tsum fun j => (gm j).aemeasurable]
    exact ne_top_of_le_ne_top geom (ENNReal.tsum_le_tsum hint)
  filter_upwards [ae_lt_top (Measurable.tsum gm) hsum] with s hs
  have h0 : Tendsto (fun j => g j s) atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hs.ne
  have h1 : Tendsto (fun j => (g j s) ^ (2⁻¹ : ℝ)) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (2⁻¹:ℝ))).tendsto 0).comp h0
    simpa [Function.comp_def] using this
  rw [tendsto_iff_edist_tendsto_0]
  refine h1.congr fun j => ?_
  simp only [g, edist_eq_enorm_sub]
  rw [← ENNReal.rpow_mul]
  norm_num

end Jointrep

open Jointrep in
theorem jointrep : JointRep := by
  classical
  intro S _ ν _ _ _
  set u := TopologicalSpace.denseSeq (Lp ℂ 2 ν) with hu
  have hex : ∀ (j : ℕ) (h : Lp ℂ 2 ν), ∃ n, edist h (u n) < (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j h
    obtain ⟨y, ⟨n, rfl⟩, hy⟩ := EMetric.mem_closure_iff.1
      (TopologicalSpace.denseRange_denseSeq (Lp ℂ 2 ν) h) _
      (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp : (2 : ℝ≥0∞) ≠ ⊤)) j)
    exact ⟨n, hy⟩
  let N : ℕ → Lp ℂ 2 ν → ℕ := fun j h => Nat.find (hex j h)
  have hN : ∀ j, Measurable (N j) := fun j =>
    measurable_find (hex j) fun n => Metric.isOpen_eball.measurableSet
  refine ⟨fun h s => limUnder atTop (fun j => (u (N j h) : S → ℂ) s), ?_, fun h => ?_⟩
  · have hf : ∀ j, StronglyMeasurable (fun p : Lp ℂ 2 ν × S => (u (N j p.1) : S → ℂ) p.2) := by
      intro j
      have m : Measurable (fun q : S × ℕ => (u q.2 : S → ℂ) q.1) :=
        measurable_from_prod_countable_left fun n => (Lp.stronglyMeasurable (u n)).measurable
      exact (m.comp (measurable_snd.prodMk ((hN j).comp measurable_fst))).stronglyMeasurable
    exact (StronglyMeasurable.limUnder (l := atTop) hf).measurable
  · filter_upwards [ae_tendsto h (fun j => u (N j h)) fun j => Nat.find_spec (hex j h)] with s hs
    exact hs.limUnder_eq

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Locint
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.Rg.BcB.E2.P

namespace Locint

theorem enorm_le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x * 1 := (mul_one x).symm
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := (sq x).symm
      _ ≤ 1 + x ^ 2 := le_add_self

end Locint

theorem locint : Tonelli → LocInt := by
  intro hT X S _ ν _ F f hF hrep
  let K := CompactExhaustion.choice X.G
  have hfin : ∀ n, ∀ᵐ s ∂ν, ∫⁻ y, (K n).indicator 1 y * ‖f y s‖ₑ ^ 2 ∂X.μ < ⊤ := by
    intro n
    have hK : IsCompact (K n) := K.isCompact n
    have hW : Measurable ((K n).indicator (1 : X.G → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
    apply hT X.G S X.μ ν F f _ hrep hW
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
    refine ne_top_of_le_ne_top (b := ∫⁻ y, (K n).indicator (fun _ => ENNReal.ofReal C ^ 2) y ∂X.μ) ?_ ?_
    · rw [lintegral_indicator_const hK.measurableSet]
      exact ENNReal.mul_ne_top (by simp) hK.measure_lt_top.ne
    · refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ K n
      · simp only [Set.indicator_of_mem hy, Pi.one_apply, one_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC y hy)
      · simp [Set.indicator_of_notMem hy]
  rw [← ae_all_iff] at hfin
  filter_upwards [hfin] with s hs
  have hm : Measurable fun y => f y s := hrep.1.of_uncurry_right
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hk
  refine IntegrableOn.mono_set ?_ hn
  have hKn : IsCompact (K n) := K.isCompact n
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have heq : (fun y => (K n).indicator 1 y * ‖f y s‖ₑ ^ 2) = (K n).indicator (fun y => ‖f y s‖ₑ ^ 2) := by
    ext y; by_cases hy : y ∈ K n <;> simp [hy]
  have h2 := hs n
  rw [heq, lintegral_indicator hKn.measurableSet] at h2
  show ∫⁻ y, ‖f y s‖ₑ ∂(X.μ.restrict (K n)) < ⊤
  calc ∫⁻ y, ‖f y s‖ₑ ∂(X.μ.restrict (K n)) ≤ ∫⁻ y, (1 + ‖f y s‖ₑ ^ 2) ∂(X.μ.restrict (K n)) :=
        lintegral_mono fun y => Locint.enorm_le_one_add_sq _
    _ = X.μ (K n) + ∫⁻ y, ‖f y s‖ₑ ^ 2 ∂(X.μ.restrict (K n)) := by
        rw [lintegral_add_left measurable_const]; simp
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hKn.measure_lt_top, h2⟩

end PositivityTheory.Rg.BcB.E2.P

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.MulLeWeightedSquares
section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Fdata

lemma mul_le_weighted_squares (a b W : ℝ≥0∞) (h0 : W ≠ 0) (ht : W ≠ ⊤) : a * b ≤ W⁻¹ * a ^ 2 + W * b ^ 2 := by
  rcases le_or_gt a (W * b) with h | h
  · calc a * b ≤ W * b * b := by gcongr
      _ = W * b ^ 2 := by rw [pow_two, mul_assoc]
      _ ≤ _ := le_add_self
  · have hb : b ≤ W⁻¹ * a := by
      calc b = W⁻¹ * (W * b) := by rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
        _ ≤ W⁻¹ * a := by gcongr
    calc a * b ≤ a * (W⁻¹ * a) := by gcongr
      _ = W⁻¹ * a ^ 2 := by ring
      _ ≤ _ := le_self_add

end Fdata

theorem fdata : RowsEx → RowsEig → FData := by
  intro hRx hRe X ι _ K _ _ _ J B _ _ _ _ R a₀ Φ g W S _ ν _ χ V hJ hΦ hT hS hne hW hW' hWc hg hg'
  obtain ⟨T₁, hT₁, hT₁J⟩ := hT 1
  obtain ⟨k, hk⟩ := hRx X ι (Φ 1) T₁ (hΦ 1) hT₁
  set L : Lp ℂ 2 ν →L[ℂ] X.Hs ι := J.comp V with hL
  have hLn : ∀ h, ‖L h‖ = ‖h‖ := fun h => (hJ _).trans (hS.iso h)
  have hL1 : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by rw [hLn, one_mul]
  set A := ContinuousLinearMap.adjoint L with hA
  have hAn : ∀ v, ‖A v‖ ≤ ‖v‖ := fun v => by
    calc ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
      _ ≤ 1 * ‖v‖ := by
          gcongr
          rw [hA, LinearIsometryEquiv.norm_map]
          exact hL1
      _ = ‖v‖ := one_mul _
  have hAe : ∀ v, ‖A v‖ₑ ≤ ‖v‖ₑ := fun v => by
    rw [← ofReal_norm, ← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hAn v)
  have hin : ∀ v h, inner ℂ (A v) h = inner ℂ v (L h) := fun v h =>
    ContinuousLinearMap.adjoint_inner_left L h v
  have hT1L : ∀ h, T₁ (L h) = J (R a₀ (V h)) := fun h => by
    show T₁ (J (V h)) = _
    rw [hT₁J, one_mul]
  have hmem : ∀ b (h : Lp ℂ 2 ν), MemLp (fun s => χ s b * h s) 2 ν := fun b h =>
    MemLp.of_le_mul (c := ‖R b‖) (Lp.memLp h)
      ((hS.meas b).aestronglyMeasurable.mul (Lp.aestronglyMeasurable h))
      (Filter.Eventually.of_forall fun s => by rw [norm_mul]; gcongr; exact hS.bdd b s)
  have hwt : ∀ i, ∫⁻ x, W x * ‖A (k i x)‖ₑ ^ 2 ∂X.ν ≠ ⊤ := by
    intro i
    obtain ⟨C, Ω, hC, hΩ, hkC⟩ := hk.norm
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (hWc Ω hΩ)) ?_
    rw [← lintegral_const_mul' _ _ hC]
    refine lintegral_mono fun x => ?_
    calc W x * ‖A (k i x)‖ₑ ^ 2 ≤ W x * ‖k i x‖ₑ ^ 2 := by gcongr; exact hAe _
      _ ≤ W x * (C * cnt X.Γ Ω x) := by gcongr; exact hkC i x
      _ = C * (W x * cnt X.Γ Ω x) := by ring
  refine ⟨fun i x => A (k i x), ?_⟩
  refine ⟨fun i => A.continuous.comp (hk.cont i), fun i γ hγ x => by simp only [hk.inv i γ hγ x], ?_, hwt, ?_, ?_, ?_⟩
  ·
    intro hF0
    have hA0 : ∀ i x, A (k i x) = 0 := fun i x => congrFun (congrFun hF0 i) x
    have h0 : ∀ h, T₁ (L h) = 0 := fun h => by
      refine PiLp.ext fun i => ?_
      rw [PiLp.zero_apply]
      refine Lp.ext ?_
      filter_upwards [hk.rep (L h) i, Lp.coeFn_zero ℂ 2 X.ν] with x h1 h2
      rw [h1, h2, ← hin, hA0, inner_zero_left]
      rfl
    set h1 : Lp ℂ 2 ν := (memLp_const (1 : ℂ)).toLp _ with hh1
    set h' : Lp ℂ 2 ν := (hmem a₀ h1).toLp _ with hh'
    have hV : V h' = R a₀ (V h1) := hS.mul _ h1 _ (MemLp.coeFn_toLp _)
    have hJ0 : J (V h') = 0 := by rw [hV, ← hT1L, h0]
    have hn : ‖h'‖ = 0 := by rw [← hS.iso, ← hJ, hJ0, norm_zero]
    have hz : h' = 0 := norm_eq_zero.1 hn
    have hae : ∀ᵐ s ∂ν, False := by
      filter_upwards [hne, MemLp.coeFn_toLp (hmem a₀ h1), MemLp.coeFn_toLp (memLp_const (1 : ℂ) (μ := ν) (p := 2)),
        Lp.coeFn_zero ℂ 2 ν] with s hs e1 e2 e3
      apply hs
      have : (h' : S → ℂ) s = 0 := by rw [hz, e3]; rfl
      rw [hh', e1, hh1, e2] at this
      simpa using this
    exact hS.ne (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hae))
  ·
    intro c x i h
    set h' : Lp ℂ 2 ν := (hmem (c * a₀) h).toLp _ with hh'
    have hV : V h' = R (c * a₀) (V h) := hS.mul _ h _ (MemLp.coeFn_toLp _)
    obtain ⟨Tc, hTc, hTcJ⟩ := hT c
    have key : Tc (T₁ (L h)) = T₁ (L h') := by
      rw [hT1L, hT1L, hTcJ, hV]
      congr 1
      show (R (c * a₀) * R a₀) (V h) = (R a₀ * R (c * a₀)) (V h)
      rw [← map_mul, ← map_mul, mul_comm]
    have e := hRe X ι (Φ c) Tc T₁ k (L h) (L h') (hΦ c) hTc hk key x i
    simp only [hin]
    rw [e, ← hin, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (hmem (c * a₀) h)] with s hs
    rw [hs, RCLike.inner_apply']
    ring
  ·
    intro n i
    have hgm : AEStronglyMeasurable (fun x => (g n i : X.G → ℂ) x) X.ν := Lp.aestronglyMeasurable _
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable hgm, ?_⟩
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hg' n i, hwt i⟩) ?_
    have hm : AEMeasurable (fun x => (W x)⁻¹ * ‖(g n i : X.G → ℂ) x‖ₑ ^ 2) X.ν :=
      hW.inv.aemeasurable.mul (hgm.enorm.pow_const 2)
    rw [← lintegral_add_left' hm]
    refine lintegral_mono fun x => ?_
    rw [RCLike.enorm_conj]
    exact Fdata.mul_le_weighted_squares _ _ _ (hW' x).1 (hW' x).2
  ·
    intro n h
    have e : ∀ i, ∫ x, conj ((g n i : X.G → ℂ) x) * inner ℂ (A (k i x)) h ∂X.ν = inner ℂ (g n i) (T₁ (L h) i) := by
      intro i
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hk.rep (L h) i] with x hx
      rw [hx, hin, RCLike.inner_apply']
    simp only [e]
    rw [← PiLp.inner_apply, hT1L]
    exact inner_eq_zero_symm.1 (hg n _)

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Rowseig
section
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem rowseig : AeEq → Unfold → RowsEig := by
  intro hAe hUn X ι _ Φ T T₁ k u u' hΦ hT hk heq x i
  have wc : ∀ j, Continuous fun y => inner ℂ (k j y) u := fun j => (hk.cont j).inner continuous_const
  have winv : ∀ j, ∀ γ ∈ X.Γ, ∀ y, (fun y => inner ℂ (k j y) u) (γ * y) = (fun y => inner ℂ (k j y) u) y :=
    fun j γ hγ y => by simp only [hk.inv j γ hγ y]
  have hLc : Continuous fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ :=
    continuous_finsetSum _ fun j _ => (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).2
  have hRc : Continuous fun x => inner ℂ (k i x) u' := (hk.cont i).inner continuous_const
  have hLinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) (γ * x)
      = (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) x := by
    intro γ hγ x
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_assoc, hk.inv j γ hγ]
  have hRinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => inner ℂ (k i x) u') (γ * x) = (fun x => inner ℂ (k i x) u') x :=
    fun γ hγ x => by simp only [hk.inv i γ hγ x]
  have h3 : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ)
      = fun x => ∑ j, ∫ y, ker X.Γ (Φ i j) x y * (T₁ u j : X.G → ℂ) y ∂X.ν := by
    funext x
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).1 x
    refine e1.symm.trans (integral_congr_ae ((hk.rep u j).mono fun y hy => ?_))
    simp only [hy]
  have hae : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) =ᵐ[X.ν]
      fun x => inner ℂ (k i x) u' := by
    rw [h3]
    have h1 := hT (T₁ u) i
    rw [heq] at h1
    exact h1.symm.trans (hk.rep u' i)
  exact congrFun (hAe X _ _ hLc hRc hLinv hRinv hae) x

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Rowsex
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory

namespace PositivityTheory.Rg.BcB.E2.P

theorem rowsex : KerBasic → VecEx → VecNorm → VecInner → RowsEx := by
  intro hK hE hN hI X ι _ Φ T hΦ hT
  have hΨ : ∀ i j, Tst ((fun i j => adj (Φ j i)) i j : X.G → ℂ) := fun i j => (hK X (Φ j i) (hΦ j i)).2.2.2.1
  obtain ⟨k', hc, hv⟩ := hE X ι (fun i j => adj (Φ j i)) hΨ
  obtain ⟨C, Ω, hC, hΩ, hb⟩ := hN X ι (fun i j => adj (Φ j i)) hΨ
  refine ⟨fun i x => k' x i, ⟨hc, ?_, ?_, ⟨C, Ω, hC, hΩ, fun i x => hb x i _ (hv x i)⟩⟩⟩
  · intro i γ hγ x
    refine PiLp.ext fun l => Lp.ext ?_
    filter_upwards [hv (γ * x) i l, hv x i l] with z h1 h2
    rw [h1, h2]
    exact ((hK X _ (hΨ l i)).2.2.1 γ hγ z x).2
  · intro u i
    filter_upwards [hT u i] with x hx
    rw [hx]
    exact ((hI X ι Φ x i (k' x i) u hΦ).2 (hv x i)).symm

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Smooth
section
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem smooth : ConvCont → Smooth := by
  classical
  intro hconv X ι κ _ u Φ lam c₀ hu hinv hΦ hlam heq
  set f : ι → X.G → ℂ := fun i x => (lam c₀)⁻¹ * ∑ j, ∫ y, Φ c₀ i j y * u j (x * y) ∂X.μ with hf
  have hcont : ∀ i, Continuous (f i) := fun i =>
    continuous_const.mul (continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c₀ i j) (hu j))
  have hae : ∀ i, f i =ᵐ[X.μ] u i := fun i => (heq c₀ i).mono fun x hx => by
    simp only [hf]
    rw [hx, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]
  refine ⟨f, fun i => ⟨hcont i, hae i, fun γ hγ x => ?_⟩, fun c i x => ?_⟩
  · simp only [hf]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext y
    rw [mul_assoc, hinv j γ hγ]
  · have hconv' : ∀ x, ∑ j, ∫ y, Φ c i j y * f j (x * y) ∂X.μ = ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ := by
      intro x
      refine Finset.sum_congr rfl fun j _ => ?_
      refine integral_congr_ae ?_
      have h1 := (measurePreserving_mul_left X.μ x).quasiMeasurePreserving.ae_eq_comp (hae j)
      filter_upwards [h1] with y hy
      simp only [Function.comp] at hy
      rw [hy]
    have hc1 : Continuous fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ :=
      continuous_finsetSum _ fun j _ => hconv X _ _ (hΦ c i j) (hu j)
    have hc2 : Continuous fun x => lam c * f i x := continuous_const.mul (hcont i)
    have hae2 : (fun x => ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ) =ᵐ[X.μ] fun x => lam c * f i x := by
      filter_upwards [heq c i, hae i] with x h1 h2
      rw [h1, h2]
    have := (Continuous.ae_eq_iff_eq X.μ hc1 hc2).1 hae2
    rw [hconv' x]
    exact congrFun this x

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Speciso
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace PositivityTheory.Rg.BcB.E2.P

namespace Speciso

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {S : Type}
  [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]

def Lmap (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) : C(S, ℂ) →ₗ[ℂ] K where
  toFun f := π f v
  map_add' f g := by simp
  map_smul' c f := by simp

lemma inner_L (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) (ν : Measure S) [IsFiniteMeasure ν]
    (hν : ∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)) (f : C(S, ℂ)) :
    inner ℂ (π f v) (π f v) =
      inner ℂ (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) (ContinuousMap.toLp (E := ℂ) 2 ν ℂ f) := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : inner ℂ (π f v) (π f v) = ∫ s, (star f * f) s ∂ν := by
    rw [hν, map_mul, map_star, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  rw [h1]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := ν) f] with s hs
  rw [hs]
  simp [Complex.conj_mul']

lemma norm_L (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) (ν : Measure S) [IsFiniteMeasure ν]
    (hν : ∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)) (f : C(S, ℂ)) :
    ‖Lmap π v f‖ = ‖ContinuousMap.toLp (E := ℂ) 2 ν ℂ f‖ := by
  have h := congrArg RCLike.re (inner_L π v ν hν f)
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

end Speciso

open Speciso in
theorem speciso : SpecIso := by
  intro K _ _ _ S _ _ _ _ _ π v ν _ _ hν
  set e : C(S, ℂ) →L[ℂ] Lp ℂ 2 ν := ContinuousMap.toLp (E := ℂ) 2 ν ℂ with he
  have hd : DenseRange e := ContinuousMap.toLp_denseRange ℂ ν ℂ (p := 2) (by simp)
  have hcoe : ∀ g, (e g : S → ℂ) =ᵐ[ν] g := fun g =>
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ := ν) g
  have hn : ∀ f, ‖Lmap π v f‖ = ‖e.toLinearMap f‖ := fun f => norm_L π v ν hν f
  have hb : ∃ C, ∀ f, ‖Lmap π v f‖ ≤ C * ‖e.toLinearMap f‖ := ⟨1, fun f => by rw [hn, one_mul]⟩
  have hdl : DenseRange e.toLinearMap := hd
  let V : Lp ℂ 2 ν →L[ℂ] K := (Lmap π v).extendOfNorm e.toLinearMap
  have hVe : ∀ f, V (e f) = π f v := fun f => LinearMap.extendOfNorm_eq hdl hb f
  refine ⟨V, fun h => ?_, fun f h h' hh' => ?_⟩
  · refine hd.induction_on (p := fun h => ‖V h‖ = ‖h‖) h
      (isClosed_eq (continuous_norm.comp V.continuous) continuous_norm) ?_
    intro g
    show ‖V (e g)‖ = ‖e g‖
    rw [hVe]
    exact hn g
  · let F : Lp ℂ ∞ ν := ContinuousMap.toLp (E := ℂ) ∞ ν ℂ f
    have hF : (F : S → ℂ) =ᵐ[ν] f := ContinuousMap.coeFn_toLp (p := ∞) (𝕜 := ℂ) (μ := ν) f
    let M : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 F
    have hM : ∀ g, (M g : S → ℂ) =ᵐ[ν] fun s => f s * g s := by
      intro g
      have h1 : (M g : S → ℂ) =ᵐ[ν] fun s => (ContinuousLinearMap.mul ℂ ℂ) (F s) (g s) :=
        (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) F g
      filter_upwards [h1, hF] with s hs hFs
      rw [hs, ContinuousLinearMap.mul_apply', hFs]
    have key : ∀ g, V (M g) = π f (V g) := by
      intro g
      refine hd.induction_on (p := fun g => V (M g) = π f (V g)) g
        (isClosed_eq (V.continuous.comp M.continuous) ((π f).continuous.comp V.continuous)) ?_
      intro g
      have : M (e g) = e (f * g) := by
        apply Lp.ext
        filter_upwards [hM (e g), hcoe g, hcoe (f * g)] with s h1 h2 h3
        rw [h1, h2, h3]
        rfl
      show V (M (e g)) = π f (V (e g))
      rw [this, hVe, hVe, map_mul, ContinuousLinearMap.mul_apply]
    have : h' = M h := by
      apply Lp.ext
      filter_upwards [hh', hM h] with s h1 h2
      rw [h1, h2]
    rw [this, key]

end PositivityTheory.Rg.BcB.E2.P
end
end

