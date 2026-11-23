module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHausdorffNullComplementConnected
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory Set Relation
open scoped NNReal ENNReal

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radial_lipschitzOnWith (x : E) (ℓ : E →L[ℝ] ℝ) {β δ : ℝ} (hδ : 0 < δ) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun c => x + ((ℓ c - ℓ x) / β)⁻¹ • (c - x))
      {c | δ ≤ (ℓ c - ℓ x) / β ∧ ‖c - x‖ ≤ R} := by
  refine ⟨_, LipschitzOnWith.of_dist_le' (K := δ⁻¹ + ‖ℓ‖ * R / (|β| * (δ * δ))) ?_⟩
  rintro a ⟨ha, -⟩ b ⟨hb, hbR⟩
  set ta := (ℓ a - ℓ x) / β with hta_def
  set tb := (ℓ b - ℓ x) / β with htb_def
  have hta : 0 < ta := hδ.trans_le ha
  have htb : 0 < tb := hδ.trans_le hb
  have hβ : β ≠ 0 := by
    rintro rfl
    rw [hta_def, div_zero] at hta
    exact lt_irrefl _ hta
  have hkey : x + ta⁻¹ • (a - x) - (x + tb⁻¹ • (b - x)) =
      ta⁻¹ • (a - b) + (ta⁻¹ - tb⁻¹) • (b - x) := by
    simp only [smul_sub, sub_smul]; abel
  have hdiff : tb - ta = ℓ (b - a) / β := by
    rw [hta_def, htb_def, map_sub]; ring
  have hinv : |ta⁻¹ - tb⁻¹| ≤ ‖ℓ‖ * ‖a - b‖ / (|β| * (δ * δ)) := by
    rw [inv_sub_inv hta.ne' htb.ne', hdiff, abs_div, abs_div, abs_of_pos (mul_pos hta htb), div_div]
    apply div_le_div₀ (by positivity)
    · rw [← Real.norm_eq_abs, norm_sub_rev a b]
      exact ℓ.le_opNorm _
    · exact mul_pos (abs_pos.2 hβ) (mul_pos hδ hδ)
    · exact mul_le_mul_of_nonneg_left (mul_le_mul ha hb hδ.le hta.le) (abs_nonneg _)
  rw [dist_eq_norm, dist_eq_norm, hkey]
  calc ‖ta⁻¹ • (a - b) + (ta⁻¹ - tb⁻¹) • (b - x)‖
      ≤ ‖ta⁻¹ • (a - b)‖ + ‖(ta⁻¹ - tb⁻¹) • (b - x)‖ := norm_add_le _ _
    _ = ta⁻¹ * ‖a - b‖ + |ta⁻¹ - tb⁻¹| * ‖b - x‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hta)]
    _ ≤ δ⁻¹ * ‖a - b‖ + ‖ℓ‖ * ‖a - b‖ / (|β| * (δ * δ)) * R := by
        gcongr
    _ = (δ⁻¹ + ‖ℓ‖ * R / (|β| * (δ * δ))) * ‖a - b‖ := by ring

variable [MeasurableSpace E] [BorelSpace E]

theorem segment_hits_image_null {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] {C : Set E} {x : E} (hx : x ∉ C) (ℓ : E →L[ℝ] ℝ) {α : ℝ}
    (hα : α ≠ ℓ x) (g : E →L[ℝ] F) {d : ℝ} (hd : 0 ≤ d) (hC : μH[d] C = 0) :
    μH[d] (g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty}) = 0 := by
  have hβ : α - ℓ x ≠ 0 := sub_ne_zero.2 hα
  have hsub : g '' {m | ℓ m = α ∧ (segment ℝ x m ∩ C).Nonempty} ⊆
      ⋃ j : ℕ, (g ∘ fun c => x + ((ℓ c - ℓ x) / (α - ℓ x))⁻¹ • (c - x)) ''
        (C ∩ {c | ((j : ℝ) + 1)⁻¹ ≤ (ℓ c - ℓ x) / (α - ℓ x) ∧ ‖c - x‖ ≤ (j : ℝ) + 1}) := by
    rintro _ ⟨m, ⟨hm, c, hcs, hcC⟩, rfl⟩
    rw [segment_eq_image'] at hcs
    obtain ⟨s, ⟨hs0, -⟩, rfl⟩ := hcs
    have hs : s ≠ 0 := by
      rintro rfl
      simp only [zero_smul, add_zero] at hcC
      exact hx hcC
    have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hτ : (ℓ (x + s • (m - x)) - ℓ x) / (α - ℓ x) = s := by
      rw [map_add (f := _), map_smul, map_sub, hm, smul_eq_mul, add_sub_cancel_left, mul_div_assoc,
        div_self hβ, mul_one]
    obtain ⟨j, hj⟩ := exists_nat_gt (max s⁻¹ ‖s • (m - x)‖)
    refine mem_iUnion.2 ⟨j, x + s • (m - x), ⟨hcC, ?_, ?_⟩, ?_⟩
    · rw [hτ]
      have h1 : s⁻¹ < (j : ℝ) + 1 := by linarith [le_max_left s⁻¹ ‖s • (m - x)‖]
      calc ((j : ℝ) + 1)⁻¹ ≤ (s⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hspos) h1.le
        _ = s := inv_inv s
    · rw [add_sub_cancel_left]
      linarith [le_max_right s⁻¹ ‖s • (m - x)‖]
    · simp only [Function.comp_apply, hτ, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs,
        one_smul, add_sub_cancel]
  refine measure_mono_null hsub (measure_iUnion_null fun j => ?_)
  obtain ⟨K, hK⟩ := radial_lipschitzOnWith x ℓ (β := α - ℓ x) (R := (j : ℝ) + 1)
    (show (0 : ℝ) < ((j : ℝ) + 1)⁻¹ by positivity)
  have hL := g.lipschitz.comp_lipschitzOnWith (hK.mono (inter_subset_right (s := C)))
  refine le_antisymm ?_ zero_le
  calc _ ≤ _ := hL.hausdorffMeasure_image_le hd
    _ = 0 := by rw [measure_mono_null inter_subset_left hC, mul_zero]

theorem diff_nonempty_of_hausdorffMeasure_null [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty) : (U \ C).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, sdiff_eq_empty] at h
  obtain ⟨z, hz⟩ := hne
  have hlt : ((k : ℝ≥0) : ℝ≥0∞) < dimH U := by
    rw [Real.dimH_of_mem_nhds (hU.mem_nhds hz), hk]
    exact_mod_cast Nat.lt_succ_self k
  have htop := hausdorffMeasure_of_lt_dimH hlt
  rw [NNReal.coe_natCast, measure_mono_null h hC] at htop
  exact ENNReal.zero_ne_top htop

theorem convex_diff_isPreconnected [FiniteDimensional ℝ E] {k : ℕ}
    (hk : Module.finrank ℝ E = k + 1) {C : Set E} (hC : μH[(k : ℝ)] C = 0) {B : Set E}
    (hBo : IsOpen B) (hBc : Convex ℝ B) : IsPreconnected (B \ C) := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  by_cases hxy : x = y
  · subst hxy
    exact ⟨{x}, singleton_subset_iff.2 hx, rfl, rfl, isPreconnected_singleton⟩
  let φ : E ≃L[ℝ] (Fin (k + 1) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by rw [hk, Module.finrank_fin_fun])
  obtain ⟨i, hi⟩ : ∃ i, φ x i ≠ φ y i := by
    by_contra h
    push Not at h
    exact hxy (φ.injective (funext h))
  let ℓ : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp (φ : E →L[ℝ] (Fin (k + 1) → ℝ))
  let g : E →L[ℝ] (Fin k → ℝ) :=
    (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (i.succAbove j)).comp
      (φ : E →L[ℝ] (Fin (k + 1) → ℝ))
  have hℓ : ∀ z, ℓ z = φ z i := fun z => rfl
  have hg : ∀ z, g z = Fin.removeNth i (φ z) := fun z => rfl
  have hαx : (φ x i + φ y i) / 2 ≠ ℓ x := by rw [hℓ]; intro h; apply hi; linarith
  have hαy : (φ x i + φ y i) / 2 ≠ ℓ y := by rw [hℓ]; intro h; apply hi; linarith
  have hvol : (volume : Measure (Fin k → ℝ)) = μH[(k : ℝ)] := by
    have := hausdorffMeasure_pi_real (ι := Fin k)
    rw [Fintype.card_fin] at this
    exact this.symm
  have hS0 : volume (g '' {m | ℓ m = (φ x i + φ y i) / 2 ∧ (segment ℝ x m ∩ C).Nonempty} ∪
      g '' {m | ℓ m = (φ x i + φ y i) / 2 ∧ (segment ℝ y m ∩ C).Nonempty}) = 0 := by
    rw [hvol]
    exact measure_union_null (segment_hits_image_null hx.2 ℓ hαx g (Nat.cast_nonneg k) hC)
      (segment_hits_image_null hy.2 ℓ hαy g (Nat.cast_nonneg k) hC)
  let ψ : (Fin k → ℝ) → E := fun w => φ.symm (Fin.insertNth i ((φ x i + φ y i) / 2) w)
  have hψc : Continuous ψ :=
    φ.symm.continuous.comp (continuous_const.finInsertNth i continuous_id)
  have hz₀ : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y ∈ B :=
    hBc hx.1 hy.1 (by norm_num) (by norm_num) (by norm_num)
  have hψz₀ : ψ (g ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) = (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y := by
    have h1 : φ ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) i = (φ x i + φ y i) / 2 := by
      simp only [map_add (f := _), map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    simp only [ψ, hg]
    rw [← h1, Fin.insertNth_self_removeNth, ContinuousLinearEquiv.symm_apply_apply]
  have hWpos : 0 < volume (ψ ⁻¹' B) :=
    (hBo.preimage hψc).measure_pos volume ⟨_, show ψ _ ∈ B from hψz₀ ▸ hz₀⟩
  obtain ⟨w, hwB, hwS⟩ := nonempty_of_measure_ne_zero
    ((measure_sdiff_null hS0).symm ▸ hWpos.ne' : volume (ψ ⁻¹' B \ _) ≠ 0)
  have hφm : φ (ψ w) = Fin.insertNth i ((φ x i + φ y i) / 2) w := by
    simp only [ψ, ContinuousLinearEquiv.apply_symm_apply]
  have hℓm : ℓ (ψ w) = (φ x i + φ y i) / 2 := by rw [hℓ, hφm, Fin.insertNth_apply_same]
  have hgm : g (ψ w) = w := by rw [hg, hφm, Fin.removeNth_insertNth]
  have hxm : segment ℝ x (ψ w) ⊆ B \ C := fun c hc =>
    ⟨hBc.segment_subset hx.1 hwB hc, fun hcC => hwS (Or.inl ⟨ψ w, ⟨hℓm, c, hc, hcC⟩, hgm⟩)⟩
  have hmy : segment ℝ (ψ w) y ⊆ B \ C := fun c hc =>
    ⟨hBc.segment_subset hwB hy.1 hc, fun hcC =>
      hwS (Or.inr ⟨ψ w, ⟨hℓm, c, segment_symm ℝ (ψ w) y ▸ hc, hcC⟩, hgm⟩)⟩
  exact ⟨segment ℝ x (ψ w) ∪ segment ℝ (ψ w) y, union_subset hxm hmy,
    Or.inl (left_mem_segment ℝ x (ψ w)), Or.inr (right_mem_segment ℝ (ψ w) y),
    (convex_segment x (ψ w)).isPreconnected.union (ψ w) (right_mem_segment ℝ x (ψ w))
      (left_mem_segment ℝ (ψ w) y) (convex_segment (ψ w) y).isPreconnected⟩

theorem HausdorffNullComplementConnected.proof : HausdorffNullComplementConnected.Statement := by
  intro E _ _ _ _ _ D C hDo hDc hC
  by_cases h0 : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    exact Set.subsingleton_of_subsingleton.isPreconnected
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero h0
  have hC' : μH[(k : ℝ)] C = 0 := by
    rw [hk, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hC
    exact hC
  choose! r hr0 hrD using Metric.isOpen_iff.1 hDo
  have hU : D \ C = ⋃ z ∈ D, ball z (r z) \ C := by
    ext z
    simp only [mem_sdiff, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hz, hzC⟩
      exact ⟨z, hz, mem_ball_self (hr0 z hz), hzC⟩
    · rintro ⟨w, hw, hzb, hzC⟩
      exact ⟨hrD w hw hzb, hzC⟩
  rw [hU]
  refine IsPreconnected.biUnion_of_reflTransGen
    (fun z _ => convex_diff_isPreconnected hk hC' isOpen_ball (convex_ball z (r z))) ?_
  intro z hz w hw
  refine hDc.induction₂' (fun a b => ReflTransGen
      (fun i j => ((ball i (r i) \ C) ∩ (ball j (r j) \ C)).Nonempty ∧ i ∈ D) a b) ?_
    (fun a b c _ _ _ h1 h2 => h1.trans h2) hz hw
  intro a ha
  filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a (hr0 a ha)), self_mem_nhdsWithin]
    with b hb hbD
  obtain ⟨p, ⟨hpa, hpb⟩, hpC⟩ := diff_nonempty_of_hausdorffMeasure_null hk hC'
    (isOpen_ball.inter isOpen_ball) ⟨b, hb, mem_ball_self (hr0 b hbD)⟩
  exact ⟨ReflTransGen.single ⟨⟨p, ⟨hpa, hpC⟩, hpb, hpC⟩, ha⟩,
    ReflTransGen.single ⟨⟨p, ⟨hpb, hpC⟩, hpa, hpC⟩, hbD⟩⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIdealHeightSpread
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IdealHeightSpread.proof : IdealHeightSpread.Statement := by
  intro R _ _ I P _ _
  classical
  have hF := I.finite_minimalPrimes_of_isNoetherianRing R

  let a : Ideal R → R := fun p =>
    if h : ¬ (p : Set R) ⊆ P then Classical.choose (Set.not_subset.mp h) else 1
  have ha : ∀ p : Ideal R, ¬ p ≤ P → a p ∈ p ∧ a p ∉ P := by
    intro p h
    have h' : ¬ (p : Set R) ⊆ P := h
    simp only [a, dif_pos h']
    exact Classical.choose_spec (Set.not_subset.mp h')
  let s : Finset (Ideal R) := hF.toFinset.filter (fun p => ¬ p ≤ P)
  refine ⟨∏ p ∈ s, a p, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨p, hp, hpP⟩
    exact (ha p (Finset.mem_filter.mp hp).2).2 hpP
  · intro Q _ _ hgQ
    rw [Ideal.height_eq_inf_minimalPrimes (I.map (algebraMap R (Localization.AtPrime Q)))]
    refine le_iInf₂ fun J hJ => ?_
    have hJp : J.IsPrime := hJ.isPrime
    have hmin : J.comap (algebraMap R (Localization.AtPrime Q)) ∈ I.minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl] at hJ
      exact hJ
    set p := J.comap (algebraMap R (Localization.AtPrime Q)) with hpdef
    have hpp : p.IsPrime := hmin.1.1

    have hpQ : p ≤ Q := by
      intro x hx
      by_contra hxQ
      have hu := IsLocalization.map_units (Localization.AtPrime Q) (⟨x, hxQ⟩ : Q.primeCompl)
      exact hJp.ne_top (Ideal.eq_top_of_isUnit_mem J hx hu)

    have hpP : p ≤ P := by
      by_contra hnot
      apply hgQ
      apply hpQ
      have hps : p ∈ s := Finset.mem_filter.mpr ⟨hF.mem_toFinset.mpr hmin, hnot⟩
      exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hps) (ha p hnot).1
    have hdisj : Disjoint (P.primeCompl : Set R) (p : Set R) := by
      rw [Set.disjoint_left]
      intro x hx hxp
      exact hx (hpP hxp)
    have hJh : J.height = p.height := (IsLocalization.height_under Q.primeCompl J).symm
    rw [hJh, ← IsLocalization.height_map_of_disjoint P.primeCompl (S := Localization.AtPrime P) p hdisj]
    exact Ideal.height_mono (Ideal.map_mono hmin.1.2)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicDerivNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Filter Topology

theorem InjectiveHolomorphicDerivNeZero.proof : InjectiveHolomorphicDerivNeZero.Statement := by
  intro D f hD hf hinj a ha hder
  have hDa : D ∈ 𝓝 a := hD.mem_nhds ha
  set g : ℂ → ℂ := fun z ↦ f z - f a with hg
  have hga : AnalyticAt ℂ g a := (hf.analyticAt hDa).sub analyticAt_const

  have hntop : analyticOrderAt g a ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hev : ∀ᶠ z in 𝓝[≠] a, (g z = 0 ∧ z ∈ D) ∧ z ∈ ({a}ᶜ : Set ℂ) :=
      ((htop.and (hDa : ∀ᶠ z in 𝓝 a, z ∈ D)).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hz0, hzD⟩, hza⟩ := hev.exists
    exact hza (hinj hzD ha (sub_eq_zero.mp hz0))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hntop
  obtain ⟨u, hu, hua, hfac⟩ := hga.analyticOrderAt_eq_natCast.mp hn.symm
  simp only [smul_eq_mul] at hfac
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := hfac.self_of_nhds
    simp [hg] at this
    exact hua this.symm
  have hn1 : n ≠ 1 := by
    rintro rfl
    have hd : HasDerivAt (fun z ↦ (z - a) ^ 1 * u z) (u a) a := by
      have := ((hasDerivAt_id' a).sub_const a).mul hu.differentiableAt.hasDerivAt
      simp only [pow_one]
      exact this.congr_deriv (by simp)
    have : deriv g a = u a :=
      (EventuallyEq.deriv_eq (hfac : g =ᶠ[𝓝 a] fun z ↦ (z - a) ^ 1 * u z)).trans hd.deriv
    rw [hg, deriv_sub_const, hder] at this
    exact hua this.symm

  set c : ℂ := u a ^ ((n : ℂ)⁻¹) with hc
  set v : ℂ → ℂ := fun z ↦ c * (u z / u a) ^ ((n : ℂ)⁻¹) with hv
  have hva : AnalyticAt ℂ v a := analyticAt_const.mul
    ((hu.div analyticAt_const hua).cpow analyticAt_const (by simp [hua, Complex.one_mem_slitPlane]))
  have hvpow : ∀ z, v z ^ n = u z := by
    intro z
    rw [hv, mul_pow, hc, Complex.cpow_nat_inv_pow _ hn0, Complex.cpow_nat_inv_pow _ hn0]
    field_simp
  have hv0 : v a ≠ 0 := by
    intro h
    have := hvpow a
    rw [h, zero_pow hn0] at this
    exact hua this.symm
  set w : ℂ → ℂ := fun z ↦ (z - a) * v z with hw
  have hwd : HasDerivAt w (v a) a := by
    have := ((hasDerivAt_id' a).sub_const a).mul hva.differentiableAt.hasDerivAt
    exact this.congr_deriv (by simp)
  have hwa : w a = 0 := by simp [hw]
  have hgw : ∀ z, g z = (z - a) ^ n * u z → g z = w z ^ n := by
    intro z hz
    rw [hz, ← hvpow z, ← mul_pow]

  have hmap : 𝓝 (w a) ≤ map w (𝓝 a) := by
    have hwan : AnalyticAt ℂ w a := (analyticAt_id.sub analyticAt_const).mul hva
    refine hwan.eventually_constant_or_nhds_le_map_nhds.resolve_left ?_
    intro hconst
    have h1 : deriv w a = 0 := by
      rw [EventuallyEq.deriv_eq (hconst : w =ᶠ[𝓝 a] fun _ ↦ w a)]
      simp
    exact hv0 (hwd.deriv.symm.trans h1)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hmap (image_mem_map (inter_mem hDa hfac)))
  rw [hwa] at hball
  have hk : 1 < n := by omega
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hprim : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  set t : ℂ := ((ε / 2 : ℝ) : ℂ) with ht
  have htn : ‖t‖ = ε / 2 := by rw [ht, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at htn
    linarith
  obtain ⟨z₁, ⟨hz₁D, hz₁⟩, hw₁⟩ := hball (by
    rw [Metric.mem_ball, dist_zero_right, htn]; linarith)
  obtain ⟨z₂, ⟨hz₂D, hz₂⟩, hw₂⟩ := hball (show ζ * t ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, dist_zero_right, norm_mul, hprim.norm'_eq_one hn0, htn]; linarith)
  have hg₁ := hgw z₁ hz₁
  have hg₂ := hgw z₂ hz₂
  rw [hw₁] at hg₁
  rw [hw₂, mul_pow, hprim.pow_eq_one, one_mul] at hg₂
  have hf12 : f z₁ = f z₂ := by
    have : g z₁ = g z₂ := hg₁.trans hg₂.symm
    simpa [hg] using this
  have h12 := hinj hz₁D hz₂D hf12
  rw [h12, hw₂] at hw₁
  have : (ζ - 1) * t = 0 := by rw [sub_mul, one_mul, hw₁, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact hprim.ne_one hk (sub_eq_zero.mp h)
  · exact ht0 h

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLengthCutLocalizedModule
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

open IsLocalRing

theorem LengthCutLocalizedModule.proof (hG : LengthCutGlobal.Statement.{u, max u v})
    (hL : LengthLocalizedLocalized.Statement.{u, v}) : LengthCutLocalizedModule.Statement.{u, v} := by
  intro B _ _ P _ y Q₀ _ M _ _ _ hnil hy hQ htf
  have hPQ : P ≤ Q₀ := hQ ▸ le_sup_left
  have hdisj : Disjoint (Q₀.primeCompl : Set B) P := Set.disjoint_left.mpr fun _ hx hxP => hx (hPQ hxP)
  have hP' : (P.map (algebraMap B (Localization.AtPrime Q₀))).IsPrime :=
    LengthLocalizedLocalized.map_isPrime B P Q₀ hPQ
  have : IsNoetherianRing (Localization.AtPrime Q₀) :=
    IsLocalization.isNoetherianRing Q₀.primeCompl _ inferInstance
  have hunder : (P.map (algebraMap B (Localization.AtPrime Q₀))).comap (algebraMap B (Localization.AtPrime Q₀)) =
      P := IsLocalization.under_map_of_isPrime_disjoint Q₀.primeCompl _ ‹P.IsPrime› hdisj

  have hy' : algebraMap B (Localization.AtPrime Q₀) y ∉ P.map (algebraMap B (Localization.AtPrime Q₀)) := by
    intro h
    apply hy
    rw [← hunder]
    exact h

  have hsup : P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} = maximalIdeal (Localization.AtPrime Q₀) := by
    have hmap : Ideal.map (algebraMap B (Localization.AtPrime Q₀)) Q₀ =
        Ideal.map (algebraMap B (Localization.AtPrime Q₀)) (P ⊔ Ideal.span {y}) := congrArg _ hQ
    rw [← Localization.AtPrime.map_eq_maximalIdeal, hmap, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have hmax : (P.map (algebraMap B (Localization.AtPrime Q₀)) ⊔
      Ideal.span {algebraMap B (Localization.AtPrime Q₀) y}).IsMaximal := by
    rw [hsup]
    exact maximalIdeal.isMaximal _

  have hnil' : IsNilpotent (P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    rw [← Ideal.map_pow, hn]
    simp

  have hpir : IsPrincipalIdealRing
      (Localization.AtPrime Q₀ ⧸ P.map (algebraMap B (Localization.AtPrime Q₀))) := by
    set I := P.map (algebraMap B (Localization.AtPrime Q₀)) with hI
    have : IsLocalRing (Localization.AtPrime Q₀ ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hm : maximalIdeal (Localization.AtPrime Q₀ ⧸ I) =
        Ideal.span {Ideal.Quotient.mk I (algebraMap B (Localization.AtPrime Q₀) y)} := by
      have hc : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).comap (Ideal.Quotient.mk I) =
          maximalIdeal (Localization.AtPrime Q₀) :=
        eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
      rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (maximalIdeal _), hc, ← hsup,
        Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_span, Set.image_singleton]
    have hprin : (maximalIdeal (Localization.AtPrime Q₀ ⧸ I)).IsPrincipal := ⟨⟨_, hm⟩⟩
    exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime Q₀ ⧸ I)).out 1 5).mpr hprin

  have htf' : ∀ s ∉ P.map (algebraMap B (Localization.AtPrime Q₀)), ∀ m : LocalizedModule Q₀.primeCompl M,
      s • m = 0 → m = 0 := by
    intro s hs m hsm
    induction s using Localization.induction_on with
    | H x =>
    obtain ⟨a, t⟩ := x
    dsimp only at hs hsm
    have ha : a ∉ P := by
      intro ha
      apply hs
      rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    induction m using LocalizedModule.induction_on with
    | h m u =>
      rw [LocalizedModule.mk_smul_mk, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hsm
      obtain ⟨v, hv⟩ := hsm
      simp only [smul_zero, one_smul, Submonoid.smul_def, smul_smul] at hv
      have hva : (v : B) * a ∉ P := fun h =>
        (‹P.IsPrime›.mem_or_mem h).elim (fun h1 => v.2 (hPQ h1)) ha
      rw [htf _ hva m hv, LocalizedModule.zero_mk]

  have hloc : (Ideal.span {y} • ⊤ : Submodule B M).localized' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M) =
      (Ideal.span {algebraMap B (Localization.AtPrime Q₀) y} • ⊤ :
        Submodule (Localization.AtPrime Q₀) (LocalizedModule Q₀.primeCompl M)) := by
    rw [Submodule.localized'_smul, Submodule.localized'_top, Ideal.localized'_eq_map, Ideal.map_span,
      Set.image_singleton]
  let e := (IsLocalizedModule.linearEquiv Q₀.primeCompl
    ((Ideal.span {y} • ⊤ : Submodule B M).toLocalizedQuotient' (Localization.AtPrime Q₀) Q₀.primeCompl
      (LocalizedModule.mkLinearMap Q₀.primeCompl M))
    (LocalizedModule.mkLinearMap Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M)))).extendScalarsOfIsLocalization
      Q₀.primeCompl (Localization.AtPrime Q₀)
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hloc).length_eq,
    hG (Localization.AtPrime Q₀) (P.map (algebraMap B (Localization.AtPrime Q₀)))
      (algebraMap B (Localization.AtPrime Q₀) y) (LocalizedModule Q₀.primeCompl M) hnil' hpir hy' hmax htf',
    hL B P Q₀ M hPQ]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolyKaehlerFree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open KaehlerDifferential TensorProduct

theorem PolyKaehlerFree.proof : PolyKaehlerFree.Statement := by
  intro R k _ _ _ n
  set B := MvPolynomial (Fin n) k

  have hinj : Function.Injective (mapBaseChange R k B) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R k B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hex := exact_mapBaseChange_map R k B

  obtain ⟨l, hl⟩ := Module.projective_lifting_property ((map R k B B).restrictScalars B)
    LinearMap.id (map_surjective R k B)
  let e := ((hex.splitSurjectiveEquiv hinj) ⟨l, hl⟩).1
  have : Module.Free B Ω[B⁄k] := Module.Free.of_basis (mvPolynomialBasis k (Fin n))
  exact Module.Free.of_equiv e.symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

