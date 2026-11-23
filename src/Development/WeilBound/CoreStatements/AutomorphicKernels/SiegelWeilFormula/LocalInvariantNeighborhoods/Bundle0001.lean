module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.MeasurePreservingOfAddEquiv
section
namespace PositivityTheory.SiegelWeilFormula.OswLocFin

open MeasureTheory

theorem measurePreserving_of_addEquiv {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    (e : G ≃+ G) (he : Continuous e) (he' : Continuous e.symm) (B : Set G) (hB : IsCompact B)
    (hB' : (interior B).Nonempty) (heB : e ⁻¹' B = B) :
    MeasureTheory.MeasurePreserving e μ μ := by
  have hm : Measurable e := he.measurable
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he he'
  obtain ⟨c, hcμ⟩ : ∃ c : NNReal, μ.map e = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map e) μ⟩
  have hBm : MeasurableSet B := hB.isClosed.measurableSet
  have hval : μ.map e B = μ B := by rw [Measure.map_apply hm hBm, heB]
  have hpos : μ B ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ hB').ne'
  have hfin : μ B ≠ ⊤ := hB.measure_lt_top.ne
  have hc : c = 1 := by
    have h1 := congrArg (fun ν : Measure G => ν B) hcμ
    simp only [Measure.smul_apply, hval, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 : (c : ENNReal) * μ B = 1 * μ B := by rw [one_mul]; exact h1.symm
    have h3 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h2
    exact_mod_cast h3
  refine ⟨hm, ?_⟩
  rw [hcμ, hc, one_smul]

end PositivityTheory.SiegelWeilFormula.OswLocFin
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.NhdsInv
section
namespace PositivityTheory.SiegelWeilFormula.OswLocFin

open Filter Topology

theorem exists_nhds_invariant {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {Φ : G → ℂ} (hΦ : IsLocallyConstant Φ ∧ HasCompactSupport Φ) :
    ∃ U ∈ nhds (0 : G), ∀ Y, ∀ Z ∈ U, Φ (Y + Z) = Φ Y := by
  obtain ⟨hlc, hcs⟩ := hΦ
  have hT : ∀ x : G, {z : G | Φ (x + z) = Φ x} ∈ 𝓝 (0 : G) := by
    intro x
    have hopen : IsOpen {z : G | Φ (x + z) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    exact hopen.mem_nhds (by simp)
  choose V₁ hV₁ hV₁s using fun x => exists_nhds_zero_half (hT x)
  choose V₂ hV₂ hV₂s using fun x => exists_nhds_half_neg (hT x)
  have hU : ∀ x : G, {y : G | y - x ∈ V₁ x ∩ V₂ x} ∈ 𝓝 x := by
    intro x
    have ht : Tendsto (fun y : G => y - x) (𝓝 x) (𝓝 (x - x)) := (continuous_sub_right x).tendsto x
    rw [sub_self] at ht
    exact ht (Filter.inter_mem (hV₁ x) (hV₂ x))
  obtain ⟨t, -, hcover⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x => {y : G | y - x ∈ V₁ x ∩ V₂ x}) (fun x _ => hU x)
  refine ⟨⋂ x ∈ t, V₁ x ∩ V₂ x, (Filter.biInter_finset_mem t).mpr fun x _ =>
    Filter.inter_mem (hV₁ x) (hV₂ x), fun Y Z hZ => ?_⟩
  have hZ' : ∀ x ∈ t, Z ∈ V₁ x ∩ V₂ x := Set.mem_iInter₂.mp hZ
  by_cases hY : Y ∈ tsupport Φ
  · obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (hcover hY)
    have hx' : Y - x ∈ V₁ x ∩ V₂ x := hx
    have h1 : Φ (x + (Y - x + Z)) = Φ x := hV₁s x _ hx'.1 Z (hZ' x hxt).1
    have h2 : Φ (x + (Y - x + 0)) = Φ x := hV₁s x _ hx'.1 0 (mem_of_mem_nhds (hV₁ x))
    rw [show x + (Y - x + Z) = Y + Z by abel] at h1
    rw [show x + (Y - x + 0) = Y by abel] at h2
    rw [h1, h2]
  · by_cases hYZ : Y + Z ∈ tsupport Φ
    · obtain ⟨x, hxt, hx⟩ := Set.mem_iUnion₂.mp (hcover hYZ)
      have hx' : Y + Z - x ∈ V₁ x ∩ V₂ x := hx
      have h1 : Φ (x + (Y + Z - x - Z)) = Φ x := hV₂s x _ hx'.2 Z (hZ' x hxt).2
      have h2 : Φ (x + (Y + Z - x + 0)) = Φ x := hV₁s x _ hx'.1 0 (mem_of_mem_nhds (hV₁ x))
      rw [show x + (Y + Z - x - Z) = Y by abel] at h1
      rw [show x + (Y + Z - x + 0) = Y + Z by abel] at h2
      rw [h1, h2]
    · rw [image_eq_zero_of_notMem_tsupport hY, image_eq_zero_of_notMem_tsupport hYZ]

end PositivityTheory.SiegelWeilFormula.OswLocFin
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalInvariantNeighborhoods.SmallSub
section
namespace PositivityTheory.SiegelWeilFormula.OswLocFin

theorem eq_one_of_re_pow_two (w : ℂ) (hw : ‖w‖ = 1) (hre : ∀ k : ℕ, 1 / 2 < (w ^ (2 ^ k)).re) :
    w = 1 := by
  have hsq : ∀ u : ℂ, ‖u‖ = 1 → u.re ^ 2 + u.im ^ 2 = 1 := by
    intro u hu
    have h := Complex.normSq_eq_norm_sq u
    rw [hu, Complex.normSq_apply] at h
    nlinarith [h]
  have hnorm : ∀ k : ℕ, ‖w ^ (2 ^ k)‖ = 1 := fun k => by rw [norm_pow, hw, one_pow]
  have hstep : ∀ k : ℕ, (w ^ (2 ^ (k + 1))).re = 2 * (w ^ (2 ^ k)).re ^ 2 - 1 := by
    intro k
    have e : w ^ (2 ^ (k + 1)) = w ^ (2 ^ k) * w ^ (2 ^ k) := by rw [← pow_add]; congr 1; ring
    rw [e, Complex.mul_re]
    have := hsq _ (hnorm k)
    nlinarith [this]
  have hle : ∀ k : ℕ, (w ^ (2 ^ k)).re ≤ 1 := fun k => (Complex.re_le_norm _).trans (hnorm k).le
  have hd0 : 0 ≤ 1 - w.re := by have := hle 0; simp at this; linarith
  have hgrow : ∀ k : ℕ, ((k : ℝ) + 1) * (1 - w.re) ≤ 1 - (w ^ (2 ^ k)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hstep k]
      have h1 := hre k
      have h2 := hle k
      have h3 : 0 ≤ (1 - (w ^ (2 ^ k)).re) * (w ^ (2 ^ k)).re :=
        mul_nonneg (by linarith) (by linarith)
      push_cast
      nlinarith [ih, h1, h2, hd0, h3]
  have hd_eq : 1 - w.re = 0 := by
    by_contra hne
    have hpos : 0 < 1 - w.re := lt_of_le_of_ne hd0 (Ne.symm hne)
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / (1 - w.re))
    have h1 := hgrow k
    have h2 := hre k
    have h4 := hle k
    have : (1 : ℝ) < ((k : ℝ) + 1) * (1 - w.re) := by
      rw [div_lt_iff₀ hpos] at hk; nlinarith
    linarith
  have hre1 : w.re = 1 := by linarith
  have him : w.im = 0 := by have := hsq w hw; rw [hre1] at this; nlinarith
  exact Complex.ext (by simp [hre1]) (by simp [him])

theorem no_small_subgroups {K : Type*} [NormedField K] [IsUltrametricDist K] [ProperSpace K]
    (χ : K → ℂ) (hc : Continuous χ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (h0 : χ 0 = 1)
    (hn : ∀ x, ‖χ x‖ = 1) : ∃ ε > 0, ∀ t : K, ‖t‖ ≤ ε → χ t = 1 := by
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.1 hc 0 (1 / 2) (by norm_num)
  refine ⟨δ / 2, half_pos hδ, fun t ht => ?_⟩
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (1 : K) 1
    rw [one_add_one_eq_two, norm_one, max_self] at this
    exact this
  have hsmall : ∀ k : ℕ, ‖(2 : K) ^ k * t‖ ≤ δ / 2 := fun k => by
    rw [norm_mul, norm_pow]
    calc ‖(2 : K)‖ ^ k * ‖t‖ ≤ 1 * ‖t‖ := by
          gcongr; exact pow_le_one₀ (norm_nonneg _) h2
      _ ≤ δ / 2 := by rw [one_mul]; exact ht
  have hpow : ∀ k : ℕ, χ ((2 : K) ^ k * t) = χ t ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show (2 : K) ^ (k + 1) * t = (2 : K) ^ k * t + (2 : K) ^ k * t by ring, hadd, ih, ← pow_add]
      congr 1
      ring
  have hre : ∀ k : ℕ, 1 / 2 < (χ t ^ (2 ^ k)).re := by
    intro k
    rw [← hpow k]
    have hd := hδc ((2 : K) ^ k * t) (by rw [dist_zero_right]; linarith [hsmall k])
    rw [h0, dist_eq_norm] at hd
    have := Complex.re_le_norm (1 - χ ((2 : K) ^ k * t))
    rw [norm_sub_rev] at this
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith
  exact eq_one_of_re_pow_two (χ t) (hn t) hre

end PositivityTheory.SiegelWeilFormula.OswLocFin
end

