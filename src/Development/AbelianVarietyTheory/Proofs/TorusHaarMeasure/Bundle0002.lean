module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSmoothStepSharpSlope
section
open MeasureTheory Set
open scoped ContDiff

namespace GlobalTheory

theorem exists_smooth_step_sharp_slope (ρ ε : ℝ) (hε : 0 < ε) (h4 : 4 * ε < ρ) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ u, u ≤ ε → η u = 1) ∧ (∀ u, ρ - ε ≤ u → η u = 0) ∧
      (∀ u, 0 ≤ η u) ∧ (∀ u, η u ≤ 1) ∧ ∀ u, -(1 / (ρ - 4 * ε)) ≤ deriv η u := by
  let ψ : ContDiffBump (ρ / 2 : ℝ) := ⟨ρ / 2 - 2 * ε, ρ / 2 - ε, by linarith, by linarith⟩
  have hψc : Continuous ψ := ψ.continuous
  have hψ0 : ∀ t, t ≤ ε ∨ ρ - ε ≤ t → ψ t = 0 := by
    intro t ht
    apply ψ.zero_of_le_dist
    rw [Real.dist_eq]
    show ρ / 2 - ε ≤ |t - ρ / 2|
    rcases ht with ht | ht
    · rw [abs_sub_comm]; exact le_trans (by linarith) (le_abs_self _)
    · exact le_trans (by linarith) (le_abs_self _)
  have hψ1 : ∀ t, 2 * ε ≤ t → t ≤ ρ - 2 * ε → ψ t = 1 := by
    intro t h1 h2
    apply ψ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |t - ρ / 2| ≤ ρ / 2 - 2 * ε
    rw [abs_le]; constructor <;> linarith
  have hII : ∀ a b, IntervalIntegrable ψ volume a b := fun a b => hψc.intervalIntegrable a b
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun u => ∫ t in ε..u, ψ t := ⟨_, rfl⟩
  have hFd : ∀ u, HasDerivAt F (ψ u) u := by
    intro u; rw [hF]; exact (hψc.integral_hasStrictDerivAt ε u).hasDerivAt
  have hFs : ContDiff ℝ ∞ F := by
    refine contDiff_infty_iff_deriv.2 ⟨fun u => (hFd u).differentiableAt, ?_⟩
    have h : deriv F = ψ := funext fun u => (hFd u).deriv
    rw [h]; exact ψ.contDiff
  have hFlow : ∀ u, u ≤ ε → F u = 0 := by
    intro u hu
    rw [hF]
    show ∫ t in ε..u, ψ t = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      exact hψ0 t (Or.inl (le_trans ht.2 (sup_le le_rfl hu)))
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ t in ε..(ρ - ε), ψ t := ⟨_, rfl⟩
  have hFhigh : ∀ u, ρ - ε ≤ u → F u = I := by
    intro u hu
    rw [hF, hI]
    show ∫ t in ε..u, ψ t = ∫ t in ε..(ρ - ε), ψ t
    rw [← intervalIntegral.integral_add_adjacent_intervals (hII ε (ρ - ε)) (hII (ρ - ε) u),
      intervalIntegral.integral_congr (a := ρ - ε) (b := u) (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      exact hψ0 t (Or.inr (le_trans (le_inf le_rfl hu) ht.1))
  have hIge : ρ - 4 * ε ≤ I := by
    rw [hI]
    calc ρ - 4 * ε = ∫ _ in (2 * ε)..(ρ - 2 * ε), (1 : ℝ) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; ring
      _ = ∫ t in (2 * ε)..(ρ - 2 * ε), ψ t := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le (by linarith)] at ht
          exact (hψ1 t ht.1 ht.2).symm
      _ ≤ ∫ t in ε..(ρ - ε), ψ t :=
          intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
            (Filter.Eventually.of_forall fun t => ψ.nonneg) (hII _ _)
  have hIpos : 0 < I := by linarith
  have hFrange : ∀ u, 0 ≤ F u ∧ F u ≤ I := by
    intro u
    rcases le_total u ε with h | h
    · rw [hFlow u h]; exact ⟨le_rfl, hIpos.le⟩
    rcases le_total (ρ - ε) u with h' | h'
    · rw [hFhigh u h']; exact ⟨hIpos.le, le_rfl⟩
    have hsplit : F u + ∫ t in u..(ρ - ε), ψ t = I := by
      rw [hF, hI]; exact intervalIntegral.integral_add_adjacent_intervals (hII _ _) (hII _ _)
    have h1 : 0 ≤ F u := by
      rw [hF]; exact intervalIntegral.integral_nonneg h fun t _ => ψ.nonneg
    have h2 : 0 ≤ ∫ t in u..(ρ - ε), ψ t := intervalIntegral.integral_nonneg h' fun t _ => ψ.nonneg
    exact ⟨h1, by linarith⟩
  refine ⟨fun u => 1 - F u / I, contDiff_const.sub (hFs.div_const I), ?_, ?_, ?_, ?_, ?_⟩
  · intro u hu; simp [hFlow u hu]
  · intro u hu; simp [hFhigh u hu, hIpos.ne']
  · intro u
    rw [sub_nonneg, div_le_one hIpos]; exact (hFrange u).2
  · intro u
    have : 0 ≤ F u / I := div_nonneg (hFrange u).1 hIpos.le
    linarith
  · intro u
    have hd : HasDerivAt (fun u => 1 - F u / I) (-(ψ u / I)) u :=
      ((hFd u).div_const I).const_sub 1
    rw [hd.deriv, neg_le_neg_iff, div_le_div_iff₀ hIpos (by linarith)]
    nlinarith [ψ.le_one (x := u), ψ.nonneg (x := u)]

theorem exists_cutoff_log_sharp : ∀ ρ0 θ : ℝ, 0 < ρ0 → 1 < θ → ∃ ε C : ℝ, 0 < ε ∧ ε < ρ0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ g : ℝ → ℝ,
    ContDiffOn ℝ ∞ g (Set.Ioi (-δ)) ∧ (∀ u, ρ0 - ε ≤ u → g u = 0) ∧
    (∀ u, 0 ≤ u → g u ≤ 0 ∧ 0 ≤ deriv g u ∧ -(θ / ρ0) ≤ deriv g u + u * deriv (deriv g) u) ∧
    (∀ u, 0 ≤ u → u ≤ ε → g u ≤ Real.log (u + δ) + C) ∧ ∀ u, ε / 2 ≤ u → -C ≤ g u := by
  intro ρ0 θ hρ hθ
  obtain ⟨ε, hε, hE⟩ : ∃ ε : ℝ, 0 < ε ∧ 8 * θ * ε = ρ0 * (θ - 1) :=
    ⟨ρ0 * (θ - 1) / (8 * θ), div_pos (mul_pos hρ (by linarith)) (by linarith), by field_simp⟩
  have h4 : 4 * ε < ρ0 := by nlinarith
  have hpos : 0 < ρ0 - 4 * ε := by linarith
  have hslope : 1 / (ρ0 - 4 * ε) ≤ θ / ρ0 := by
    rw [one_div_le hpos (by positivity), one_div_div, div_le_iff₀ (by linarith)]
    nlinarith
  obtain ⟨η, hηs, hη1, hη0, hηnn, hηle, hηd⟩ := exists_smooth_step_sharp_slope ρ0 ε hε h4
  refine ⟨ε, 2 * ρ0 / ε + |Real.log ε|, hε, by linarith, ?_⟩
  intro δ hδ _
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = fun t => η t / (t + δ) := ⟨_, rfl⟩
  have hfv : ∀ t, f t = η t / (t + δ) := fun t => by rw [hf]
  have hfc : ContDiffOn ℝ ∞ f (Set.Ioi (-δ)) := by
    rw [hf]
    refine hηs.contDiffOn.div (contDiffOn_id.add contDiffOn_const) fun t ht => ?_
    have h : 0 < t + δ := by simp only [Set.mem_Ioi] at ht; linarith
    exact h.ne'
  have hfcont := hfc.continuousOn
  have hsub : ∀ a b, -δ < a → -δ < b → Set.uIcc a b ⊆ Set.Ioi (-δ) := fun a b ha hb t ht =>
    lt_of_lt_of_le (lt_inf_iff.2 ⟨ha, hb⟩) ht.1
  have hII : ∀ a b, -δ < a → -δ < b → IntervalIntegrable f volume a b :=
    fun a b ha hb => (hfcont.mono (hsub a b ha hb)).intervalIntegrable
  have hd : ∀ u, -δ < u → HasDerivAt (fun u => ∫ t in ρ0..u, f t) (f u) u := fun u hu =>
    intervalIntegral.integral_hasDerivAt_right (hII ρ0 u (by linarith) hu)
      (hfcont.stronglyMeasurableAtFilter isOpen_Ioi u hu)
      (hfcont.continuousAt (isOpen_Ioi.mem_nhds hu))
  have hnn : ∀ t, -δ < t → 0 ≤ f t := fun t ht => by
    rw [hfv]; exact div_nonneg (hηnn t) (by linarith)
  have hzero : ∀ u, ρ0 - ε ≤ u → ∫ t in ρ0..u, f t = 0 := by
    intro u hu
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      have h : ρ0 - ε ≤ t := le_trans (le_inf (by linarith) hu) ht.1
      simp only [hfv, hη0 t h, zero_div]
  have hle0 : ∀ u, 0 ≤ u → ∫ t in ρ0..u, f t ≤ 0 := by
    intro u hu
    rcases le_total u ρ0 with h | h
    · rw [intervalIntegral.integral_symm]
      have := intervalIntegral.integral_nonneg (μ := volume) h fun t ht =>
        hnn t (lt_of_lt_of_le (by linarith) ht.1)
      linarith
    · rw [hzero u (by linarith)]
  refine ⟨fun u => ∫ t in ρ0..u, f t, ?_, hzero, ?_, ?_, ?_⟩
  · exact (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).2
      ⟨fun u hu => (hd u hu).differentiableAt.differentiableWithinAt,
       hfc.congr fun u hu => (hd u hu).deriv⟩
  · intro u hu
    have hu' : -δ < u := by linarith
    have hp : 0 < u + δ := by linarith
    have hdg : deriv (fun u => ∫ t in ρ0..u, f t) u = f u := (hd u hu').deriv
    have hηdiff : HasDerivAt η (deriv η u) u := ((hηs.differentiable (by simp)) u).hasDerivAt
    have hfd : HasDerivAt f ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2) u := by
      rw [hf]; exact hηdiff.fun_div ((hasDerivAt_id u).add_const δ) hp.ne'
    have hdd : deriv (deriv (fun u => ∫ t in ρ0..u, f t)) u = deriv f u := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds hu'] with t ht using (hd t ht).deriv
    refine ⟨hle0 u hu, ?_, ?_⟩
    · rw [hdg, hfv]; exact div_nonneg (hηnn u) hp.le
    · rw [hdg, hdd, hfd.deriv, hfv]
      have ha : 0 < 1 / (ρ0 - 4 * ε) := by positivity
      have key : η u / (u + δ) + u * ((deriv η u * (u + δ) - η u * 1) / (u + δ) ^ 2)
          = η u * δ / (u + δ) ^ 2 + u * deriv η u / (u + δ) := by
        field_simp; ring
      rw [key]
      have h1 : 0 ≤ η u * δ / (u + δ) ^ 2 := div_nonneg (mul_nonneg (hηnn u) hδ.le) (sq_nonneg _)
      have h2 : -(1 / (ρ0 - 4 * ε)) ≤ u * deriv η u / (u + δ) := by
        rw [le_div_iff₀ hp]
        nlinarith [mul_le_mul_of_nonneg_left (hηd u) hu, mul_pos ha hδ]
      linarith
  · intro u hu0 huε
    beta_reduce
    have hp : 0 < u + δ := by linarith
    have hεδ : 0 < ε + δ := by linarith
    have hsplit : ∫ t in ρ0..u, f t = (∫ t in ρ0..ε, f t) - ∫ t in u..ε, f t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hII ρ0 ε (by linarith) (by linarith)) (hII ε u (by linarith) (by linarith)),
        intervalIntegral.integral_symm u ε]
      ring
    have hlog : ∫ t in u..ε, f t = Real.log (ε + δ) - Real.log (u + δ) := by
      rw [intervalIntegral.integral_congr (g := fun t => (t + δ)⁻¹) ?_]
      · have h := intervalIntegral.integral_comp_add_right (a := u) (b := ε) (fun t : ℝ => t⁻¹) δ
        rw [h, integral_inv_of_pos hp hεδ, Real.log_div hεδ.ne' hp.ne']
      · intro t ht
        have h : t ≤ ε := le_trans ht.2 (sup_le huε le_rfl)
        simp only [hfv, hη1 t h, one_div]
    rw [hsplit, hlog]
    have h1 := hle0 ε hε.le
    have h2 : Real.log ε ≤ Real.log (ε + δ) := Real.log_le_log hε (by linarith)
    have h3 := neg_abs_le (Real.log ε)
    have h5 : 0 ≤ 2 * ρ0 / ε := by positivity
    linarith
  · intro u hu
    beta_reduce
    have hC : 0 ≤ 2 * ρ0 / ε + |Real.log ε| := by positivity
    rcases le_total u ρ0 with h | h
    · have hu' : -δ < u := by linarith
      rw [intervalIntegral.integral_symm]
      have hb : ∫ t in u..ρ0, f t ≤ ∫ _ in u..ρ0, (2 / ε) := by
        refine intervalIntegral.integral_mono_on h (hII u ρ0 hu' (by linarith))
          intervalIntegrable_const fun t ht => ?_
        have ht1 : ε / 2 ≤ t := le_trans hu ht.1
        have hk : 2 / ε * ε = 2 := div_mul_cancel₀ 2 hε.ne'
        rw [hfv, div_le_iff₀ (by linarith)]
        nlinarith [hηle t, mul_nonneg (div_pos two_pos hε).le (show 0 ≤ t + δ - ε / 2 by linarith)]
      rw [intervalIntegral.integral_const, smul_eq_mul] at hb
      have hm : (ρ0 - u) * (2 / ε) ≤ 2 * ρ0 / ε := by
        rw [show 2 * ρ0 / ε = ρ0 * (2 / ε) by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have := abs_nonneg (Real.log ε)
      linarith
    · rw [hzero u (by linarith)]; linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory


open MeasureTheory Topology Matrix in
open scoped ComplexOrder ENNReal Pointwise in
theorem _root_.GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) := by
  intro G _ _ _ _ _ _ _ _ Γ ⟨U, hU, hΓU⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨t, htU, ht, h1t⟩ := mem_nhds_iff.1 hU
    have hopen : IsOpen ({1} : Set Γ) := by
      rw [isOpen_induced_iff]
      refine ⟨t, ht, ?_⟩
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx
        exact Subtype.ext (hΓU x x.2 (htU hx))
      · rintro rfl
        exact h1t
    haveI : DiscreteTopology Γ := discreteTopology_of_isOpen_singleton_one hopen
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  · obtain ⟨V, hVo, hV1, hVU⟩ := exists_open_nhds_one_split hU
    let C : G → Set G := fun x => {y | y * x⁻¹ ∈ V ∧ x * y⁻¹ ∈ V}
    have hCo : ∀ x, IsOpen (C x) := fun x =>
      (hVo.preimage (continuous_id.mul continuous_const)).inter
        (hVo.preimage (continuous_const.mul continuous_inv))
    have hCx : ∀ x, x ∈ C x := fun x => by simp [C, hV1]
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable C hCo
    have hTne : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h1 : (1 : G) ∈ ⋃ x, C x := Set.mem_iUnion.2 ⟨1, hCx 1⟩
      rw [← hT, h] at h1
      simp at h1
    obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
    let W : ℕ → Set G := fun n => C (c n)
    have hWo : ∀ n, IsOpen (W n) := fun n => hCo _
    have hcover : ∀ x, ∃ n, x ∈ W n := by
      intro x
      have hx : x ∈ ⋃ y ∈ T, C y := by rw [hT]; exact Set.mem_iUnion.2 ⟨x, hCx x⟩
      rw [hc] at hx
      simp only [Set.biUnion_range, Set.mem_iUnion] at hx
      exact hx
    have hsep : ∀ n (x : G) (γ : Γ), x ∈ W n → (γ : G) * x ∈ W n → γ = 1 := by
      intro n x γ hx hγx
      have h := hVU _ hγx.1 _ hx.2
      have he : (γ : G) * x * (c n)⁻¹ * (c n * x⁻¹) = γ := by group
      rw [he] at h
      exact Subtype.ext (hΓU γ γ.2 h)
    let S : ℕ → Set G := fun m => ⋃ γ : Γ, (fun x => (γ : G) * x) ⁻¹' W m
    have hSo : ∀ m, IsOpen (S m) := fun m =>
      isOpen_iUnion fun γ => (hWo m).preimage (continuous_const.mul continuous_id)
    have hmemS : ∀ m x, x ∈ S m ↔ ∃ γ : Γ, (γ : G) * x ∈ W m := fun m x => by
      simp only [S, Set.mem_iUnion, Set.mem_preimage]
    refine ⟨⋃ n : ℕ, W n \ ⋃ m : Fin n, S m, ?_, ?_⟩
    · exact MeasurableSet.iUnion fun n =>
        (hWo n).measurableSet.diff (MeasurableSet.iUnion fun m => (hSo m).measurableSet)
    · intro g
      have hmemF : ∀ y, y ∈ (⋃ n : ℕ, W n \ ⋃ m : Fin n, S m) ↔
          ∃ n, y ∈ W n ∧ ∀ m < n, y ∉ S m := by
        intro y
        simp only [Set.mem_iUnion, Set.mem_diff, not_exists]
        constructor
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m hm' => hm ⟨m, hm'⟩⟩
        · rintro ⟨n, hy, hm⟩
          exact ⟨n, hy, fun m => hm m m.2⟩
      have hex : ∃ n, g ∈ S n := by
        obtain ⟨n, hn⟩ := hcover g
        exact ⟨n, (hmemS n g).2 ⟨1, by simpa using hn⟩⟩
      classical
      obtain ⟨γ, hγ⟩ := (hmemS _ g).1 (Nat.find_spec hex)
      refine ⟨γ, (hmemF _).2 ⟨Nat.find hex, hγ, fun m hm hS => ?_⟩, ?_⟩
      · obtain ⟨δ, hδ⟩ := (hmemS m _).1 hS
        exact Nat.find_min hex hm ((hmemS m g).2 ⟨δ * γ, by simpa [mul_assoc] using hδ⟩)
      · intro γ' hγ'
        obtain ⟨k, hk, hkS⟩ := (hmemF _).1 hγ'
        have hkN : k = Nat.find hex := by
          refine le_antisymm ?_ (Nat.find_min' hex ((hmemS k g).2 ⟨γ', hk⟩))
          by_contra hlt
          push_neg at hlt
          exact hkS _ hlt ((hmemS _ _).2 ⟨γ * γ'⁻¹, by simpa [mul_assoc] using hγ⟩)
        rw [hkN] at hk
        have h1 := hsep _ _ (γ' * γ⁻¹) hγ (by simpa [mul_assoc] using hk)
        exact mul_inv_eq_one.1 h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FundamentalSetLintegralMulRightAndMeasureLe
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem fundamentalSet_lintegral_mul_right_and_measure_le :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) := by
  intro G _ _ _ _ _ _ _ _ ν _ Γ _ F hF hex
  have hFD : IsFundamentalDomain Γ F ν :=
    IsFundamentalDomain.mk' hF.nullMeasurableSet (fun g => hex g)
  refine ⟨?_, ?_⟩
  · intro h hh φ hφ hinv
    have hmeas : MeasurableSet {g : G | g * h⁻¹ ∈ F} := (measurable_mul_const h⁻¹) hF
    have hFD' : IsFundamentalDomain Γ {g : G | g * h⁻¹ ∈ F} ν := by
      refine IsFundamentalDomain.mk' hmeas.nullMeasurableSet (fun g => ?_)
      have := hex (g * h⁻¹)
      simpa [Subgroup.smul_def, mul_assoc] using this
    have h1 : ∫⁻ g in {g : G | g * h⁻¹ ∈ F}, φ g ∂ν = ∫⁻ g in F, φ (g * h) ∂ν := by
      conv_lhs => rw [← hh]
      rw [setLIntegral_map hmeas hφ (measurable_mul_const h)]
      congr 2
      ext g
      simp
    rw [← h1]
    exact hFD'.setLIntegral_eq hFD φ (fun γ g => hinv γ γ.2 g)
  · intro K hK
    rw [hFD.measure_eq_tsum K]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro g ⟨hg, γ, hγ, k, hk, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hg⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetCauchySchwarzOfDetMono
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem gram_det_cauchy_schwarz_of_det_mono :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (P Q : Matrix n n ℂ), P.PosSemidef → Q.PosSemidef → 0 ≤ P.det.re ∧ P.det.re ≤ (P + Q).det.re ∧ (P.det ≠ 0 → (P + Q).det.re ≤ P.det.re → Q = 0)) → (∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix m n ℂ), ‖(Aᴴ * B).det‖ ^ 2 ≤ (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ∧ ((Aᴴ * B).det ≠ 0 → (((A)ᴴ * (A)).det.re) * (((B)ᴴ * (B)).det.re) ≤ ‖(Aᴴ * B).det‖ ^ 2 → ∃ C : Matrix n n ℂ, B = A * C)) := by
  intro H m n _ _ _ A B
  classical
  have hA : (Aᴴ * A).PosSemidef := posSemidef_conjTranspose_mul_self A
  have hB : (Bᴴ * B).PosSemidef := posSemidef_conjTranspose_mul_self B
  have hA0 : 0 ≤ (Aᴴ * A).det.re := (H n _ _ hA hA).1
  have hB0 : 0 ≤ (Bᴴ * B).det.re := (H n _ _ hB hB).1
  by_cases hG : (Aᴴ * A).det = 0
  · obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hG
    have hAv : A *ᵥ v = 0 := (conjTranspose_mul_self_mulVec_eq_zero A v).mp hv0
    have h1 : (Bᴴ * A).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, by rw [← mulVec_mulVec, hAv, mulVec_zero]⟩
    have h2 : (Aᴴ * B).det = 0 := by
      have : Aᴴ * B = (Bᴴ * A)ᴴ := by simp
      rw [this, det_conjTranspose, h1, star_zero]
    refine ⟨?_, fun h => (h h2).elim⟩
    rw [h2]
    simpa using mul_nonneg hA0 hB0
  · have hreal : (Aᴴ * A).det = ((Aᴴ * A).det.re : ℂ) := by
      have : star (Aᴴ * A).det = (Aᴴ * A).det := by
        rw [← det_conjTranspose, hA.1.eq]
      exact (Complex.conj_eq_iff_re.mp this).symm
    set g : ℝ := (Aᴴ * A).det.re with hg
    have hg0 : g ≠ 0 := fun h => hG (by rw [hreal, h]; simp)
    have hgpos : 0 < g := lt_of_le_of_ne hA0 hg0.symm
    obtain ⟨C, hC⟩ : ∃ C : Matrix n n ℂ, (Aᴴ * A) * C = Aᴴ * B :=
      ⟨(Aᴴ * A)⁻¹ * (Aᴴ * B), mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hG)⟩
    have horth : (A * C)ᴴ * (B - A * C) = 0 := by
      rw [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_sub, ← Matrix.mul_assoc Aᴴ A C, hC,
        sub_self, Matrix.mul_zero]
    have horth' : (B - A * C)ᴴ * (A * C) = 0 := by
      have := congrArg conjTranspose horth
      rwa [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_zero] at this
    have hsum : Bᴴ * B = (A * C)ᴴ * (A * C) + (B - A * C)ᴴ * (B - A * C) := by
      have hBe : B = A * C + (B - A * C) := by abel
      generalize B - A * C = D at *
      generalize A * C = E at *
      rw [hBe, conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, horth, horth']
      simp
    have hP : ((A * C)ᴴ * (A * C)).det = ((g * ‖C.det‖ ^ 2 : ℝ) : ℂ) := by
      have : (A * C)ᴴ * (A * C) = Cᴴ * (Aᴴ * A) * C := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [this, det_mul, det_mul, det_conjTranspose, hreal]
      push_cast
      rw [← Complex.conj_mul' C.det]
      simp only [RCLike.star_def]
      ring
    have hAB : (Aᴴ * B).det = g * C.det := by rw [← hC, det_mul, hreal]
    have hN : ‖(Aᴴ * B).det‖ ^ 2 = g * (g * ‖C.det‖ ^ 2) := by
      rw [hAB, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA0]
      ring
    obtain ⟨-, h2, h3⟩ := H n _ _ (posSemidef_conjTranspose_mul_self (A * C))
      (posSemidef_conjTranspose_mul_self (B - A * C))
    rw [← hsum, hP, Complex.ofReal_re] at h2 h3
    rw [hN]
    refine ⟨mul_le_mul_of_nonneg_left h2 hA0, fun hne hle => ⟨C, ?_⟩⟩
    have hc : C.det ≠ 0 := fun h => hne (by rw [hAB, h, mul_zero])
    have hQ := h3 (by
      have : g * ‖C.det‖ ^ 2 ≠ 0 := mul_ne_zero hg0 (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))
      exact_mod_cast this) (le_of_mul_le_mul_left hle hgpos)
    exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp hQ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetContraction
section
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem gramDet_contraction : (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ η : ℝ, 0 < η ∧ ∀ (i : ℕ), 0 < i → i < r → ∀ M : Matrix (Fin r) (Fin i) ℂ, 0 < (((M)ᴴ * (M)).det.re) → η ≤ ∑ a ∈ S, Real.log ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re))) → (∀ (N : ℕ) (ω η : ℝ), 1 ≤ ω → 0 < η → ∃ δ c : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ ∀ (σ : Type) (S : Finset σ) (t : σ → ℝ), S.card = N → (∀ s ∈ S, ω⁻¹ ≤ t s ∧ t s ≤ ω) → η ≤ ∑ s ∈ S, Real.log (t s) → ∑ s ∈ S, t s ^ (-δ) ≤ N * c) → (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) := by
  intro h1 h2 h3 r S hS hirr
  choose w hw1 hw using h1 r
  obtain ⟨η, hη, hη2⟩ := h2 r S hS hirr
  have hw0 : ∀ a, 0 ≤ w a := fun a => le_trans zero_le_one (hw1 a)
  have hΩ1 : (1:ℝ) ≤ 1 + ∑ a ∈ S, w a := by
    have := Finset.sum_nonneg (s := S) (fun a _ => hw0 a)
    linarith
  have hwΩ : ∀ a ∈ S, w a ≤ 1 + ∑ a ∈ S, w a := by
    intro a ha
    have := Finset.single_le_sum (s := S) (fun a _ => hw0 a) ha
    linarith
  generalize (1 + ∑ a ∈ S, w a) = Ω at hΩ1 hwΩ
  obtain ⟨δ, c, hδ, hc0, hc1, hc⟩ := h3 S.card Ω η hΩ1 hη
  refine ⟨δ, c, Ω, hδ, hc0, hc1, hΩ1, ?_⟩
  intro i M hM
  have hΩ0 : 0 < Ω := lt_of_lt_of_le one_pos hΩ1
  have key : ∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ Ω * (((M)ᴴ * (M)).det.re) ∧
      (((M)ᴴ * (M)).det.re) ≤ Ω * (((a * M)ᴴ * (a * M)).det.re) := by
    intro a ha
    obtain ⟨-, hdet, hinv⟩ := hS a ha
    refine ⟨(hw a (Fin i) M).trans (mul_le_mul_of_nonneg_right (hwΩ a ha) hM.le), ?_⟩
    have h := hw a⁻¹ (Fin i) (a * M)
    have e : a⁻¹ * (a * M) = M := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mul]
    rw [e] at h
    have hpos : 0 < (((a * M)ᴴ * (a * M)).det.re) := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos (hw0 a⁻¹) (not_lt.mp hn)
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right (hwΩ _ hinv) hpos.le)
  refine ⟨key, fun hi hir => ?_⟩
  refine hc _ S (fun a => (((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) rfl ?_
    (hη2 i hi hir M hM)
  intro a ha
  obtain ⟨k1, k2⟩ := key a ha
  refine ⟨?_, (div_le_iff₀ hM).mpr k1⟩
  rw [le_div_iff₀ hM, inv_mul_le_iff₀ hΩ0]
  exact k2

end GlobalTheory
end

