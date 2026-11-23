module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibGlue
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibDis
section
noncomputable section

namespace PI.VolStabSW.DiscreteGroups

open MeasureTheory Topology Set Filter PI.VolStabSW PI.VolStabSW.Glue
open scoped ENNReal

section

variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]

theorem cover (U : Set V) (hU : IsOpen U) : ∃ W : ℕ → Set V,
    (∀ n, IsOpen (W n) ∧ IsCompact (closure (W n)) ∧ closure (W n) ⊆ U) ∧ ⋃ n, W n = U := by
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice U
  have h : ∀ n, ∃ W, IsOpen W ∧ Subtype.val '' E n ⊆ W ∧ closure W ⊆ U ∧ IsCompact (closure W) :=
    fun n => exists_open_between_and_isCompact_closure ((E.isCompact n).image continuous_subtype_val)
      hU (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  choose W hW1 hW2 hW3 hW4 using h
  refine ⟨W, fun n => ⟨hW1 n, hW4 n, hW3 n⟩,
    subset_antisymm (iUnion_subset fun n => subset_closure.trans (hW3 n)) ?_⟩
  intro x hx
  obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
  exact mem_iUnion.2 ⟨n, hW2 n ⟨_, hn, rfl⟩⟩

theorem approx (O : Set V) (hO : IsOpen O) : ∃ φ : ℕ → V → ℝ,
    (∀ k, Continuous (φ k) ∧ HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ O) ∧
    (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧ (∀ x, Monotone fun k => φ k x) ∧
    ∀ x, ⨆ k, ENNReal.ofReal (φ k x) = O.indicator 1 x := by
  haveI : LocallyCompactSpace O := hO.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let E := CompactExhaustion.choice O
  have h : ∀ k, ∃ g : C(V, ℝ), EqOn g 1 (Subtype.val '' E k) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ Subtype.val '' interior (E (k + 1)) ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 := fun k =>
    exists_continuousMap_one_of_isCompact_subset_isOpen ((E.isCompact k).image continuous_subtype_val)
      (hO.isOpenMap_subtype_val _ isOpen_interior) (image_mono (E.subset_interior_succ k))
  choose g hg1 hgc hgs hg01 using h
  have hsubO : ∀ k, tsupport (g k) ⊆ O :=
    fun k => (hgs k).trans (by rintro _ ⟨u, -, rfl⟩; exact u.2)
  have hmono : ∀ x, Monotone fun k => g k x := by
    intro x
    refine monotone_nat_of_le_succ fun k => ?_
    by_cases hx : x ∈ tsupport (g k)
    · obtain ⟨u, hu, rfl⟩ := hgs k hx
      rw [hg1 (k + 1) ⟨u, interior_subset hu, rfl⟩]
      exact (hg01 k _).2
    · rw [image_eq_zero_of_notMem_tsupport hx]
      exact (hg01 (k + 1) x).1
  refine ⟨fun k => g k, fun k => ⟨(g k).continuous, hgc k, hsubO k⟩, fun k x => hg01 k x, hmono,
    fun x => ?_⟩
  by_cases hx : x ∈ O
  · obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
    rw [indicator_of_mem hx]
    apply le_antisymm
    · refine iSup_le fun k => ?_
      have := ENNReal.ofReal_le_ofReal (hg01 k x).2
      simpa using this
    · refine le_iSup_of_le n ?_
      have h1 : g n x = 1 := hg1 n ⟨⟨x, hx⟩, hn, rfl⟩
      show (1 : V → ℝ≥0∞) x ≤ ENNReal.ofReal (g n x)
      rw [h1]
      simp
  · rw [indicator_of_notMem hx]
    simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hsubO _ h))]

variable {X Y : Type} [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}
  (hf : Continuous f) (hι : IsClosedEmbedding ι) (hr : ∀ v, f v ∈ Set.range ι) (hU : IsOpen U)
  (h0 : ∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) (h2 : ∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤)
  (h3 : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν)

include hf hι hr hU h0 h2 h3

theorem cc_case (ψ : V → ℝ) (hψ : IsCcOn U ψ) (h0ψ : ∀ v, 0 ≤ ψ v) :
    ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν := by
  obtain ⟨hint, hcont, hS⟩ := h3 ψ hψ
  set S : Set X := ι ⁻¹' (f '' tsupport ψ) with hSdef
  have hSc : IsCompact S := hι.isCompact_preimage (hψ.2.1.image hf)
  have hsub : tsupport ψ ⊆ f ⁻¹' (ι '' S) := by
    intro v hv
    obtain ⟨s, hs⟩ := hr v
    exact ⟨s, ⟨v, hv, hs.symm⟩, hs⟩
  have hzero : ∀ b ∉ S, ∫ v, ψ v ∂(fib b) = 0 := by
    intro b hb
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ v ∂(fib b), v ∉ (f ⁻¹' {ι b} ∩ U)ᶜ := measure_eq_zero_iff_ae_notMem.1 (h0 b)
    filter_upwards [hae] with v hv
    simp only [mem_compl_iff, not_not] at hv
    exact (eq_or_ne (ψ v) 0).resolve_right fun hne => hb ⟨v, subset_tsupport _ hne, hv.1⟩
  have e1 : ∫ v in f ⁻¹' (ι '' S), ψ v ∂μ = ∫ v, ψ v ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv =>
      image_eq_zero_of_notMem_tsupport fun h => hv (hsub h)
  have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)) ∂ν = ∫ b, (∫ v, ψ v ∂(fib b)) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun b hb => hzero b hb
  have hG : Integrable (fun b => ∫ v, ψ v ∂(fib b)) ν :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro' hSc hSc.isClosed hzero)
  have hi : Integrable ψ μ := hψ.1.integrable_of_hasCompactSupport hψ.2.1
  calc ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ENNReal.ofReal (∫ v, ψ v ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0ψ)).symm
    _ = ENNReal.ofReal (∫ b, (∫ v, ψ v ∂(fib b)) ∂ν) := by rw [← e1, hS S hSc, e2]
    _ = ∫⁻ b, ENNReal.ofReal (∫ v, ψ v ∂(fib b)) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hG
          (ae_of_all _ fun b => integral_nonneg fun v => h0ψ v)
    _ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν :=
        lintegral_congr fun b => ofReal_integral_eq_lintegral_ofReal (hint b) (ae_of_all _ h0ψ)

theorem open_case (O : Set V) (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable (fun b => fib b O) ∧ μ O = ∫⁻ b, fib b O ∂ν := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := approx O hO
  have hcc : ∀ k, IsCcOn U (φ k) := fun k => ⟨(hφ k).1, (hφ k).2.1, (hφ k).2.2.trans hOU⟩
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have hfibO : ∀ b, fib b O = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro b
    rw [← lintegral_iSup hmeas hmon]
    simp_rw [hlim]
    rw [lintegral_indicator_one hO.measurableSet]
  have hk : ∀ k, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro k
    have : (fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b)) =
        fun b => ENNReal.ofReal (∫ v, φ k v ∂(fib b)) :=
      funext fun b => (ofReal_integral_eq_lintegral_ofReal ((h3 _ (hcc k)).1 b)
        (ae_of_all _ fun v => (h01 k v).1)).symm
    rw [this]
    exact ENNReal.measurable_ofReal.comp (h3 _ (hcc k)).2.1.measurable
  have hmonb : Monotone fun k b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) :=
    fun i j hij b => lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hmono v hij)
  refine ⟨?_, ?_⟩
  · simp_rw [hfibO]
    exact Measurable.iSup hk
  · calc μ O = ∫⁻ v, O.indicator 1 v ∂μ := (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂μ := by simp_rw [hlim]
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂μ := lintegral_iSup hmeas hmon
      _ = ⨆ k, ∫⁻ b, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := by
          congr 1; funext k
          exact cc_case hf hι hr hU h0 h2 h3 (φ k) (hcc k) fun v => (h01 k v).1
      _ = ∫⁻ b, ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := (lintegral_iSup hk hmonb).symm
      _ = ∫⁻ b, fib b O ∂ν := by simp_rw [hfibO]

theorem null_compl (b : X) : fib b Uᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 inter_subset_right) (h0 b)

theorem meas_fib : ∀ A, MeasurableSet A → Measurable fun b => fib b A := by
  obtain ⟨W, hW, hWU⟩ := cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hfin : ∀ b n, fib b (W n) ≠ ⊤ := fun b n =>
    (lt_of_le_of_lt (measure_mono subset_closure) (h2 b _ (hW n).2.1 (hW n).2.2)).ne
  have hP : ∀ n, ∀ A, MeasurableSet A → Measurable fun b => fib b (A ∩ W n) := by
    intro n
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => Measurable fun b => fib b (A ∩ W n)) (s := {s : Set V | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_ ?_ ?_
    · simp only [empty_inter, measure_empty]; exact measurable_const
    · intro t ht
      exact (open_case hf hι hr hU h0 h2 h3 (t ∩ W n) ((ht : IsOpen t).inter (hW n).1)
        (inter_subset_right.trans (hWsub n))).1
    · intro t htm IH
      have e : ∀ b, fib b (tᶜ ∩ W n) = fib b (W n) - fib b (t ∩ W n) := by
        intro b
        rw [← measure_diff inter_subset_right (htm.inter (hW n).1.measurableSet).nullMeasurableSet
          ((measure_mono inter_subset_right).trans_lt (lt_top_iff_ne_top.2 (hfin b n))).ne]
        congr 1
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_diff]
        tauto
      simp_rw [e]
      exact (open_case hf hι hr hU h0 h2 h3 (W n) (hW n).1 (hWsub n)).1.sub IH
    · intro g hd hgm IH
      have e : ∀ b, fib b ((⋃ i, g i) ∩ W n) = ∑' i, fib b (g i ∩ W n) := by
        intro b
        rw [iUnion_inter, measure_iUnion (fun i j hij => (hd hij).mono inter_subset_left
          inter_subset_left) (fun i => (hgm i).inter (hW n).1.measurableSet)]
      simp_rw [e]
      exact Measurable.tsum IH
  intro A hA
  have hD : ∀ n, MeasurableSet (disjointed W n) :=
    MeasurableSet.disjointed fun n => (hW n).1.measurableSet
  have e : ∀ b, fib b A = ∑' n, fib b (A ∩ disjointed W n) := by
    intro b
    rw [← measure_inter_add_diff A hU.measurableSet,
      measure_mono_null (show A \ U ⊆ Uᶜ from fun x hx => hx.2) (null_compl hf hι hr hU h0 h2 h3 b),
      add_zero,
      ← hWU, ← iUnion_disjointed, inter_iUnion,
      measure_iUnion (fun i j hij => ((disjoint_disjointed W) hij).mono inter_subset_right
        inter_subset_right) (fun n => hA.inter (hD n))]
  simp_rw [e]
  refine Measurable.tsum fun n => ?_
  have := hP n (A ∩ disjointed W n) (hA.inter (hD n))
  simpa only [inter_eq_left.2 (inter_subset_right.trans (disjointed_subset W n))] using this

end

theorem disintStep_holds : DisintStep := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν hμ hν hpos f ι U hf hι hr hU fib h0 h2 h3 φ hφ
  have hmf : Measurable fib :=
    Measure.measurable_of_measurable_coe fib (meas_fib hf hι hr hU h0 h2 h3)
  have hρ : μ.restrict U = ν.bind fib := by
    obtain ⟨B, hB, hBU⟩ := cover (univ : Set V) isOpen_univ
    refine Measure.ext_of_generateFrom_of_iUnion {s : Set V | IsOpen s} B BorelSpace.measurable_eq
      isPiSystem_isOpen hBU (fun i => (hB i).1) (fun i => ?_) ?_
    · exact ((Measure.restrict_apply_le _ _).trans_lt
        ((measure_mono subset_closure).trans_lt (hB i).2.1.measure_lt_top)).ne
    · intro s hs
      rw [Measure.restrict_apply (hs : IsOpen s).measurableSet,
        Measure.bind_apply hs.measurableSet hmf.aemeasurable,
        (open_case hf hι hr hU h0 h2 h3 (s ∩ U) (hs.inter hU) inter_subset_right).2]
      congr 1
      funext b
      rw [← measure_inter_add_diff s hU.measurableSet,
        measure_mono_null (show s \ U ⊆ Uᶜ from fun x hx => hx.2)
          (null_compl hf hι hr hU h0 h2 h3 b), add_zero]
  rw [hρ, Measure.lintegral_bind hmf.aemeasurable hφ.aemeasurable]

theorem fibOfDens_holds : FibOfDens := fibOfDens_of disintStep_holds

end PI.VolStabSW.DiscreteGroups
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHF
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Filter Set Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Core

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

private lemma module_finite_F_E {W : Type} [MeasurableSpace W] (m : Measure W) (s : Set W)
    (hs : MeasurableSet s) (h : Integrable (s.indicator (1 : W → ℝ)) m) : m s ≠ ⊤ := by
  have h1 := h.lintegral_lt_top
  have e : (fun x => ENNReal.ofReal (s.indicator (1 : W → ℝ) x)) = s.indicator 1 := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [e, lintegral_indicator_one hs] at h1
  exact h1.ne

theorem fib_of_ratio (μ : Measure V) (ν : Measure X) [ν.IsAddHaarMeasure]
    (f : V → Y) (ι : X → Y) (hι : Function.Injective ι) (G : V → X) (hGc : Continuous G)
    (hfG : ∀ x, f x = ι (G x)) (U : Set V) (B : Set X) (fib : X → Measure V)
    (hfib : IsFibreFamily μ f ι U ν B fib) (T : X) (hB : B ∈ 𝓝 T) (Nb : Set X) (hNb : Nb ∈ 𝓝 T)
    (hNbU : ∀ x, G x ∈ Nb → x ∈ U) (Q : Set V) (hQo : IsOpen Q) (hQcl : IsClosed Q)
    (hQc : IsCompact Q) (H : ℕ → AddSubgroup X) (hHo : ∀ n, IsOpen (H n : Set X))
    (hHc : ∀ n, IsCompact (H n : Set X)) (hHb : ∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N')
    (κ : ℝ) (hratio : ∀ n, μ.real (Q ∩ G ⁻¹' {z | z - T ∈ H n}) = κ * ν.real (H n)) :
    ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) = (κ : ℂ) := by
  classical
  obtain ⟨hconc, hdis, hcont⟩ := hfib
  obtain ⟨S, hSdef⟩ : ∃ S : ℕ → Set X, S = fun n => {z | z - T ∈ H n} := ⟨_, rfl⟩
  have hmemS : ∀ n z, z ∈ S n ↔ z - T ∈ H n := by
    intro n z
    rw [hSdef]
    rfl
  have hSo : ∀ n, IsOpen (S n) := by
    intro n
    rw [hSdef]
    exact (hHo n).preimage (continuous_id.sub continuous_const)
  have hScl : ∀ n, IsClosed (S n) := by
    intro n
    rw [hSdef]
    exact (AddSubgroup.isClosed_of_isOpen (H n) (hHo n)).preimage
      (continuous_id.sub continuous_const)
  have hSm : ∀ n, MeasurableSet (S n) := fun n => (hSo n).measurableSet
  have hSc : ∀ n, IsCompact (S n) := by
    intro n
    have e : S n = (fun z => z + T) '' (H n : Set X) := by
      ext z
      constructor
      · intro hz
        exact ⟨z - T, (hmemS n z).1 hz, sub_add_cancel z T⟩
      · rintro ⟨w, hw, rfl⟩
        rw [hmemS]
        simpa using hw
    rw [e]
    exact (hHc n).image (continuous_add_const T)
  have hνS : ∀ n, ν (S n) = ν (H n) := by
    intro n
    have e : S n = (fun z => -T + z) ⁻¹' (H n : Set X) := by
      ext z
      rw [hmemS]
      simp [neg_add_eq_sub]
    rw [e]
    exact measure_preimage_add ν (-T) (H n : Set X)
  have hTS : ∀ n, T ∈ S n := fun n => (hmemS n T).2 (by rw [sub_self]; exact (H n).zero_mem)
  have hsmall : ∀ N ∈ 𝓝 T, ∃ n, S n ⊆ N := by
    intro N hN
    have h0 : (fun x : X => T + x) ⁻¹' N ∈ 𝓝 (0 : X) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hN)
    obtain ⟨n, hn⟩ := hHb _ h0
    refine ⟨n, fun z hz => ?_⟩
    have h := hn ((hmemS n z).1 hz)
    simpa using h
  obtain ⟨n₀, hn₀⟩ := hsmall (Nb ∩ B) (Filter.inter_mem hNb hB)
  have hQ'o : IsOpen (Q ∩ G ⁻¹' S n₀) := hQo.inter ((hSo n₀).preimage hGc)
  have hQ'cl : IsClosed (Q ∩ G ⁻¹' S n₀) := hQcl.inter ((hScl n₀).preimage hGc)
  have hQ'c : IsCompact (Q ∩ G ⁻¹' S n₀) := hQc.of_isClosed_subset hQ'cl Set.inter_subset_left
  have hQ'm : MeasurableSet (Q ∩ G ⁻¹' S n₀) := hQ'o.measurableSet
  have hQ'U : Q ∩ G ⁻¹' S n₀ ⊆ U := fun x hx => hNbU x (hn₀ hx.2).1
  have hS0B : S n₀ ⊆ B := fun z hz => (hn₀ hz).2
  have hfr : frontier (Q ∩ G ⁻¹' S n₀) = ∅ := by
    rw [frontier, hQ'cl.closure_eq, hQ'o.interior_eq, Set.diff_self]
  have hφc : Continuous ((Q ∩ G ⁻¹' S n₀).indicator (1 : V → ℝ)) := by
    rw [← Set.piecewise_eq_indicator]
    exact continuous_one.piecewise (fun a ha => by rw [hfr] at ha; simp at ha) continuous_zero
  have hts : tsupport ((Q ∩ G ⁻¹' S n₀).indicator (1 : V → ℝ)) ⊆ Q ∩ G ⁻¹' S n₀ :=
    closure_minimal Set.support_indicator_subset hQ'cl
  have hφcs : HasCompactSupport ((Q ∩ G ⁻¹' S n₀).indicator (1 : V → ℝ)) :=
    hQ'c.of_isClosed_subset (isClosed_tsupport _) hts
  obtain ⟨hint, hFc0⟩ := hcont _ hφc hφcs (hts.trans hQ'U)
  obtain ⟨F, hFdef⟩ : ∃ F : X → ℝ,
      F = fun b => ∫ v, (Q ∩ G ⁻¹' S n₀).indicator (1 : V → ℝ) v ∂(fib b) := ⟨_, rfl⟩
  have hFc : ContinuousOn F B := by
    rw [hFdef]
    exact hFc0
  have hFval : ∀ b, F b = (fib b (Q ∩ G ⁻¹' S n₀)).toReal := by
    intro b
    simp only [hFdef]
    rw [integral_indicator_one hQ'm, measureReal_def]
  have hF0 : ∀ b, 0 ≤ F b := fun b => by
    rw [hFval]
    exact ENNReal.toReal_nonneg
  have hGb : ∀ b x, x ∈ f ⁻¹' {ι b} ∩ U → G x = b := fun b x hx =>
    hι ((hfG x).symm.trans (Set.mem_singleton_iff.1 hx.1))
  have hfibS : ∀ b (R : Set V), fib b R = fib b (R ∩ (f ⁻¹' {ι b} ∩ U)) :=
    fun b R => (measure_inter_conull (hconc b)).symm
  have hcut : ∀ b m, b ∈ S m →
      (Q ∩ G ⁻¹' S m) ∩ (f ⁻¹' {ι b} ∩ U) = Q ∩ (f ⁻¹' {ι b} ∩ U) := by
    intro b m hb
    ext x
    constructor
    · rintro ⟨⟨hxQ, _⟩, hxA⟩
      exact ⟨hxQ, hxA⟩
    · rintro ⟨hxQ, hxA⟩
      refine ⟨⟨hxQ, ?_⟩, hxA⟩
      show G x ∈ S m
      rw [hGb b x hxA]
      exact hb
  have hfin : ∀ b ∈ B, fib b (Q ∩ G ⁻¹' S n₀) ≠ ⊤ := fun b hb => module_finite_F_E (fib b) _ hQ'm (hint b hb)
  have hmain : ∀ n, S n ⊆ S n₀ → ∫ b in S n, F b ∂ν = κ * ν.real (H n) := by
    intro n hn
    have hSvm : MeasurableSet (Q ∩ G ⁻¹' S n) := (hQo.inter ((hSo n).preimage hGc)).measurableSet
    have hSvU : Q ∩ G ⁻¹' S n ⊆ U := fun x hx => hQ'U ⟨hx.1, hn hx.2⟩
    have h1 := hdis ((Q ∩ G ⁻¹' S n).indicator 1) (measurable_one.indicator hSvm)
    rw [lintegral_indicator_one hSvm, Measure.restrict_apply hSvm, Set.inter_eq_left.2 hSvU] at h1
    simp_rw [lintegral_indicator_one hSvm] at h1
    have hpt : ∀ b, fib b (Q ∩ G ⁻¹' S n) =
        (S n).indicator (fun b => ENNReal.ofReal (F b)) b := by
      intro b
      simp only [Set.indicator_apply]
      split_ifs with hb
      · rw [hfibS b, hcut b n hb, ← hcut b n₀ (hn hb), ← hfibS b, hFval,
          ENNReal.ofReal_toReal (hfin b (hS0B (hn hb)))]
      · rw [hfibS b]
        have e : (Q ∩ G ⁻¹' S n) ∩ (f ⁻¹' {ι b} ∩ U) = ∅ := Set.subset_empty_iff.1 fun x hx =>
          hb (by rw [← hGb b x hx.2]; exact hx.1.2)
        rw [e, measure_empty]
    have h2 : μ (Q ∩ G ⁻¹' S n) = ∫⁻ b in S n, ENNReal.ofReal (F b) ∂ν := by
      rw [h1, lintegral_congr hpt, lintegral_indicator (hSm n)]
    have hFint : IntegrableOn F (S n) ν :=
      (hFc.mono fun z hz => hS0B (hn hz)).integrableOn_compact (hSc n)
    rw [← ofReal_integral_eq_lintegral_ofReal hFint (ae_of_all _ hF0)] at h2
    have hr : μ.real (Q ∩ G ⁻¹' S n) = κ * ν.real (H n) := by
      rw [hSdef]
      exact hratio n
    rw [measureReal_def, h2, ENNReal.toReal_ofReal (integral_nonneg hF0)] at hr
    exact hr
  have hcT : ContinuousAt F T := hFc.continuousAt hB
  have hrpos : ∀ n, 0 < ν.real (H n) := by
    intro n
    rw [measureReal_def]
    exact ENNReal.toReal_pos ((hHo n).measure_ne_zero ν ⟨0, (H n).zero_mem⟩)
      (hHc n).measure_lt_top.ne
  have key : ∀ ε > 0, |κ - F T| ≤ ε := by
    intro ε hε
    have hW : F ⁻¹' Metric.ball (F T) ε ∈ 𝓝 T := hcT (Metric.ball_mem_nhds _ hε)
    obtain ⟨n, hnW⟩ := hsmall _ (Filter.inter_mem hW ((hSo n₀).mem_nhds (hTS n₀)))
    have hsub : S n ⊆ S n₀ := fun z hz => (hnW hz).2
    have hI := hmain n hsub
    have hFint : IntegrableOn F (S n) ν :=
      (hFc.mono fun z hz => hS0B (hsub hz)).integrableOn_compact (hSc n)
    have hclose : ∀ b ∈ S n, |F b - F T| < ε := fun b hb => by
      have h := (hnW hb).1
      rwa [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at h
    have hup : ∫ b in S n, F b ∂ν ≤ ∫ b in S n, (F T + ε) ∂ν :=
      setIntegral_mono_on hFint (continuousOn_const.integrableOn_compact (hSc n)) (hSm n)
        fun b hb => by linarith [(abs_sub_lt_iff.1 (hclose b hb)).1]
    have hlo : ∫ b in S n, (F T - ε) ∂ν ≤ ∫ b in S n, F b ∂ν :=
      setIntegral_mono_on (continuousOn_const.integrableOn_compact (hSc n)) hFint (hSm n)
        fun b hb => by linarith [(abs_sub_lt_iff.1 (hclose b hb)).2]
    rw [setIntegral_const, hI] at hup
    rw [setIntegral_const, hI] at hlo
    simp only [smul_eq_mul, measureReal_def, hνS n] at hup hlo
    have hr := hrpos n
    rw [measureReal_def] at hr
    rw [abs_le]
    constructor <;> nlinarith
  have hk : κ = F T := by
    by_contra hne
    have hpos : 0 < |κ - F T| := abs_pos.2 (sub_ne_zero.2 hne)
    have := key (|κ - F T| / 2) (half_pos hpos)
    linarith
  have hQQ : fib T Q = fib T (Q ∩ G ⁻¹' S n₀) := by
    rw [hfibS T (Q ∩ G ⁻¹' S n₀), hcut T n₀ (hTS n₀), ← hfibS T Q]
  have hint' : ∫ x, Q.indicator (1 : V → ℂ) x ∂(fib T) =
      ∫ x, ((Q.indicator (1 : V → ℝ) x : ℝ) : ℂ) ∂(fib T) :=
    integral_congr_ae (ae_of_all _ fun x => by by_cases hx : x ∈ Q <;> simp [hx])
  rw [hint', integral_complex_ofReal, integral_indicator_one hQo.measurableSet, measureReal_def, hQQ,
    ← hFval, ← hk]

end Core

section Lat

variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] in
theorem cos_inter_eq (Λ0 : AddSubgroup V) (Hn : AddSubgroup X) (G : V → X) (y : V) (T : X) :
    {x | x - y ∈ Λ0} ∩ G ⁻¹' {z | z - T ∈ Hn} = (fun x => -y + x) ⁻¹' hlev Λ0 Hn G y T := by
  ext x
  simp [hlev, neg_add_eq_sub]

theorem cos_ratio (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (T : X) (hyT : G y - T ∈ H 0) (n : ℕ) :
    μ ({x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n}) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  have hset : {x | x - y ∈ Λ 0} ∩ G ⁻¹' {z | z - T ∈ H n} =
      (fun x => -y + x) ⁻¹' hlev (Λ 0) (H n) G y T := cos_inter_eq (Λ 0) (H n) G y T
  rw [hset, measure_preimage_add]
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG T
    (by simpa [neg_sub] using (H 0).neg_mem hyT) n

end Lat

section Fin

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

end Fin

end PI.VolStabSW
end
end

