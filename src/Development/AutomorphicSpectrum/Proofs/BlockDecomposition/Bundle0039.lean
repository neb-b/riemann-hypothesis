module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureComplementImageEqZero
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.SmallUnit

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]

theorem infinite_factor_points {f : A} (hf : NonDiscreteAt f) {W : Set A} (hW : W ∈ 𝓝 (0 : A)) :
    {x | x ∈ W ∧ f * x = x}.Infinite := by
  intro hfin
  have hfin' : ({x | x ∈ W ∧ f * x = x} \ {0}).Finite := hfin.subset Set.diff_subset
  have hV : ({x | x ∈ W ∧ f * x = x} \ {0})ᶜ ∈ 𝓝 (0 : A) :=
    hfin'.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨x, hx, hx0, hfx⟩ := hf _ (inter_mem hW hV)
  exact hx.2 ⟨⟨hx.1, hfx⟩, hx0⟩

theorem measure_complement_image_eq_zero [MeasurableSpace A] [BorelSpace A]
    (h : Measure A) [h.IsAddHaarMeasure] {f : A} (hid : f * f = f) (hf : NonDiscreteAt f)
    {W : Set A} (hWc : IsCompact W) (hW : W ∈ 𝓝 (0 : A)) :
    h ((fun w => (1 - f) * w) '' W) = 0 := by
  set Q : Set A := (fun w => (1 - f) * w) '' W with hQ
  have hQc : IsCompact Q := hWc.image (by fun_prop)
  by_contra hne
  set K : Set A := (fun p : A × A => p.1 + p.2) '' (W ×ˢ Q) with hK
  have hKc : IsCompact K := (hWc.prod hQc).image (by fun_prop)
  have hKfin : h K ≠ ∞ := hKc.measure_lt_top.ne
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hne hKfin
  obtain ⟨T, hTS, hTc⟩ := (infinite_factor_points hf hW).exists_subset_card_eq n
  have hdisj : (T : Set A).PairwiseDisjoint (fun p => (fun q => p + q) '' Q) := by
    intro p hp p' hp' hpp
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩ ⟨_, ⟨w', -, rfl⟩, hEq⟩
    apply hpp
    have hfp : f * p = p := (hTS hp).2
    have hfp' : f * p' = p' := (hTS hp').2
    have hz : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hid, sub_self]
    have := congrArg (fun t => f * t) hEq
    simp only [mul_add, ← mul_assoc, hz, zero_mul, add_zero, hfp, hfp'] at this
    exact this.symm
  have hmeas : ∀ p ∈ T, MeasurableSet ((fun q => p + q) '' Q) := fun p _ =>
    (hQc.image (by fun_prop)).isClosed.measurableSet
  have hsum := measure_biUnion_finset (μ := h) hdisj hmeas
  have each : ∀ p, h ((fun q => p + q) '' Q) = h Q := fun p => by
    rw [Set.image_add_left]
    exact measure_preimage_add h (-p) Q
  have hle : h (⋃ p ∈ T, (fun q => p + q) '' Q) ≤ h K := by
    refine measure_mono (Set.iUnion₂_subset fun p hp => ?_)
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(p, q), ⟨(hTS hp).1, hq⟩, rfl⟩
  rw [hsum, Finset.sum_congr rfl (fun p _ => each p), Finset.sum_const, hTc, nsmul_eq_mul] at hle
  exact absurd hle (not_le.2 hn)

theorem exists_nhds_add_mul_subset {Q W O : Set A} (hQ : IsCompact Q) (hW : IsCompact W)
    (hO : IsOpen O) (hQO : Q ⊆ O) :
    ∃ N ∈ 𝓝 (0 : A), ∀ x ∈ N, ∀ q ∈ Q, ∀ w ∈ W, q + x * w ∈ O := by
  have hn : IsOpen ((fun p : A × A × A => p.2.1 + p.1 * p.2.2) ⁻¹' O) :=
    hO.preimage (by fun_prop)
  obtain ⟨u, v, hu, -, h0u, hQWv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : A)))
    (hQ.prod hW) hn (by
      rintro ⟨x, q, w⟩ ⟨hx, hq, hw⟩
      have hx0 : x = 0 := hx
      simpa [hx0] using hQO hq)
  exact ⟨u, hu.mem_nhds (h0u rfl), fun x hx q hq w hw => huv (Set.mk_mem_prod hx (show (q, w) ∈ v from hQWv ⟨hq, hw⟩))⟩

end GlobalTheory.CompanionTheory.NullFr.SmallUnit

namespace GlobalTheory.CompanionTheory.NullFr


open SmallUnit in
theorem exists_unit_small_module {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A]
    [BorelSpace A] (md : Aˣ →* ℝ≥0) (hmd : IsHaarMod md) (f : A) (hfi : IsFieldIdem f)
    (hnd : NonDiscreteAt f) (ε : ℝ≥0) (hε : 0 < ε) (V : Set A) (hV : V ∈ 𝓝 (0 : A)) :
    ∃ u : Aˣ, (1 - f) * (u : A) = 1 - f ∧ f * (u : A) ∈ V ∧ md u < ε := by
  obtain ⟨W, hWc, hW⟩ := exists_compact_mem_nhds (0 : A)
  let h : Measure A := Measure.addHaar
  have hWpos : 0 < h W := Measure.measure_pos_of_mem_nhds h hW
  have hWfin : h W ≠ ∞ := hWc.measure_lt_top.ne
  set Q : Set A := (fun w => (1 - f) * w) '' W with hQdef
  have hQc : IsCompact Q := hWc.image (by fun_prop)
  have hQ0 : h Q = 0 := measure_complement_image_eq_zero h hfi.idem hnd hWc hW
  have hεW : h Q < (ε : ℝ≥0∞) * h W := by
    rw [hQ0]
    exact ENNReal.mul_pos (by exact_mod_cast hε.ne') hWpos.ne' |>.bot_lt
  obtain ⟨O, hQO, hOo, hOlt⟩ := Q.exists_isOpen_lt_of_lt _ hεW
  obtain ⟨N, hN, hNO⟩ := exists_nhds_add_mul_subset hQc hWc hOo hQO
  obtain ⟨x, ⟨hxN, hxV⟩, hx0, hfx⟩ := hnd _ (inter_mem hN hV)
  obtain ⟨y, hy⟩ := hfi.inv x (by rwa [hfx])
  rw [hfx] at hy
  have hz : f * (1 - f) = 0 := by rw [mul_sub, mul_one, hfi.idem, sub_self]
  have hzz : (1 - f) * (1 - f) = 1 - f := by
    rw [sub_mul, one_mul, hz, sub_zero]
  have hxz : (1 - f) * x = 0 := by rw [← hfx, ← mul_assoc, mul_comm (1 - f), hz, zero_mul]
  have huv : (1 - f + x) * (1 - f + f * y) = 1 := by
    have e : (1 - f + x) * (1 - f + f * y) =
        (1 - f) * (1 - f) + (f * (1 - f)) * y + (1 - f) * x + (f * x) * y := by ring
    rw [e, hzz, hz, hxz, hfx, hy]
    ring
  let u : Aˣ := ⟨1 - f + x, 1 - f + f * y, huv, by rw [mul_comm]; exact huv⟩
  have hu : (u : A) = 1 - f + x := rfl
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [hu, mul_add, hzz, hxz, add_zero]
  · rw [hu, mul_add, hz, zero_add, hfx]
    exact hxV
  · have hmap := hmd h inferInstance u⁻¹
    have hWm : MeasurableSet W := hWc.isClosed.measurableSet
    have hg : Measurable (fun z : A => ((u⁻¹ : Aˣ) : A) * z) := (by fun_prop : Continuous _).measurable
    have hpre : h ((fun z : A => ((u⁻¹ : Aˣ) : A) * z) ⁻¹' W) = (md u : ℝ≥0∞) * h W := by
      rw [← Measure.map_apply hg hWm, hmap, Measure.smul_apply, smul_eq_mul]
      congr 1
      have hm : md u⁻¹ * md u = 1 := by rw [← map_mul]; simp
      have : (md u⁻¹ : ℝ≥0∞) * (md u : ℝ≥0∞) = 1 := by exact_mod_cast hm
      exact (ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])).symm
    have hsub : (fun z : A => ((u⁻¹ : Aˣ) : A) * z) ⁻¹' W ⊆ O := by
      intro z hz'
      have hzw : ((u⁻¹ : Aˣ) : A) * z ∈ W := hz'
      have hzeq : z = (1 - f) * (((u⁻¹ : Aˣ) : A) * z) + x * (((u⁻¹ : Aˣ) : A) * z) := by
        rw [← add_mul, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
      rw [hzeq]
      exact hNO x hxN _ ⟨_, hzw, rfl⟩ _ hzw
    have hlt : (md u : ℝ≥0∞) * h W < (ε : ℝ≥0∞) * h W :=
      lt_of_le_of_lt (hpre ▸ measure_mono hsub) hOlt
    have : (md u : ℝ≥0∞) < ε := lt_of_mul_lt_mul_right' hlt
    exact_mod_cast this

end GlobalTheory.CompanionTheory.NullFr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasureUnitImage
section
open MeasureTheory Topology Filter GlobalTheory.CompanionTheory.NullFr
open scoped NNReal ENNReal Matrix

namespace GlobalTheory.CompanionTheory.NullFr.Packing

theorem exists_max_card {α : Type} (Q : Finset α → Prop) (B : ℕ) (h0 : ∃ P, Q P)
    (hB : ∀ P, Q P → P.card ≤ B) : ∃ P, Q P ∧ ∀ P', Q P' → P'.card ≤ P.card := by
  obtain ⟨P₀, hP₀⟩ := h0
  have hne : {n : ℕ | ∃ P, Q P ∧ P.card = n}.Nonempty := ⟨P₀.card, P₀, hP₀, rfl⟩
  have hbdd : BddAbove {n : ℕ | ∃ P, Q P ∧ P.card = n} := by
    refine ⟨B, ?_⟩
    rintro n ⟨P, hP, rfl⟩
    exact hB P hP
  obtain ⟨P, hP, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨P, hP, fun P' hP' => ?_⟩
  rw [hcard]
  exact le_csSup hbdd ⟨P', hP', rfl⟩

theorem measure_unit_image {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K : Set A} (hK : IsCompact K) :
    h ((fun x : A => (u : A) * x) '' K) = md u * h K := by
  have hc : Continuous fun x : A => (u : A) * x := continuous_const.mul continuous_id
  have hinj : Function.Injective fun x : A => (u : A) * x := fun x y hxy => by
    simpa using congrArg (fun z => ((u⁻¹ : Aˣ) : A) * z) hxy
  have hKu : IsCompact ((fun x : A => (u : A) * x) '' K) := hK.image hc
  have key := congrArg (fun μ : Measure A => μ ((fun x : A => (u : A) * x) '' K))
    (hmd h inferInstance u)
  rw [Measure.map_apply hc.measurable hKu.measurableSet, Set.preimage_image_eq _ hinj,
    Measure.smul_apply, smul_eq_mul] at key
  have hmd0 : ((md u : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    intro h0
    rw [ENNReal.coe_eq_zero] at h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  rw [key, ← mul_assoc, ENNReal.mul_inv_cancel hmd0 ENNReal.coe_ne_top, one_mul]

theorem card_mul_le {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] {md : Aˣ →* ℝ≥0} (hmd : IsHaarMod md)
    (h : Measure A) [h.IsAddHaarMeasure] (u : Aˣ) {K L : Set A} (hK : IsCompact K) (P : Finset A)
    (hdisj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K))
    (hL : ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L) :
    (P.card : ℝ≥0∞) * (md u * h K) ≤ h L := by
  classical
  have hcont : ∀ p : A, Continuous fun x : A => p + (u : A) * x := fun p =>
    continuous_const.add (continuous_const.mul continuous_id)
  have hmT : ∀ p : A, h ((fun x : A => p + (u : A) * x) '' K) = md u * h K := by
    intro p
    have e : (fun x : A => p + (u : A) * x) '' K =
        (fun y => -p + y) ⁻¹' ((fun x : A => (u : A) * x) '' K) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, by abel⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨x, hx, by rw [hxy]; abel⟩
    rw [e, measure_preimage_add, GlobalTheory.CompanionTheory.NullFr.Packing.measure_unit_image hmd h u hK]
  have hsub : (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) ⊆ L := by
    refine Set.iUnion₂_subset fun p hp => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hL p hp w hw
  calc (P.card : ℝ≥0∞) * (md u * h K)
      = ∑ p ∈ P, h ((fun x : A => p + (u : A) * x) '' K) := by
        rw [Finset.sum_congr rfl (fun p _ => hmT p), Finset.sum_const, nsmul_eq_mul]
    _ = h (⋃ p ∈ P, (fun x : A => p + (u : A) * x) '' K) :=
        (measure_biUnion_finset (fun p hp q hq hpq => hdisj p hp q hq hpq)
          (fun p _ => (hK.image (hcont p)).measurableSet)).symm
    _ ≤ h L := measure_mono hsub

theorem net : ∀ {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] (md : Aˣ →* ℝ≥0) (_ : IsHaarMod md) (f : A) (_ : f * f = f) (C U : Set A) (_ : IsCompact C) (_ : U ∈ 𝓝 (0 : A)),
    ∃ (κ : ℝ≥0) (V : Set A), V ∈ 𝓝 (0 : A) ∧ ∀ u : Aˣ, (1 - f) * (u : A) = 1 - f → f * (u : A) ∈ V →
      ∃ N : Finset A, (∀ p ∈ N, f * p = p ∧ p ∈ C) ∧ (N.card : ℝ≥0) * md u ≤ κ ∧
        ∀ c ∈ C, f * c = c → ∃ p ∈ N, ∃ w ∈ U, f * w = w ∧ c = p + u * w := by
  intro A _ _ _ _ _ _ _ _ md hmd f _ C U hC hU
  classical
  have hU' : U ∈ 𝓝 ((0 : A) - 0) := by rwa [sub_zero]
  have h0 : (fun p : A × A => p.1 - p.2) ⁻¹' U ∈ 𝓝 ((0 : A), (0 : A)) :=
    continuous_sub.tendsto ((0 : A), (0 : A)) hU'
  obtain ⟨W₁, hW₁, W₂, hW₂, hW⟩ := mem_nhds_prod_iff.1 h0
  obtain ⟨K, hK0, hKW, hK⟩ := local_compact_nhds (Filter.inter_mem hW₁ hW₂)
  have hKU : ∀ a ∈ K, ∀ b ∈ K, a - b ∈ U := fun a ha b hb =>
    hW (Set.mk_mem_prod (hKW ha).1 (hKW hb).2)
  obtain ⟨V, hV0, -, hV⟩ := local_compact_nhds (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : A))
  obtain ⟨L, hLdef⟩ : ∃ L : Set A,
      L = (fun q : A × A × A => q.1 + q.2.1 * q.2.2 + (1 - f) * q.2.2) '' (C ×ˢ V ×ˢ K) :=
    ⟨_, rfl⟩
  have hLc : IsCompact L := by
    rw [hLdef]
    exact (hC.prod (hV.prod hK)).image (by fun_prop)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure A, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  have hKpos : 0 < μ K := Measure.measure_pos_of_mem_nhds μ hK0
  have hKfin : μ K < ⊤ := hK.measure_lt_top
  have hLfin : μ L < ⊤ := hLc.measure_lt_top
  refine ⟨(μ L / μ K).toNNReal, V, hV0, ?_⟩
  intro u hu1 hfu
  have hmd0 : md u ≠ 0 := by
    intro h0
    have h1 : md u * md u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hm0 : (md u : ℝ≥0∞) * μ K ≠ 0 := mul_ne_zero (by exact_mod_cast hmd0) hKpos.ne'
  have hmtop : (md u : ℝ≥0∞) * μ K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top hKfin.ne
  have hLmem : ∀ P : Finset A, (∀ p ∈ P, f * p = p ∧ p ∈ C) →
      ∀ p ∈ P, ∀ w ∈ K, p + (u : A) * w ∈ L := by
    intro P hP p hp w hw
    rw [hLdef]
    refine ⟨(p, f * u, w), ⟨(hP p hp).2, hfu, hw⟩, ?_⟩
    show p + f * u * w + (1 - f) * w = p + u * w
    rw [← hu1]
    ring
  have hB : ∀ P : Finset A, ((∀ p ∈ P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      Disjoint ((fun x : A => p + (u : A) * x) '' K) ((fun x : A => q + (u : A) * x) '' K)) →
      P.card ≤ ⌈(μ L / ((md u : ℝ≥0∞) * μ K)).toReal⌉₊ := by
    intro P hP
    have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hP.2 (hLmem P hP.1)
    have h1 : (P.card : ℝ≥0∞) ≤ μ L / ((md u : ℝ≥0∞) * μ K) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).2 hc
    have h2 : (P.card : ℝ) ≤ (μ L / ((md u : ℝ≥0∞) * μ K)).toReal := by
      simpa using ENNReal.toReal_mono (ENNReal.div_ne_top hLfin.ne hm0) h1
    exact_mod_cast h2.trans (Nat.le_ceil _)
  obtain ⟨P, ⟨hPC, hPdisj⟩, hmax⟩ :=
    GlobalTheory.CompanionTheory.NullFr.Packing.exists_max_card (hB := hB) (h0 := ⟨∅, by simp⟩)
  refine ⟨P, hPC, ?_, ?_⟩
  · have hc := GlobalTheory.CompanionTheory.NullFr.Packing.card_mul_le hmd μ u hK P hPdisj (hLmem P hPC)
    have h2 : (((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞) ≤ μ L / μ K := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hKpos.ne') (Or.inl hKfin.ne)]
      push_cast
      rw [mul_assoc]
      exact hc
    calc (P.card : ℝ≥0) * md u = ((((P.card : ℝ≥0) * md u : ℝ≥0) : ℝ≥0∞)).toNNReal := by
          rw [ENNReal.toNNReal_coe]
      _ ≤ (μ L / μ K).toNNReal :=
          ENNReal.toNNReal_mono (ENNReal.div_ne_top hLfin.ne hKpos.ne') h2
  · intro c hc hfc
    by_cases hcP : c ∈ P
    · exact ⟨c, hcP, 0, mem_of_mem_nhds hU, by simp, by simp⟩
    · obtain ⟨p, hp, hpc⟩ : ∃ p ∈ P, ¬ Disjoint ((fun x : A => p + (u : A) * x) '' K)
          ((fun x : A => c + (u : A) * x) '' K) := by
        by_contra hcon
        push_neg at hcon
        have hQ : (∀ p ∈ insert c P, f * p = p ∧ p ∈ C) ∧ ∀ p ∈ insert c P, ∀ q ∈ insert c P,
            p ≠ q → Disjoint ((fun x : A => p + (u : A) * x) '' K)
              ((fun x : A => q + (u : A) * x) '' K) := by
          refine ⟨fun p hp => ?_, fun p hp q hq hpq => ?_⟩
          · rcases Finset.mem_insert.1 hp with rfl | hp'
            · exact ⟨hfc, hc⟩
            · exact hPC p hp'
          · rcases Finset.mem_insert.1 hp with rfl | hp' <;>
              rcases Finset.mem_insert.1 hq with rfl | hq'
            · exact absurd rfl hpq
            · exact (hcon q hq').symm
            · exact hcon p hp'
            · exact hPdisj p hp' q hq' hpq
        have hle := hmax _ hQ
        rw [Finset.card_insert_of_notMem hcP] at hle
        omega
      obtain ⟨x, ⟨k₁, hk₁, hx₁⟩, ⟨k₂, hk₂, hx₂⟩⟩ := Set.not_disjoint_iff.1 hpc
      have hx₁' : p + (u : A) * k₁ = x := hx₁
      have hx₂' : c + (u : A) * k₂ = x := hx₂
      have hw : (u : A) * (k₁ - k₂) = c - p := by linear_combination hx₁' - hx₂'
      have hfp : f * p = p := (hPC p hp).1
      refine ⟨p, hp, k₁ - k₂, hKU k₁ hk₁ k₂ hk₂, ?_, by rw [hw]; ring⟩
      calc f * (k₁ - k₂) = ((u⁻¹ : Aˣ) : A) * ((u : A) * (f * (k₁ - k₂))) := by simp
        _ = ((u⁻¹ : Aˣ) : A) * (f * ((u : A) * (k₁ - k₂))) := by ring
        _ = ((u⁻¹ : Aˣ) : A) * ((u : A) * (k₁ - k₂)) := by rw [hw, mul_sub f c p, hfc, hfp]
        _ = k₁ - k₂ := by simp

end GlobalTheory.CompanionTheory.NullFr.Packing
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIdempotentComplementIff
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompIdeal

theorem mem_compI_iff : ∀ {S : Type} [CommRing S] (P : Ideal S), P.IsPrime → ∀ x : S,
    x ∈ compI P ↔ ∃ e, IsIdempotentElem e ∧ e ∉ P ∧ e * x = 0 := by
  intro S _ P hP x
  constructor
  · intro hx
    unfold compI Ideal.span at hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨hi, haP⟩ := ha
      refine ⟨1 - a, hi.one_sub, fun h => hP.ne_top ?_, ?_⟩
      · exact (Ideal.eq_top_iff_one P).2 (by simpa using P.add_mem h haP)
      · rw [sub_mul, one_mul, hi.eq, sub_self]
    | zero => exact ⟨1, IsIdempotentElem.one, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h), mul_zero 1⟩
    | add a b _ _ iha ihb =>
      obtain ⟨e, he, heP, hea⟩ := iha
      obtain ⟨f, hf, hfP, hfb⟩ := ihb
      refine ⟨e * f, he.mul hf, fun h => (hP.mem_or_mem h).elim heP hfP, ?_⟩
      calc e * f * (a + b) = f * (e * a) + e * (f * b) := by ring
        _ = 0 := by rw [hea, hfb, mul_zero, mul_zero, add_zero]
    | smul s a _ ih =>
      obtain ⟨e, he, heP, hea⟩ := ih
      refine ⟨e, he, heP, ?_⟩
      calc e * s • a = s * (e * a) := by rw [smul_eq_mul]; ring
        _ = 0 := by rw [hea, mul_zero]
  · rintro ⟨e, he, heP, hex⟩
    have h0 : e * (1 - e) ∈ P := by
      rw [mul_sub, mul_one, he.eq, sub_self]
      exact P.zero_mem
    have h1 : 1 - e ∈ P := (hP.mem_or_mem h0).resolve_left heP
    have h2 : x = x * (1 - e) := by
      rw [mul_sub, mul_one, mul_comm x e, hex, sub_zero]
    rw [h2]
    exact Ideal.mul_mem_left _ x (Ideal.subset_span ⟨he.one_sub, h1⟩)

end GlobalTheory.CompanionTheory.CompIdeal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulProdCongr
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.RootNear

theorem mul_prod_congr {B ι : Type} [CommRing B] (u : B) (x y : ι → B) (S : Finset ι)
    (h : ∀ j ∈ S, u * x j = u * y j) : u * ∏ j ∈ S, x j = u * ∏ j ∈ S, y j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : u * x a = u * y a := h a (Finset.mem_insert_self a s)
    have h2 : u * ∏ j ∈ s, x j = u * ∏ j ∈ s, y j :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    calc u * (x a * ∏ j ∈ s, x j) = (u * x a) * ∏ j ∈ s, x j := by ring
      _ = (u * y a) * ∏ j ∈ s, x j := by rw [h1]
      _ = y a * (u * ∏ j ∈ s, x j) := by ring
      _ = y a * (u * ∏ j ∈ s, y j) := by rw [h2]
      _ = u * (y a * ∏ j ∈ s, y j) := by ring

theorem exists_shift {B ι : Type} [CommRing B] (I : Ideal B) (c f : ι → B) (S : Finset ι)
    (hf : ∀ j ∈ S, IsIdempotentElem (f j)) (hc : ∀ j ∈ S, f j * c j ∈ I) :
    ∃ s ∈ I, (∏ j ∈ S, (1 - f j)) ∣ ∏ j ∈ S, (c j - s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, I.zero_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, htI, hdvd⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hfa : f a * f a = f a := hf a (Finset.mem_insert_self a s)
    have hca : f a * c a ∈ I := hc a (Finset.mem_insert_self a s)
    refine ⟨(1 - f a) * t + f a * c a, I.add_mem (I.mul_mem_left _ htI) hca, ?_⟩
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcong : (1 - f a) * ∏ j ∈ s, (c j - ((1 - f a) * t + f a * c a)) =
        (1 - f a) * ∏ j ∈ s, (c j - t) :=
      mul_prod_congr (1 - f a) _ _ s (fun j _ => by linear_combination (c a - t) * hfa)
    have hfirst : c a - ((1 - f a) * t + f a * c a) = (1 - f a) * (c a - t) := by ring
    rw [hfirst, mul_comm (1 - f a) (c a - t), mul_assoc, hcong]
    exact Dvd.dvd.mul_left (mul_dvd_mul_left (1 - f a) hdvd) _

theorem root_near (B : Type) [CommRing B] (π : B) (hπ : π ∈ nonZeroDivisors B) (hV : VAL π)
    (d M : ℕ) (b : Fin d → B) (a : B) (hd : 0 < d)
    (hprod : ∏ j, (a - b j) ∈ Ideal.span {π ^ (d * M)}) :
    ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ ∏ j, (a₁ - b j) = 0 := by
  classical
  have key : ∀ j : Fin d, ∃ e : B, IsIdempotentElem e ∧ e * (a - b j) ∈ Ideal.span {π ^ M} ∧
      (1 - e) * π ^ M ∈ Ideal.span {a - b j} := fun j =>
    hV (a - b j) (π ^ M) ⟨M, Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  choose e he1 he2 he3 using key
  have hee : ∀ j, e j * e j = e j := fun j => he1 j
  have hr : ∀ j, ∃ r : B, (1 - e j) * π ^ M = (a - b j) * r := fun j =>
    Ideal.mem_span_singleton.mp (he3 j)
  choose r hr using hr
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hprod
  obtain ⟨j0, -⟩ : ∃ j : Fin d, True := ⟨⟨0, hd⟩, trivial⟩
  obtain ⟨E, hEdef⟩ : ∃ E : B, E = ∏ j, (1 - e j) := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hEdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by linear_combination hee j)
  have hEj : ∀ j, E * (1 - e j) = E := by
    intro j
    have hsplit : (1 - e j) * ∏ i ∈ Finset.univ.erase j, (1 - e i) = E := by
      rw [hEdef]; exact Finset.mul_prod_erase _ (fun i => 1 - e i) (Finset.mem_univ j)
    rw [← hsplit]
    linear_combination (∏ i ∈ Finset.univ.erase j, (1 - e i)) * hee j
  have hT : ∀ j, (a - b j) * (E * r j) = E * π ^ M := by
    intro j
    calc (a - b j) * (E * r j) = E * ((a - b j) * r j) := by ring
      _ = E * ((1 - e j) * π ^ M) := by rw [← hr j]
      _ = (E * (1 - e j)) * π ^ M := by ring
      _ = E * π ^ M := by rw [hEj j]
  have hEpow : ∀ n : ℕ, E ^ (n + 1) = E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hEE]
  have hEd : E ^ d = E := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', hEpow]
  have hmain : π ^ (d * M) * (q * ∏ j, (E * r j)) = π ^ (d * M) * E := by
    calc π ^ (d * M) * (q * ∏ j, (E * r j)) = (∏ j, (a - b j)) * ∏ j, (E * r j) := by
          rw [hq]; ring
      _ = ∏ j, ((a - b j) * (E * r j)) := Finset.prod_mul_distrib.symm
      _ = ∏ _j : Fin d, (E * π ^ M) := Finset.prod_congr rfl (fun j _ => hT j)
      _ = π ^ (d * M) * E := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, hEd, ← pow_mul,
            mul_comm M d]
          ring
  have hpow : π ^ (d * M) ∈ nonZeroDivisors B := pow_mem hπ _
  have hET : E = q * ∏ j, (E * r j) := by
    have h0 : (q * ∏ j, (E * r j) - E) * π ^ (d * M) = 0 := by linear_combination hmain
    exact (sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hpow).2 _ h0)).symm
  have hEa : E * (a - b j0) ∈ Ideal.span {π ^ M} := by
    rw [Ideal.mem_span_singleton]
    have hsplit : (E * r j0) * ∏ i ∈ Finset.univ.erase j0, (E * r i) = ∏ i, (E * r i) :=
      Finset.mul_prod_erase _ (fun i => E * r i) (Finset.mem_univ j0)
    refine ⟨q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E, ?_⟩
    calc E * (a - b j0) = q * (∏ i, (E * r i)) * (a - b j0) := by rw [← hET]
      _ = q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * ((a - b j0) * (E * r j0)) := by
          rw [← hsplit]; ring
      _ = π ^ M * (q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E) := by rw [hT j0]; ring
  obtain ⟨s, hs, w, hw⟩ := exists_shift (Ideal.span {π ^ M}) (fun j => a - b j) e Finset.univ
    (fun j _ => he1 j) (fun j _ => he2 j)
  have hw' : ∏ j, (a - b j - s) = E * w := by rw [hEdef]; exact hw
  obtain ⟨a₁, ha₁⟩ : ∃ x : B, x = (1 - E) * (a - s) + E * b j0 := ⟨_, rfl⟩
  refine ⟨a₁, ?_, ?_⟩
  · have h1 : a₁ - a = (E - 1) * s - E * (a - b j0) := by rw [ha₁]; ring
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hs) hEa
  · have hsplit2 : (a₁ - b j0) * ∏ i ∈ Finset.univ.erase j0, (a₁ - b i) = ∏ i, (a₁ - b i) :=
      Finset.mul_prod_erase _ (fun i => a₁ - b i) (Finset.mem_univ j0)
    have hE0 : E * ∏ i, (a₁ - b i) = 0 := by
      rw [← hsplit2]
      linear_combination E * (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * ha₁ +
        (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * (b j0 - (a - s)) * hEE
    have hcong : (1 - E) * ∏ i, (a₁ - b i) = (1 - E) * ∏ i, (a - b i - s) :=
      mul_prod_congr (1 - E) _ _ Finset.univ
        (fun j _ => by linear_combination (1 - E) * ha₁ + (a - s - b j0) * hEE)
    calc ∏ i, (a₁ - b i) = E * ∏ i, (a₁ - b i) + (1 - E) * ∏ i, (a₁ - b i) := by ring
      _ = 0 + (1 - E) * ∏ i, (a - b i - s) := by rw [hE0, hcong]
      _ = 0 := by rw [hw']; linear_combination (-w) * hEE

end GlobalTheory.CompanionTheory.RootNear
end

