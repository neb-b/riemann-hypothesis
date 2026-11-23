module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairOmSumSameDatumLe
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactArrFiniteDimensional
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProd
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Filter Topology
open scoped ENNReal

namespace GlobalTheory.LeviIso

def SublevelLe {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] (c : ℝ≥0∞) (T : ℝ)
    (μ : Measure X) (q : X → ℝ) (μ' : Measure X') (q' : X' → ℝ) : Prop :=
  ∀ t ≤ T, μ {x | q x ≤ t} ≤ c * μ' {x | q' x ≤ t}

theorem SublevelLe.mono {X X' : Type} [MeasurableSpace X] [MeasurableSpace X'] {c : ℝ≥0∞}
    {T T' : ℝ} {μ : Measure X} {q : X → ℝ} {μ' : Measure X'} {q' : X' → ℝ}
    (h : SublevelLe c T μ q μ' q') (hT : T' ≤ T) : SublevelLe c T' μ q μ' q' :=
  fun t ht => h t (ht.trans hT)

theorem SublevelLe.prod {X X' Y Y' : Type} [MeasurableSpace X] [MeasurableSpace X']
    [MeasurableSpace Y] [MeasurableSpace Y'] {c : ℝ≥0∞} {T : ℝ}
    {μ : Measure X} {q : X → ℝ} {μ' : Measure X'} {q' : X' → ℝ}
    {ν : Measure Y} {p : Y → ℝ} {ν' : Measure Y'} {p' : Y' → ℝ}
    [SFinite μ] [SFinite μ'] [SFinite ν] [SFinite ν'] (hc : c ≠ ⊤)
    (hq : Measurable q) (hq' : Measurable q') (hp : Measurable p) (hp' : Measurable p')
    (hq0 : ∀ x, 0 ≤ q' x) (hp0 : ∀ y, 0 ≤ p y)
    (h1 : SublevelLe c T μ q μ' q') (h2 : SublevelLe c T ν p ν' p') :
    SublevelLe (c * c) T (μ.prod ν) (fun z => q z.1 + p z.2) (μ'.prod ν')
      (fun z => q' z.1 + p' z.2) := by
  intro t ht
  have m1 : MeasurableSet {z : X × Y | q z.1 + p z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have m2 : MeasurableSet {z : X' × Y | q' z.1 + p z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have m3 : MeasurableSet {z : X' × Y' | q' z.1 + p' z.2 ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  have s1 : (μ.prod ν) {z : X × Y | q z.1 + p z.2 ≤ t}
      ≤ c * (μ'.prod ν) {z : X' × Y | q' z.1 + p z.2 ≤ t} := by
    rw [Measure.prod_apply_symm m1, Measure.prod_apply_symm m2, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono fun y => ?_
    have := h1 (t - p y) (by linarith [hp0 y])
    simpa only [Set.preimage_setOf_eq, le_sub_iff_add_le] using this
  have s2 : (μ'.prod ν) {z : X' × Y | q' z.1 + p z.2 ≤ t}
      ≤ c * (μ'.prod ν') {z : X' × Y' | q' z.1 + p' z.2 ≤ t} := by
    rw [Measure.prod_apply m2, Measure.prod_apply m3, ← lintegral_const_mul' _ _ hc]
    refine lintegral_mono fun x => ?_
    have := h2 (t - q' x) (by linarith [hq0 x])
    simpa only [Set.preimage_setOf_eq, le_sub_iff_add_le'] using this
  calc _ ≤ _ := s1
    _ ≤ c * (c * _) := by gcongr
    _ = _ := by rw [mul_assoc]

theorem volume_norm_sq_le (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ r ^ 2}
      = ENNReal.ofReal (r ^ d) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  have : {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ r ^ 2} = Metric.closedBall 0 r := by
    ext u
    simp [sq_le_sq₀ (norm_nonneg u) hr]
  rw [this, Measure.addHaar_closedBall _ _ hr]
  simp

theorem setOf_sqrt_le {X : Type} (q : X → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {x | √(q x) ≤ r} = {x | q x ≤ r ^ 2} := by
  ext x
  simp [Real.sqrt_le_left hr, Real.sqrt_le_iff, hr]

theorem volume_prod_norm_sq_le (d e : ℕ) (t : ℝ) :
    ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod
      (volume : Measure (EuclideanSpace ℝ (Fin e)))) {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ t}
      = volume {u : EuclideanSpace ℝ (Fin (d + e)) | ‖u‖ ^ 2 ≤ t} := by
  let f : WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (d + e)) :=
    ((stdOrthonormalBasis ℝ _).reindex (finCongr (by
      rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]; simp))).repr
  have h := f.measurePreserving.comp (WithLp.volume_preserving_toLp _ _)
  rw [← h.measure_preimage (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet]
  congr 1
  ext z
  simp [WithLp.prod_norm_sq_eq_of_L2]

theorem exists_one_lt_mul_mul_lt {a b : ℝ≥0∞} (h : a < b) :
    ∃ c : ℝ≥0∞, 1 < c ∧ c ≠ ⊤ ∧ c * c * a < b := by
  have ha : a ≠ ⊤ := h.ne_top
  have t1 : Tendsto (fun c : ℝ≥0∞ => c * c * a) (𝓝 1) (𝓝 (1 * 1 * a)) :=
    ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.mul tendsto_id (by simp) tendsto_id (by simp)) (Or.inr ha)
  simp only [one_mul] at t1
  have e1 := t1.eventually (gt_mem_nhds h)
  have e2 : ∀ᶠ c : ℝ≥0∞ in 𝓝 1, c < ⊤ := gt_mem_nhds (by simp)
  haveI : (𝓝[>] (1 : ℝ≥0∞)).NeBot := nhdsGT_neBot_of_exists_gt ⟨⊤, by simp⟩
  obtain ⟨c, ⟨h1, h2⟩, h3⟩ := (((e1.and e2).filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ≥0∞)) (a := 1))).exists
  exact ⟨c, h3, h2.ne, h1⟩

theorem IsRadial.sublevelLe {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℝ} {d : ℕ}
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (h : IsRadial μ q d) {c : ℝ≥0∞} (hc : 1 < c)
    (hc' : c ≠ ⊤) :
    ∃ T > 0, SublevelLe c T μ q volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) ∧
      SublevelLe c T volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) μ q := by
  unfold IsRadial at h
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ω0 : ω ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have ωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have hlt : ω < c * ω := by
    simpa using ENNReal.mul_lt_mul_left ω0 ωt hc
  have e1 := h.eventually (gt_mem_nhds hlt)
  have e2 := (ENNReal.Tendsto.const_mul (a := c) h (Or.inl ω0)).eventually (lt_mem_nhds hlt)
  have e3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ {x | √(q x) ≤ r} ≤ c * (ENNReal.ofReal (r ^ d) * ω) ∧
      ENNReal.ofReal (r ^ d) * ω ≤ c * μ {x | √(q x) ≤ r} := by
    filter_upwards [e1, e2, self_mem_nhdsWithin] with r h1 h2 hr
    have hr' : (0 : ℝ) < r := hr
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    constructor
    · have := (ENNReal.div_le_iff n0 ENNReal.ofReal_ne_top).1 h1.le
      calc _ ≤ _ := this
        _ = _ := by ring
    · rw [← mul_div_assoc] at h2
      have := (ENNReal.le_div_iff_mul_le (Or.inl n0) (Or.inl ENNReal.ofReal_ne_top)).1 h2.le
      rwa [mul_comm] at this
  have tg : Tendsto (fun r : ℝ => μ {x | √(q x) ≤ r}) (𝓝[>] 0) (𝓝 (μ {x | √(q x) ≤ 0})) := by
    have hI : {x | √(q x) ≤ 0} = ⋂ r > (0 : ℝ), {x | √(q x) ≤ r} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h r hr => h.trans hr.le, fun h => le_of_forall_gt_imp_ge_of_dense h⟩
    rw [hI]
    refine tendsto_measure_biInter_gt (s := fun r : ℝ => {x | √(q x) ≤ r})
      (fun r _ => (measurableSet_le (by fun_prop) measurable_const).nullMeasurableSet)
      (fun i j _ hij x hx => le_trans hx hij) ?_
    obtain ⟨r, h1, h2⟩ := (e3.and self_mem_nhdsWithin).exists
    exact ⟨r, h2, ne_top_of_le_ne_top
      (ENNReal.mul_ne_top hc' (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ωt)) h1.1⟩
  have th : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ d) * ω) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ d) * ω)) :=
    ENNReal.Tendsto.mul_const
      (((ENNReal.continuous_ofReal.comp (continuous_pow d)).tendsto 0).mono_left
        nhdsWithin_le_nhds) (Or.inr ωt)
  have z1 := le_of_tendsto_of_tendsto tg (ENNReal.Tendsto.const_mul (a := c) th (Or.inr hc'))
    (e3.mono fun r h => h.1)
  have z2 := le_of_tendsto_of_tendsto th (ENNReal.Tendsto.const_mul (a := c) tg (Or.inr hc'))
    (e3.mono fun r h => h.2)
  obtain ⟨δ, hδ, hs⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 e3
  have hδ' : (0 : ℝ) < δ := hδ
  have key : ∀ r, 0 ≤ r → r ≤ δ → μ {x | √(q x) ≤ r} ≤ c * (ENNReal.ofReal (r ^ d) * ω) ∧
      ENNReal.ofReal (r ^ d) * ω ≤ c * μ {x | √(q x) ≤ r} := by
    intro r h0 h1
    rcases h0.eq_or_lt with rfl | h0
    · exact ⟨z1, z2⟩
    · exact hs ⟨h0, h1⟩
  have key2 : ∀ t ≤ δ ^ 2,
      μ {x | q x ≤ t} ≤ c * volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} ∧
      volume {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} ≤ c * μ {x | q x ≤ t} := by
    intro t ht
    rcases lt_or_ge t 0 with h0 | h0
    · have a1 : {x | q x ≤ t} = ∅ := by
        ext x; simp; linarith [hq0 x]
      have a2 : {u : EuclideanSpace ℝ (Fin d) | ‖u‖ ^ 2 ≤ t} = ∅ := by
        ext x; simp; nlinarith [sq_nonneg ‖x‖]
      simp [a1, a2]
    · have := key (√t) (Real.sqrt_nonneg _) (Real.sqrt_le_iff.2 ⟨hδ'.le, ht⟩)
      rw [← volume_norm_sq_le d (Real.sqrt_nonneg _), setOf_sqrt_le q (Real.sqrt_nonneg _),
        Real.sq_sqrt h0] at this
      exact this
  exact ⟨δ ^ 2, by positivity, fun t ht => (key2 t ht).1, fun t ht => (key2 t ht).2⟩

theorem isRadial_of_sublevelLe {X : Type} [MeasurableSpace X] {μ : Measure X} {q : X → ℝ} {d : ℕ}
    (h : ∀ c : ℝ≥0∞, 1 < c → c ≠ ⊤ → ∃ T > 0,
      SublevelLe (c * c) T μ q volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) ∧
      SublevelLe (c * c) T volume (fun u : EuclideanSpace ℝ (Fin d) => ‖u‖ ^ 2) μ q) :
    IsRadial μ q d := by
  unfold IsRadial
  have hv := fun r => volume_norm_sq_le d (r := r)
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ev : ∀ T > (0 : ℝ), ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r ^ 2 ≤ T := by
    intro T hT
    filter_upwards [Ioc_mem_nhdsGT (Real.sqrt_pos.2 hT)] with r hr
    exact ⟨hr.1, (Real.le_sqrt hr.1.le hT.le).1 hr.2⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨c, c1, c2, c3⟩ := exists_one_lt_mul_mul_lt ha
    obtain ⟨T, hT, -, h2⟩ := h c c1 c2
    filter_upwards [ev T hT] with r ⟨hr, hrT⟩
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := h2 _ hrT
    rw [hv r hr.le, ← setOf_sqrt_le q hr.le, mul_comm,
      ← ENNReal.le_div_iff_mul_le (Or.inl n0) (Or.inl ENNReal.ofReal_ne_top),
      mul_div_assoc] at this
    by_contra hn
    have h3 : c * c * (μ {x | √(q x) ≤ r} / ENNReal.ofReal (r ^ d)) ≤ c * c * a := by
      gcongr; exact not_lt.1 hn
    exact absurd (c3.trans_le (this.trans h3)) (lt_irrefl _)
  · obtain ⟨c, c1, c2, c3⟩ := exists_one_lt_mul_mul_lt ha
    obtain ⟨T, hT, h1, -⟩ := h c c1 c2
    filter_upwards [ev T hT] with r ⟨hr, hrT⟩
    have n0 : ENNReal.ofReal (r ^ d) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have := h1 _ hrT
    rw [hv r hr.le, ← setOf_sqrt_le q hr.le] at this
    refine lt_of_le_of_lt ?_ c3
    rw [ENNReal.div_le_iff n0 ENNReal.ofReal_ne_top]
    calc _ ≤ _ := this
      _ = _ := by ring

theorem isRadial_prod : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (q : X → ℝ) (p : Y → ℝ) (d e : ℕ), Measurable q → Measurable p → (∀ x, 0 ≤ q x) → (∀ y, 0 ≤ p y) → IsRadial μ q d → IsRadial ν p e → IsRadial (μ.prod ν) (fun z => q z.1 + p z.2) (d + e) := by
  intro X Y _ _ μ ν _ _ q p d e hq hp hq0 hp0 h1 h2
  refine isRadial_of_sublevelLe fun c c1 c2 => ?_
  obtain ⟨T, hT, a1, a2⟩ := h1.sublevelLe hq hq0 c1 c2
  obtain ⟨T', hT', b1, b2⟩ := h2.sublevelLe hp hp0 c1 c2
  refine ⟨min T T', lt_min hT hT', fun t ht => ?_, fun t ht => ?_⟩
  · have := SublevelLe.prod c2 hq (by fun_prop) hp (by fun_prop) (fun _ => by positivity) hp0
      (a1.mono (min_le_left _ _)) (b1.mono (min_le_right _ _)) t ht
    rwa [volume_prod_norm_sq_le] at this
  · have := SublevelLe.prod c2 (by fun_prop) hq (by fun_prop) hp hq0 (fun _ => by positivity)
      (a2.mono (min_le_left _ _)) (b2.mono (min_le_right _ _)) t ht
    rwa [volume_prod_norm_sq_le] at this

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFrameWeightSumSameDatumLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt

theorem tsum_ite_le_sum_fibres {α β : Type*} (Q : α → Prop) (R : β → α → Prop) (f : α → ℝ≥0∞) (S : Finset β)
    [∀ a, Decidable (Q a)] [∀ p a, Decidable (R p a)]
    (h : ∀ a, Q a → ∃ p ∈ S, R p a) :
    (∑' a, if Q a then f a else 0) ≤ ∑ p ∈ S, ∑' a, if R p a then f a else 0 := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine ENNReal.tsum_le_tsum fun a => ?_
  split_ifs with hq
  · obtain ⟨p, hp, hr⟩ := h a hq
    refine le_trans ?_ (Finset.single_le_sum (f := fun p => if R p a then f a else 0)
      (fun _ _ => zero_le) hp)
    simp [hr]
  · exact zero_le

theorem cf_nonneg_of_numberField (K : Type) [Field K] [NumberField K] : 0 ≤ cf K := by
  have h : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have := Real.logb_nonneg (b := 2) (by norm_num) h
  unfold cf
  linarith

theorem index_pair_bound {G D c X : ℝ} (k i b : ℕ) (hG : 0 < G) (hc : 0 ≤ c) (hX : 0 ≤ X)
    (h : G * (i : ℝ) ^ 2 * (b : ℝ) ^ 2 ≤ D) (hi : (i : ℝ) ≤ D) :
    ((i : ℝ) * b) ^ k * (i : ℝ) ^ c * X ≤ (D / G) ^ ((k : ℝ) / 2) * D ^ c * X := by
  have h0 : (0 : ℝ) ≤ (i : ℝ) * b := by positivity
  have h1 : ((i : ℝ) * b) ^ 2 ≤ D / G := by
    rw [le_div_iff₀ hG]; nlinarith
  have h2 : ((i : ℝ) * b) ^ k ≤ (D / G) ^ ((k : ℝ) / 2) := by
    calc ((i : ℝ) * b) ^ k = (((i : ℝ) * b) ^ 2) ^ ((k : ℝ) / 2) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul h0, ← Real.rpow_natCast]
          congr 1; push_cast; ring
      _ ≤ _ := Real.rpow_le_rpow (by positivity) h1 (by positivity)
  have h3 : (i : ℝ) ^ c ≤ D ^ c := Real.rpow_le_rpow (by positivity) hi hc
  have h4 : 0 ≤ (D / G) ^ ((k : ℝ) / 2) := le_trans (by positivity) h2
  gcongr

theorem omSum_sameDat_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ') ≤ ENNReal.ofReal ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ (cf K + 2) * (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hΛ
  obtain ⟨-, hG, hI, -, hGI, -⟩ := _root_.GlobalTheory.DegCnt.FixIdx.main K V H hK r N g Λ hg hΛ
  have hG1 : (1 : ℝ) ≤ N.gI g Λ := by exact_mod_cast hG
  have hI1 : (1 : ℝ) ≤ N.iI g Λ := by exact_mod_cast hI
  have hD : 1 ≤ N.Del := le_trans (by nlinarith) hGI
  have hnD : ∀ l, 0 ≤ N.nD l := fun l => by
    unfold NF.nD
    split_ifs
    · positivity
    · exact le_rfl
  have hDb : 0 ≤ N.Db := Finset.prod_nonneg fun l _ => hnD l
  have hNT : 0 ≤ N.NT := by unfold NF.NT; positivity
  have hX : 0 ≤ (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) := by positivity
  set X := (N.Db * N.Del * N.NT) ^ (10000 * (r + 1) ^ 3) with hXdef
  set S : Finset (ℕ × ℕ) := (Finset.Icc 1 ⌊N.Del⌋₊ ×ˢ Finset.Icc 1 ⌊N.Del⌋₊).filter
    (fun p => (N.gI g Λ : ℝ) * (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2 ≤ N.Del) with hS
  have hcard : (S.card : ℝ) ≤ N.Del ^ 2 := by
    have h1 : S.card ≤ ⌊N.Del⌋₊ * ⌊N.Del⌋₊ := by
      refine (Finset.card_filter_le _ _).trans ?_
      simp
    have h2 : (⌊N.Del⌋₊ : ℝ) ≤ N.Del := Nat.floor_le (by linarith)
    calc (S.card : ℝ) ≤ (⌊N.Del⌋₊ : ℝ) * ⌊N.Del⌋₊ := by exact_mod_cast h1
      _ ≤ N.Del * N.Del := by gcongr
      _ = _ := by ring
  have hcover : ∀ Λ' : Submodule (𝓞 K) V, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' →
      ∃ p ∈ S, N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2 := by
    rintro Λ' ⟨h1, h2⟩
    refine ⟨(N.iI g Λ', N.bI Λ'), ?_, h1, h2, rfl, rfl⟩
    obtain ⟨-, -, hI', hb, -⟩ := _root_.GlobalTheory.DegCnt.FixIdx.main K V H hK r N g Λ' hg h1
    have hb0 := (_root_.GlobalTheory.DegCnt.SplitIdx.main K V H hK r N g Λ' hg h1).1
    have hgg : N.gI g Λ' = N.gI g Λ := by
      unfold NF.gI flagPairDefinitePartLattice latLa
      rw [h2.1, h2.2.2]
    rw [hgg] at hb
    have hi1 : (1 : ℝ) ≤ N.iI g Λ' := by exact_mod_cast hI'
    have hb1 : (1 : ℝ) ≤ N.bI Λ' := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb0
    have hi2 : (N.iI g Λ' : ℝ) ≤ (N.iI g Λ' : ℝ) ^ 2 := by nlinarith only [hi1]
    have hb2 : (N.bI Λ' : ℝ) ≤ (N.bI Λ' : ℝ) ^ 2 := by nlinarith only [hb1]
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨hI', Nat.le_floor ?_⟩, Nat.one_le_iff_ne_zero.2 hb0, Nat.le_floor ?_⟩, hb⟩
    · refine le_trans ?_ hb
      calc (N.iI g Λ' : ℝ) = 1 * (N.iI g Λ' : ℝ) * 1 := by ring
        _ ≤ _ := by gcongr; linarith
    · refine le_trans ?_ hb
      calc (N.bI Λ' : ℝ) = 1 * 1 * (N.bI Λ' : ℝ) := by ring
        _ ≤ _ := by gcongr; linarith
  have hc := cf_nonneg_of_numberField K
  have hY : 0 ≤ (N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X := by
    have : 0 ≤ N.Del := by linarith
    positivity
  calc N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ')
      ≤ ∑ p ∈ S, N.omSum (fun Λ' => N.IsTerm g Λ' ∧ N.SameDat g Λ Λ' ∧ N.iI g Λ' = p.1 ∧ N.bI Λ' = p.2) := by
        unfold NF.omSum
        exact @tsum_ite_le_sum_fibres _ _ _ _ _ S (fun _ => Classical.propDecidable _)
          (fun _ _ => Classical.propDecidable _) fun o ho => hcover _ ho
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X) := by
        refine Finset.sum_le_sum fun p hp => ?_
        refine (_root_.GlobalTheory.DegCnt.OmCount.main K V H hK r N g Λ hg hΛ p.1 p.2).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        refine index_pair_bound _ _ _ (by linarith) hc hX hp.2 ?_
        exact le_trans (by exact_mod_cast hp.1.1.2) (Nat.floor_le (by linarith : 0 ≤ N.Del))
    _ = ENNReal.ofReal (S.card *
          ((N.Del / N.gI g Λ) ^ ((Module.finrank K N.Wt : ℝ) / 2) * N.Del ^ cf K * X)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_right hcard hY).trans (le_of_eq ?_))
        rw [Real.rpow_add (by linarith), Real.rpow_two]
        ring

end GlobalTheory.DegCnt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightDerivativeSumZero
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.Schmid

theorem rhoN_add_rhoC {n : ℕ} (ε : Fin n → Bool) (a : Fin n) :
    Formalism.REAL.rhoN ε a + Formalism.REAL.rhoC ε a = ((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ) := by
  have h1 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      = n - 1 - a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h2 : (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
      = a := by
    rw [← Finset.filter_filter, ← Finset.filter_filter, Finset.card_filter_add_card_filter_not,
      Finset.filter_gt_eq_Iio, Fin.card_Iio]
  have ha := a.2
  have h3 : (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
      + a + 1 = n := by omega
  have h3' := congrArg (Nat.cast : ℕ → ℝ) h3
  have h2' := congrArg (Nat.cast : ℕ → ℝ) h2
  push_cast at h3' h2'
  unfold Formalism.REAL.rhoN Formalism.REAL.rhoC
  linarith

theorem nsq_sub_root {n : ℕ} (u : Fin n → ℝ) {a b : Fin n} (hab : a ≠ b) :
    Formalism.REAL.nsq (u - Formalism.REAL.root a b) = Formalism.REAL.nsq u - 2 * (u a - u b) + 2 := by
  have : ∀ i, (u - Formalism.REAL.root a b) i * (u - Formalism.REAL.root a b) i =
      u i * u i - 2 * ((if i = a then u i else 0) - (if i = b then u i else 0)) +
        ((if i = a then 1 else 0) + (if i = b then 1 else 0)) := by
    intro i
    simp only [Formalism.REAL.root, Pi.sub_apply, Pi.single_apply]
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h1.symm.trans h2) hab
    all_goals simp [h1, h2, hab, hab.symm]
    all_goals ring
  simp only [Formalism.REAL.nsq, Formalism.REAL.dot, this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  norm_num

theorem vNormSq_sub_root_lt {n : ℕ} (ε : Fin n → Bool) {μ : Fin n → ℝ} (hμ : StrictAnti μ)
    {a b : Fin n} (hab : a < b) :
    Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b) < Formalism.MainNotions.S.vNormSq ε (Formalism.QuantumDeterminants.lowK ε μ) := by
  unfold Formalism.MainNotions.S.vNormSq
  rw [show Formalism.QuantumDeterminants.lowK ε μ - Formalism.REAL.root a b + (2 : ℝ) • Formalism.REAL.rhoC ε
      = (Formalism.QuantumDeterminants.lowK ε μ + (2 : ℝ) • Formalism.REAL.rhoC ε) - Formalism.REAL.root a b by abel,
    nsq_sub_root _ hab.ne]
  have h1 := hμ hab
  have h2 := rhoN_add_rhoC ε a
  have h3 := rhoN_add_rhoC ε b
  have h4 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Formalism.QuantumDeterminants.lowK, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

theorem thetaA_one {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (G : Arr V n 1) :
    thetaA E 1 G = ∑ a, ∑ b, E a b (at1 G a b) := by
  rw [theta_map_word_sum_apply, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin n × Fin n)) _ _ fun α => ?_
  have h : α = fun _ => (α 0) := fin_one_fun_eq_const_apply_zero α
  have e : at1 G (α 0).1 (α 0).2 = G α := by
    conv_rhs => rw [h]
    rfl
  simp only [Equiv.funUnique_apply]
  change _ = E (α 0).1 (α 0).2 (at1 G (α 0).1 (α 0).2)
  rw [e]
  simp [ew]

theorem mul_vminus_eq_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsHCParam lam → IsDS ε lam σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0 := by
  intro n ε H _ _ _ σ V E lam u hl hσ hD hu hfd F hF
  have hg := hD.1
  obtain ⟨-, hθ⟩ := (arr_module_facts V n ε E 1).1 hg
  obtain ⟨-, -, hst, -, -, -, hpf⟩ := pfil_facts_hold V n ε E u hg
  have hker : Vminus ε E (LamOf ε lam) u ≤ LinearMap.ker (thetaA E 1) := by
    apply isotypic_part_le_of_forall
    intro y hy μ hμ hyh
    apply compact_span_le_of_stable
    · intro c d _ x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hθ, hx, map_zero]
    · rw [LinearMap.mem_ker]
      obtain ⟨a, b, hba, hne, rfl⟩ := hμ
      by_contra hw0
      have hμeq : LamOf ε lam + Formalism.REAL.root a b = lowK ε lam - Formalism.REAL.root b a := by
        rw [root_swap' a b, sub_eq_add_neg]; rfl
      have hwh : KHighest ε E (lowK ε lam - Formalism.REAL.root b a) (thetaA E 1 y) := by
        refine ⟨fun c => ?_, fun c d hcd hcomp => ?_⟩
        · rw [← hθ, hyh.1 c, map_smul, hμeq]
        · rw [← hθ, hyh.2 c d hcd hcomp, map_zero]
      have hmem : thetaA E 1 y ∈ pfil ε E u 1 := (theta_filtration_holds V n ε E u hg).1 1 y hy
      have := hpf hfd 1
      have hf : FiniteDimensional ℂ (kSpan ε E (thetaA E 1 y)) :=
        Submodule.finiteDimensional_of_le (compact_span_le_of_stable (hst 1) hmem)
      have hK := (GlobalTheory.Jet.KType.kType_iff n ε H σ V E hσ.2.2.1 hD).1 _ _ hw0 hwh hf
      exact absurd (hσ.2.2.2.2.2.2 _ _ hK) (not_le.mpr (vNormSq_sub_root_lt ε hl.1 hba))
  rw [← thetaA_one]
  exact hker hF

end GlobalTheory.Jet.Schmid
end
end

