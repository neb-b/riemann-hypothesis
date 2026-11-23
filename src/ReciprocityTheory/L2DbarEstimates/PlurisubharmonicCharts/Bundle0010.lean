module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0009
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0006

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.BStepA
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

def bsTr (la : La) (U : Set Y) (a : ι → Y → ℂ) : Prop :=
  ∀ i j y, y ∈ U → y ∈ (A.chart i).source → y ∈ (A.chart j).source → a i y = A.g la i j y * a j y

theorem bsA_g_zero {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g 0 i j y = 1 := by
  have h := A.g_add 0 0 i j y hi hj
  rw [add_zero] at h
  have hne := A.g_ne 0 i j y hi hj
  have h2 : A.g 0 i j y * (A.g 0 i j y - 1) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 hne
  · exact sub_eq_zero.mp h3

theorem bsA_g_nsmul (la : La) (k : ℕ) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : A.g (k • la) i j y = A.g la i j y ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact bsA_g_zero A hi hj
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]

theorem bsA_ph_zero {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hi
  rw [add_zero] at h
  linarith

theorem bsA_ph_nsmul (la : La) (k : ℕ) {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) :
    A.ph (k • la) i y = k * A.ph la i y := by
  induction k with
  | zero => rw [zero_nsmul, bsA_ph_zero A hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring

theorem bsA_ph_sub (la mu : La) {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) :
    A.ph (la - mu) i y = A.ph la i y - A.ph mu i y := by
  have h := A.ph_add (la - mu) mu i y hi
  rw [sub_add_cancel] at h
  linarith

theorem bsA_tr_of_isSecOn {la : La} {U : Set Y} {a : ι → Y → ℂ} (h : A.IsSecOn la U a) :
    bsTr A la U a := by
  unfold WeightedAtlas.IsSecOn at h
  exact h.2

theorem bsA_isSecOn_mono {la : La} {U V : Set Y} {a : ι → Y → ℂ} (h : A.IsSecOn la U a)
    (hVU : V ⊆ U) : A.IsSecOn la V a := by
  unfold WeightedAtlas.IsSecOn at h ⊢
  exact And.intro (fun i => (h.1 i).mono (fun v hv => ⟨hv.1, hVU hv.2⟩))
    (fun i j y hy => h.2 i j y (hVU hy))

theorem bsA_tr_mul {la mu : La} {U : Set Y} {a b : ι → Y → ℂ} (ha : bsTr A la U a)
    (hb : bsTr A mu U b) : bsTr A (la + mu) U (fun i y => a i y * b i y) := by
  unfold bsTr at ha hb ⊢
  intro i j y hy hi hj
  show a i y * b i y = A.g (la + mu) i j y * (a j y * b j y)
  rw [ha i j y hy hi hj, hb i j y hy hi hj, A.g_add la mu i j y hi hj]
  ring

theorem bsA_tr_pow {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) (k : ℕ) :
    bsTr A (k • la) U (fun i y => a i y ^ k) := by
  unfold bsTr at ha ⊢
  intro i j y hy hi hj
  show a i y ^ k = A.g (k • la) i j y * a j y ^ k
  rw [ha i j y hy hi hj, bsA_g_nsmul A la k hi hj, mul_pow]

theorem bsA_tr_ratio {la : La} {U : Set Y} {a b : ι → Y → ℂ} (ha : bsTr A la U a)
    (hb : bsTr A la U b) {i j : ι} {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : a i y / b i y = a j y / b j y := by
  unfold bsTr at ha hb
  rw [ha i j y hy hi hj, hb i j y hy hi hj, mul_div_mul_left _ _ (A.g_ne la i j y hi hj)]

theorem bsA_ne_of_tr {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i j : ι}
    {y : Y} (hy : y ∈ U) (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source)
    (h : a j y ≠ 0) : a i y ≠ 0 := by
  unfold bsTr at ha
  rw [ha i j y hy hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h

theorem bsA_nsq_chart {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) {i : ι} {y : Y}
    (hy : y ∈ U) (hi : y ∈ (A.chart i).source) :
    A.nsq la a y = ‖a i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
  have hp := A.mem_pick y
  unfold bsTr at ha
  unfold WeightedAtlas.nsq
  have hg : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (A.g_ne la (A.pick y) i y hp hi)) 2
  rw [ha (A.pick y) i y hy hp hi, A.ph_trans la (A.pick y) i y hp hi, norm_mul, mul_pow, neg_sub,
    sub_eq_add_neg, Real.exp_add, Real.exp_log hg]
  ring

theorem continuousOn_section_chart {la : La} {a : ι → Y → ℂ} (ha : A.IsSec la a) (i : ι) :
    ContinuousOn (a i) (A.chart i).source := by
  unfold WeightedAtlas.IsSec WeightedAtlas.IsSecOn at ha
  have h1 := (ha.1 i).continuousOn
  have h2 : ContinuousOn ((a i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun z hz => ⟨(A.chart i).map_source hz, Set.mem_univ _⟩)
  refine h2.congr ?_
  intro z hz
  simp only [Function.comp_apply, (A.chart i).left_inv hz]

theorem bsA_ph_cont (la : La) (i : ι) : ContinuousOn (A.ph la i) (A.chart i).source := by
  have h1 := (A.smooth_ph la i).continuousOn
  have h2 : ContinuousOn ((A.ph la i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun z hz => (A.chart i).map_source hz)
  refine h2.congr ?_
  intro z hz
  simp only [Function.comp_apply, (A.chart i).left_inv hz]

theorem bsA_nsq_cont {la : La} {a : ι → Y → ℂ} (ha : A.IsSec la a) : Continuous (A.nsq la a) := by
  have htr : bsTr A la Set.univ a := bsA_tr_of_isSecOn A (U := Set.univ) ha
  rw [continuous_iff_continuousAt]
  intro y
  have hs : (A.chart (A.pick y)).source ∈ 𝓝 y :=
    (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousOn (fun z => ‖a (A.pick y) z‖ ^ 2 * Real.exp (-A.ph la (A.pick y) z))
      (A.chart (A.pick y)).source :=
    ((continuousOn_section_chart A ha (A.pick y)).norm.pow 2).mul ((bsA_ph_cont A la (A.pick y)).neg.rexp)
  refine (hc.continuousAt hs).congr ?_
  filter_upwards [hs] with z hz
  exact (bsA_nsq_chart A htr (Set.mem_univ z) hz).symm

theorem bsA_sqn_cont {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} (hw : ∀ k, A.IsSec la (w k)) :
    Continuous (A.sqn la w) := by
  show Continuous (fun y => ∑ k, A.nsq la (w k) y)
  exact continuous_finsetSum _ (fun k _ => bsA_nsq_cont A (hw k))

theorem bsA_nsq_nonneg (la : La) (a : ι → Y → ℂ) (y : Y) : 0 ≤ A.nsq la a y := by
  unfold WeightedAtlas.nsq
  positivity

theorem bsA_nsq_pos {la : La} {a : ι → Y → ℂ} {y : Y} (h : a (A.pick y) y ≠ 0) :
    0 < A.nsq la a y := by
  unfold WeightedAtlas.nsq
  exact mul_pos (pow_pos (norm_pos_iff.mpr h) 2) (Real.exp_pos _)

theorem bsA_sqn_pos {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {y : Y}
    (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by
  obtain ⟨k, hk⟩ := h
  show 0 < ∑ k, A.nsq la (w k) y
  exact Finset.sum_pos' (fun m _ => bsA_nsq_nonneg A la (w m) y) ⟨k, Finset.mem_univ _, bsA_nsq_pos A hk⟩

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.VanishingOrderTransfer
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem vanishing_order_transfer (A : WeightedAtlas n Y ι La) (L : La) (m : ℕ) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (Nsec : ι → Y → ℂ)
    (hw : A.IsSec L w0) (hs : ∀ k, A.IsSec L (s k)) (hN : A.IsSec (m • L) Nsec)
    (y : Y) (hy0 : w0 (A.pick y) y ≠ 0)
    (hdet : (fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det ≠ 0)
    (hvan : A.VanishOrd Nsec y (m + 1))
    {T : Type*} [TopologicalSpace T] (j : T → Y) (hj : Continuous j)
    (e : OpenPartialHomeomorph T (V n)) (he : Set.EqOn (fun t => A.zmap w0 s (j t)) e e.source)
    (t0 : T) (ht0 : t0 ∈ e.source) (hjt0 : j t0 = y) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 (e t0),
      ‖(fun t => Nsec (A.pick (j t)) (j t) / w0 (A.pick (j t)) (j t) ^ m) (e.symm v)‖ ≤
        C * ‖v - e t0‖ ^ (m + 1) := by
  set p := A.pick y with hp
  set c := A.chart p with hc
  set v0 := e t0 with hv0def
  have hy : y ∈ c.source := A.mem_pick y
  have hv0 : v0 ∈ e.target := e.map_source ht0
  have hsymm0 : e.symm v0 = t0 := e.left_inv ht0
  have hte : Tendsto (fun v => j (e.symm v)) (𝓝 v0) (𝓝 y) := by
    have h := (hj.continuousAt (x := e.symm v0)).tendsto.comp (e.continuousAt_symm hv0).tendsto
    rw [hsymm0, hjt0] at h
    exact h
  let φ := fun v => c (j (e.symm v))
  have htφ : Tendsto φ (𝓝 v0) (𝓝 (c y)) := (c.continuousAt hy).tendsto.comp hte
  have hev : ∀ᶠ v in 𝓝 v0, v ∈ e.target ∧ j (e.symm v) ∈ c.source :=
    (e.open_target.eventually_mem hv0).and (hte.eventually (c.open_source.eventually_mem hy))
  have hzφ : ∀ᶠ v in 𝓝 v0, A.zLoc w0 s p (φ v) = v := hev.mono fun v hv => by
    rw [localCoordinates_eq_zmap A L w0 s hw hs p _ hv.2]
    have := he (e.map_target hv.1)
    simp only at this
    rw [this, e.right_inv hv.1]
  have hUeq : ∀ᶠ v in 𝓝 v0,
      Nsec p (c.symm (φ v)) * (w0 p (c.symm (φ v)) ^ m)⁻¹ =
      (fun t => Nsec (A.pick (j t)) (j t) / w0 (A.pick (j t)) (j t) ^ m) (e.symm v) :=
    hev.mono fun v hv => by
      simp only [φ, c.left_inv hv.2]
      rw [ratio_pow_chart_independent A L m Nsec w0 hN hw (A.pick (j (e.symm v))) p _ (A.mem_pick _) hv.2,
        div_eq_mul_inv]
  have hN' : (fun w => Nsec p (c.symm w)) =O[𝓝 (c y)] (fun w => ‖w - c y‖ ^ (m + 1)) := by
    obtain ⟨C, hC⟩ := hvan
    exact IsBigO.of_bound C (hC.mono fun w hw => by rw [norm_pow, norm_norm]; exact hw)
  have hw0c : ContinuousAt (fun w => w0 p (c.symm w)) (c y) := by
    have := hw.1 p
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact (this.differentiableAt (c.open_target.mem_nhds (c.map_source hy))).continuousAt
  have hinv : (fun w => (w0 p (c.symm w) ^ m)⁻¹) =O[𝓝 (c y)] (fun _ => (1 : ℝ)) := by
    have : ContinuousAt (fun w => (w0 p (c.symm w) ^ m)⁻¹) (c y) :=
      (hw0c.pow m).inv₀ (by
        show w0 p (c.symm (c y)) ^ m ≠ 0
        rw [c.left_inv hy]; exact pow_ne_zero _ hy0)
    exact this.tendsto.isBigO_one ℝ
  have hG := (hN'.mul hinv).comp_tendsto htφ
  have hlow : (fun v => φ v - c y) =O[𝓝 v0] (fun v => v - v0) := by
    have hd := differentiableAt_localCoordinates A L w0 s hw hs p y hy hy0
    have h1 := (sub_isBigO_of_det_ne_zero hd.hasFDerivAt hdet).comp_tendsto htφ
    have hq0 : A.zLoc w0 s p (c y) = v0 := by
      rw [localCoordinates_eq_zmap A L w0 s hw hs p y hy, ← hjt0]; exact he ht0
    refine h1.congr' (Eventually.of_forall fun v => rfl) (hzφ.mono fun v hv => ?_)
    simp only [Function.comp_apply, hv]
    exact congrArg (v - ·) hq0
  have hfin : (fun v => Nsec p (c.symm (φ v)) * (w0 p (c.symm (φ v)) ^ m)⁻¹) =O[𝓝 v0]
      (fun v => ‖v - v0‖ ^ (m + 1)) := by
    refine hG.trans ?_
    have := hlow.norm_norm.pow (m + 1)
    exact this.congr_left (fun v => by simp [φ])
  obtain ⟨C, hC⟩ := isBigO_iff.1 (hfin.congr' hUeq EventuallyEq.rfl)
  refine ⟨C, hC.mono fun v hv => ?_⟩
  rwa [norm_pow, norm_norm] at hv

end atlas

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem norm_section_ratio_le {N' : ℕ} (A : WeightedAtlas n Y ι La) (L : La) (m : ℕ)
    (w : Fin N' → ι → Y → ℂ) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (Nsec : ι → Y → ℂ)
    (C1 C2 : ℝ) (h1 : ∀ y, A.nsq (m • L) Nsec y ≤ C1 * A.sqn L w y ^ m)
    (h2 : ∀ y, A.sqn L w y ≤ C2 * (A.nsq L w0 y + A.sqn L s y)) (y : Y)
    (hy0 : w0 (A.pick y) y ≠ 0) :
    ‖Nsec (A.pick y) y / w0 (A.pick y) y ^ m‖ ≤
      Real.sqrt (max C1 0 * |C2| ^ m) * (1 + ‖A.zmap w0 s y‖ ^ 2) ^ ((m : ℝ) / 2) := by
  set p := A.pick y with hp
  set E := Real.exp (-A.ph L p y) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hw0n : 0 < ‖w0 p y‖ := norm_pos_iff.2 hy0
  set a := ‖w0 p y‖ ^ 2 * E with ha
  have ha0 : 0 < a := by positivity
  set t := 1 + ‖A.zmap w0 s y‖ ^ 2 with ht
  have ht0 : 0 < t := by positivity
  set U := Nsec p y / w0 p y ^ m with hU
  have hsq : A.sqn L s y = a * ‖A.zmap w0 s y‖ ^ 2 := by
    simp only [sqn, nsq, zmap, EuclideanSpace.norm_sq_eq, ← hp, ← hE, ha,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [norm_div]
    field_simp
  have hw0sq : A.nsq L w0 y = a := rfl
  have hNsq : A.nsq (m • L) Nsec y = ‖U‖ ^ 2 * a ^ m := by
    simp only [nsq, ← hp]
    rw [weight_nsmul_eq_mul A L m p y (A.mem_pick y), show -(↑m * A.ph L p y) = ↑m * (-A.ph L p y)
      by ring, Real.exp_nat_mul, ← hE, hU, ha, norm_div, norm_pow]
    field_simp
    ring_nf
  have hsqw : 0 ≤ A.sqn L w y :=
    Finset.sum_nonneg (fun k _ => by unfold nsq; positivity)
  have hle : ‖U‖ ^ 2 * a ^ m ≤ (max C1 0 * |C2| ^ m * t ^ m) * a ^ m := by
    rw [← hNsq]
    have hb : A.sqn L w y ≤ |C2| * (a * t) := by
      have := h2 y
      rw [hw0sq, hsq] at this
      calc A.sqn L w y ≤ C2 * (a + a * ‖A.zmap w0 s y‖ ^ 2) := this
        _ = C2 * (a * t) := by rw [ht]; ring
        _ ≤ |C2| * (a * t) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    calc A.nsq (m • L) Nsec y ≤ C1 * A.sqn L w y ^ m := h1 y
      _ ≤ max C1 0 * A.sqn L w y ^ m :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hsqw m)
      _ ≤ max C1 0 * (|C2| * (a * t)) ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsqw hb m) (le_max_right _ _)
      _ = (max C1 0 * |C2| ^ m * t ^ m) * a ^ m := by ring
  have hle' : ‖U‖ ^ 2 ≤ max C1 0 * |C2| ^ m * t ^ m :=
    le_of_mul_le_mul_right hle (pow_pos ha0 m)
  have hK : 0 ≤ max C1 0 * |C2| ^ m := by positivity
  calc ‖U‖ = Real.sqrt (‖U‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (max C1 0 * |C2| ^ m * t ^ m) := Real.sqrt_le_sqrt hle'
    _ = Real.sqrt (max C1 0 * |C2| ^ m) * Real.sqrt (t ^ m) :=
        Real.sqrt_mul hK _
    _ = Real.sqrt (max C1 0 * |C2| ^ m) * t ^ ((m : ℝ) / 2) := by
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        congr 1; ring

end atlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

