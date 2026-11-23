module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.ShellCeilEq
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

lemma shell_mem (a t : ℝ) (ht : a + 1 < t) :
    a + 1 + (⌈t - a - 2⌉₊ : ℝ) < t ∧ t ≤ a + 2 + (⌈t - a - 2⌉₊ : ℝ) := by
  constructor
  · rcases le_or_gt 0 (t - a - 2) with h | h
    · have := Nat.ceil_lt_add_one h
      linarith
    · rw [Nat.ceil_eq_zero.mpr h.le]
      simp only [CharP.cast_eq_zero, add_zero]
      linarith
  · have := Nat.le_ceil (t - a - 2)
    linarith

lemma shell_coef (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-(Real.log (1 + C) + k))) * ENNReal.ofReal C ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by linarith)]
  have h1 : 0 < 1 + C := by linarith
  have h2 := Real.exp_pos (-(k : ℝ))
  have h3 : (1 + C)⁻¹ * C ≤ 1 := by
    rw [inv_mul_le_iff₀ h1]
    linarith
  have h4 : 0 ≤ (1 + C)⁻¹ := inv_nonneg.mpr h1.le
  nlinarith [mul_le_mul_of_nonneg_left h3 h2.le]

private lemma vol_lt_infty_of_compact {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) {K : Set M} (hK : IsCompact K) :
    vol n z K < ⊤ := by
  classical
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold vol
  split_ifs with h
  · rw [Measure.ofMeasurable_apply K hKm]
    unfold volFun
    have hz' : ∀ x, ∃ e : OpenPartialHomeomorph M (V n), x ∈ e.source ∧ z = e :=
      fun x => (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hz) x (Set.mem_univ x)
    choose e he hze using hz'
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => (e x).source) (fun x => (e x).open_source)
      (fun x _ => Set.mem_iUnion.mpr ⟨x, he x⟩)
    have hbound : ∀ y : V n, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤
        (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y := by
      intro y
      by_cases hy : y ∈ z '' K
      · rw [Set.indicator_of_mem hy]
        have hidx : ∀ p ∈ K ∩ z ⁻¹' {y}, ∃ i ∈ t, p ∈ (e i).source := by
          intro p hp
          have := ht hp.1
          simp only [Set.mem_iUnion] at this
          obtain ⟨i, hi, hpi⟩ := this
          exact ⟨i, hi, hpi⟩
        choose! f hf1 hf2 using hidx
        have h1 : (K ∩ z ⁻¹' {y}).encard ≤ ((t : Set M)).encard := by
          refine Set.encard_le_encard_of_injOn (fun p hp => hf1 p hp) ?_
          intro p hp q hq hpq
          have hp' := hf2 p hp
          have hq' := hf2 q hq
          rw [hpq] at hp'
          apply (e (f q)).injOn hp' hq'
          have h3 := congrFun (hze (f q))
          rw [← h3 p, ← h3 q, Set.mem_singleton_iff.mp hp.2, Set.mem_singleton_iff.mp hq.2]
        rw [Set.encard_coe_eq_coe_finsetCard] at h1
        calc ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ ((t.card : ℕ∞) : ℝ≥0∞) := ENat.toENNReal_le.mpr h1
          _ = t.card := by simp
      · rw [Set.indicator_of_notMem hy]
        have : K ∩ z ⁻¹' {y} = ∅ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro hp hzp
          exact hy ⟨p, hp, hzp⟩
        rw [this, Set.encard_empty]
        simp
    calc ∫⁻ y, ((K ∩ z ⁻¹' {y}).encard : ℝ≥0∞) ≤ ∫⁻ y, (z '' K).indicator (fun _ => (t.card : ℝ≥0∞)) y :=
          lintegral_mono hbound
      _ = t.card * volume (z '' K) :=
          lintegral_indicator_const (hK.image hz.continuous).isClosed.measurableSet _
      _ < ⊤ := ENNReal.mul_lt_top (by simp) (hK.image hz.continuous).measure_lt_top
  · simp

theorem shell (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ShellStatement n M := by
  classical
  intro z hz e ph ψ v a he hK hph hψ hv
  set g : M → ℝ := fun x => ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) with hg
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hgm : Measurable fun x => ENNReal.ofReal (g x) := ENNReal.measurable_ofReal.comp hgc.measurable
  have hfin : ∀ b : ℝ, ∫⁻ x in {x | e x ≤ b}, ENNReal.ofReal (g x) ∂vol n z < ⊤ := by
    intro b
    exact setLIntegral_lt_top_of_isCompact (vol_lt_infty_of_compact z hz (hK b)).ne (hK b)
      (f := fun x => (g x).toNNReal) (continuous_real_toNNReal.comp hgc)
  set C : ℕ → ℝ := fun k => (∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z).toReal with hC
  have hC0 : ∀ k : ℕ, 0 ≤ C k := fun k => ENNReal.toReal_nonneg
  have hCeq : ∀ k : ℕ, ∫⁻ x in {x | e x ≤ a + 2 + k}, ENNReal.ofReal (g x) ∂vol n z = ENNReal.ofReal (C k) :=
    fun k => (ENNReal.ofReal_toReal (hfin _).ne).symm
  set R : ℝ → ℝ := fun t => if a + 1 < t then Real.log (1 + C ⌈t - a - 2⌉₊) + ⌈t - a - 2⌉₊ else 0 with hR
  have hterm0 : ∀ k : ℕ, 0 ≤ Real.log (1 + C k) + k :=
    fun k => add_nonneg (Real.log_nonneg (by linarith [hC0 k])) (Nat.cast_nonneg k)
  refine ⟨R, ?_, ?_⟩
  · intro b
    refine ⟨∑ k ∈ Finset.range (⌈b - a - 2⌉₊ + 1), (Real.log (1 + C k) + k), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_Iic] at ht
    simp only [hR]
    split_ifs with h
    · exact Finset.single_le_sum (f := fun k : ℕ => Real.log (1 + C k) + k) (fun k _ => hterm0 k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.ceil_mono (by linarith))))
    · exact Finset.sum_nonneg fun k _ => hterm0 k
  · intro χ hχ0 hχR
    unfold nV
    set S : ℕ → Set M := fun k => {x | a + 1 + k < e x ∧ e x ≤ a + 2 + k} with hS
    have hSm : ∀ k, MeasurableSet (S k) := fun k =>
      (measurableSet_lt measurable_const he.measurable).inter (measurableSet_le he.measurable measurable_const)
    have hLm : MeasurableSet {x | e x ≤ a + 1} := measurableSet_le he.measurable measurable_const
    have hpt : ∀ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ≤
        {x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x +
        ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
          ENNReal.ofReal (g x)) x := by
      intro x
      by_cases hx : e x ≤ a + 1
      · rw [Set.indicator_of_mem (show x ∈ {x | e x ≤ a + 1} from hx)]
        refine le_trans ?_ le_self_add
        apply ENNReal.ofReal_le_ofReal
        simp only [hg]
        gcongr
        linarith [hχ0 (e x)]
      · push_neg at hx
        have hxS : x ∈ S ⌈e x - a - 2⌉₊ := shell_mem a (e x) hx
        refine le_trans ?_ (le_add_left (ENNReal.le_tsum ⌈e x - a - 2⌉₊))
        rw [Set.indicator_of_mem hxS, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        apply ENNReal.ofReal_le_ofReal
        have hRx : Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊ ≤ χ (e x) := by
          have := hχR (e x) hx.le
          simp only [hR, if_pos hx] at this
          exact this
        simp only [hg]
        rw [show -(ph x + χ (e x) - ψ x) = -(χ (e x)) + (-ph x + ψ x) by ring, Real.exp_add]
        have h1 : Real.exp (-(χ (e x))) ≤ Real.exp (-(Real.log (1 + C ⌈e x - a - 2⌉₊) + ⌈e x - a - 2⌉₊)) :=
          Real.exp_le_exp.mpr (by linarith)
        have h2 : 0 ≤ ‖v x‖ ^ 2 * Real.exp (-ph x + ψ x) := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    calc ∫⁻ x, ENNReal.ofReal (‖v x‖ ^ 2 * Real.exp (-(ph x + χ (e x) - ψ x))) ∂vol n z
        ≤ ∫⁻ x, ({x | e x ≤ a + 1}.indicator (fun x => ENNReal.ofReal (g x)) x +
          ∑' k, (S k).indicator (fun x => ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
            ENNReal.ofReal (g x)) x) ∂vol n z := lintegral_mono hpt
      _ = ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z +
          ∑' k, ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) *
            ∫⁻ x in S k, ENNReal.ofReal (g x) ∂vol n z := by
        rw [lintegral_add_left (hgm.indicator hLm), lintegral_indicator hLm,
          lintegral_tsum (fun k => ((hgm.const_mul _).indicator (hSm k)).aemeasurable)]
        congr 1
        refine tsum_congr fun k => ?_
        rw [lintegral_indicator (hSm k), lintegral_const_mul _ hgm]
      _ ≤ ∫⁻ x in {x | e x ≤ a + 1}, ENNReal.ofReal (g x) ∂vol n z +
          ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(k : ℝ))) := by
        refine add_le_add le_rfl (ENNReal.tsum_le_tsum fun k => ?_)
        calc ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ∫⁻ x in S k, ENNReal.ofReal (g x) ∂vol n z
            ≤ ENNReal.ofReal (Real.exp (-(Real.log (1 + C k) + k))) * ENNReal.ofReal (C k) := by
              gcongr
              rw [← hCeq k]
              exact lintegral_mono_set (fun x hx => hx.2)
          _ ≤ _ := shell_coef (C k) (hC0 k) k
      _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨hfin (a + 1), ?_⟩
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (Real.exp_pos _).le) Real.summable_exp_neg_nat]
        exact ENNReal.ofReal_lt_top

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.TestIneq
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem ti_le_of_forall_pos (x c Y : ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → x ≤ c * (ENNReal.ofReal (1 + ε) * Y)) : x ≤ c * Y := by
  have hc : Continuous fun ε : ℝ => ENNReal.ofReal (1 + ε) :=
    ENNReal.continuous_ofReal.comp (continuous_const.add continuous_id)
  have ht0 : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h1
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal (1 + ε) * (c * Y)) (𝓝[>] 0) (𝓝 (c * Y)) := by
    have h1 := ENNReal.Tendsto.mul_const (b := c * Y) ht0 (Or.inl one_ne_zero)
    simpa using h1
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => by
    calc x ≤ c * (ENNReal.ofReal (1 + ε) * Y) := h ε hε
      _ = ENNReal.ofReal (1 + ε) * (c * Y) := by ring)

theorem ti_hasCompactSupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → V n) (hf : IsTestForm n z f) : HasCompactSupport f := by
  have h : ∀ j, HasCompactSupport (fun x => f x j) := fun j => (hf j).2
  have hsub : Function.support f ⊆ ⋃ j, Function.support (fun x => f x j) := by
    intro x hx
    rw [Set.mem_iUnion]
    by_contra hne
    push_neg at hne
    apply hx
    ext j
    simpa [Function.mem_support] using hne j
  have hts : tsupport f ⊆ ⋃ j, tsupport (fun x => f x j) := by
    show closure (Function.support f) ⊆ ⋃ j, closure (Function.support fun x => f x j)
    rw [← closure_iUnion_of_finite]
    exact closure_mono hsub
  exact IsCompact.of_isClosed_subset (isCompact_iUnion fun j => h j) (isClosed_tsupport f) hts

private theorem db_eq_wdb_comp_symm_of_isChart {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    (j : Fin n) (f : M → ℂ) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) {x : M}
    (hx : x ∈ e.source) : db n z j f x = wdb n j (f ∘ e.symm) (z x) := by
  have hex : ∃ c : OpenPartialHomeomorph M (V n), IsChart n z c ∧ x ∈ c.source := ⟨e, he, hx⟩
  rw [db, dite_eq_left hex]
  obtain ⟨hc, hxc⟩ := Classical.choose_spec hex
  apply wdb_congr
  have hzx : z x = e x := he hx
  have hzc : z x = (Classical.choose hex) x := hc hxc
  have h1 : ∀ᶠ y in 𝓝 (z x), y ∈ e.target := by
    rw [hzx]
    exact e.open_target.mem_nhds (e.map_source hx)
  have h2 : ∀ᶠ y in 𝓝 (z x), y ∈ (Classical.choose hex).target := by
    rw [hzc]
    exact (Classical.choose hex).open_target.mem_nhds ((Classical.choose hex).map_source hxc)
  have h3 : ∀ᶠ y in 𝓝 (z x), e.symm y ∈ (Classical.choose hex).source := by
    have hca : ContinuousAt e.symm (z x) := by
      rw [hzx]
      exact e.continuousAt_symm (e.map_source hx)
    apply hca.preimage_mem_nhds
    rw [hzx, e.left_inv hx]
    exact (Classical.choose hex).open_source.mem_nhds hxc
  filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
  show f ((Classical.choose hex).symm y) = f (e.symm y)
  congr 1
  apply (Classical.choose hex).injOn ((Classical.choose hex).map_target hy2) hy3
  rw [(Classical.choose hex).right_inv hy2, ← hc hy3, he (e.map_target hy1), e.right_inv hy1]

private theorem ck_one_db_of_smooth {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n} {F : M → ℂ}
    (hF : Smooth n z F) (j : Fin n) : Ck n z 1 (fun x => db n z j F x) := by
  intro e he
  have hG : ContDiffOn ℝ 2 (F ∘ e.symm) e.target := (hF e he).of_le (by first
      | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr le_top
      | simp)
  have hD : ContDiffOn ℝ 1 (fun y => fderiv ℝ (F ∘ e.symm) y) e.target :=
    hG.fderiv_of_isOpen e.open_target (by norm_num)
  have hW : ContDiffOn ℝ 1 (fun y => wdb n j (F ∘ e.symm) y) e.target := by
    unfold wdb
    exact ((hD.clm_apply contDiffOn_const).add
      (contDiffOn_const.mul (hD.clm_apply contDiffOn_const))).div_const _
  refine hW.congr fun y hy => ?_
  show db n z j F (e.symm y) = wdb n j (F ∘ e.symm) y
  rw [db_eq_wdb_comp_symm_of_isChart j F e he (e.map_target hy), he (e.map_target hy), e.right_inv hy]

private theorem smoothR_sub_const_mul {M : Type*} [TopologicalSpace M] {n : ℕ} {z : M → V n}
    {a b : M → ℝ} (ha : SmoothR n z a) (hb : SmoothR n z b) (c : ℝ) :
    SmoothR n z (fun x => a x - c * b x) := by
  intro e he
  refine ((ha e he).sub ((contDiffOn_const (c := ((c : ℝ) : ℂ))).mul (hb e he))).congr
    fun y _ => ?_
  simp [Function.comp]

theorem testIneq (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hCh : ChoiceStatement n M) (hP : PrimedIneqStatement n M)
    (hC : ClosureIneqStatement n M) (hS : SplitTestStatement n M) (hL : LocalityStatement n M)
    (hWS : WeakSSmoothStatement n M) (hSD : SbarDbarStatement n M) : TestIneqStatement n M := by
  intro X ph F0 h hph hlev hF0 hh hdom hI f hf
  have hz := X.isLocalHomeomorph
  apply ti_le_of_forall_pos
  intro ε hε
  have hck2 : Ck n X.z 2 F0 := fun e he => (hF0 e he).of_le (by first
      | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤)
      | exact WithTop.coe_le_coe.mpr le_top
      | simp)
  have hcj : ∀ j, Continuous fun x => db n X.z j F0 x := by
    intro j
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨e, hxe, hze⟩ := hz x
    have he : IsChart n X.z e := fun y _ => by rw [hze]
    have hC := (ck_one_db_of_smooth hF0 j e he).continuousOn
    have h1 : ContinuousOn (((fun x => db n X.z j F0 x) ∘ e.symm) ∘ e) e.source :=
      hC.comp e.continuousOn (fun y hy => e.map_source hy)
    have h2 : ContinuousOn (fun x => db n X.z j F0 x) e.source :=
      h1.congr fun y hy => by simp [e.left_inv hy]
    exact h2.continuousAt (e.open_source.mem_nhds hxe)
  have hcont : Continuous (dbarF n X.z F0) := by
    show Continuous fun x => WithLp.toLp 2 (fun j => db n X.z j F0 x)
    first
      | exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp (continuous_pi hcj)
      | exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin n => ℂ)).comp (continuous_pi hcj)
      | fun_prop
  obtain ⟨ph', ψ, e', U, hph', hψ, he', hcut, hU, hCU, hUeq, hle, hlevi, hL2⟩ :=
    hCh X ph (dbarF n X.z F0) (tsupport f) ε hph hcont (ti_hasCompactSupport n X.z f hf) hε
  have hprim := hP X.z hz ph ph' ψ F0 h ε hph hlev hph' hψ hF0 hh hdom hε hle hlevi hI
  have hclos := hC X.z hz e' ph' ψ (dbarF n X.z F0) _ ε he' hph' hψ hcut hL2 hI hε hprim
  have hw1 : SmoothR n X.z (w1 ph' ψ) := smoothR_sub_const_mul hph' hψ 2
  have hw2 : SmoothR n X.z (w2 ph' ψ) := by
    have h1 := smoothR_sub_const_mul hph' hψ 1
    simp only [one_mul] at h1
    exact h1
  have hWS0 : IsWeakS n X.z (dbarF n X.z F0) 0 := by
    have h1 := hWS X.z hz (dbarF n X.z F0) (fun j => ck_one_db_of_smooth hF0 j)
    have h0 : sbar n X.z (dbarF n X.z F0) = 0 := by
      funext x
      exact hSD X.z hz F0 hck2 x
    rwa [h0] at h1
  obtain ⟨hT, f₁, hf₁, hS1, hadj, hip⟩ :=
    hS X.z hz (w1 ph' ψ) (w2 ph' ψ) (dbarF n X.z F0) f hw1 hw2 hL2 hWS0 hf
  obtain ⟨hloc1, hloc2⟩ := hL X.z hz ph ph' ψ U f hU hf hCU hUeq
  have hfin := hclos f₁ (tstar n X.z (w1 ph' ψ) (w2 ph' ψ) f) hf₁ hT hadj hS1
  rw [← hip, hloc1, hloc2] at hfin
  exact hfin

end

end ReciprocityTheory.L2DbarEstimates.F
end

