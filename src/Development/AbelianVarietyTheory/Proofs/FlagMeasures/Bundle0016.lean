module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdFixedPlaceAverage
section
open Finset

namespace GlobalTheory

theorem sum_prod_fixed_place_average {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {V : Type}
    [AddCommGroup V] [Module ℂ V] (a : ∀ i, G i → ℂ) (f : (∀ i, G i) → V)
    (hf : ∀ i (γ : ∀ i, G i), γ i = 1 → ∑ β : G i, a i β • f (Function.update γ i β) = f γ) :
    ∑ γ : (∀ i, G i), (∏ i, a i (γ i)) • f γ = f 1 := by
  classical
  let c : Finset ι → (∀ i, G i) → ℂ := fun S γ =>
    ∏ i, (if i ∈ S then a i (γ i) else if γ i = 1 then 1 else 0)
  have key : ∀ S : Finset ι, ∑ γ, c S γ • f γ = f 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.sum_eq_single (1 : ∀ i, G i)]
      · simp [c]
      · intro γ _ hγ
        obtain ⟨i, hi⟩ : ∃ i, γ i ≠ 1 := by
          by_contra hcon
          push_neg at hcon
          exact hγ (funext hcon)
        have : c ∅ γ = 0 := Finset.prod_eq_zero (mem_univ i) (by simp [hi])
        rw [this, zero_smul]
      · intro h; exact absurd (mem_univ _) h
    | insert j S hj ih =>
      rw [← ih]
      let h : ∀ i, G i → ℂ := fun i x => if i ∈ S then a i x else if x = 1 then 1 else 0
      have cU : ∀ (γ : ∀ i, G i) (β : G j),
          c S (Function.update γ j β) = h j β * ∏ i ∈ univ.erase j, h i (γ i) := by
        intro γ β
        show ∏ i, h i (Function.update γ j β i) = _
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro i hi
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      have cI : ∀ γ : ∀ i, G i, c (insert j S) γ = a j (γ j) * ∏ i ∈ univ.erase j, h i (γ i) := by
        intro γ
        show ∏ i, _ = _
        rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro i hi
          have : i ≠ j := Finset.ne_of_mem_erase hi
          simp [h, this]
      have step1 : ∑ γ, c S γ • f γ
          = ∑ γ, ∑ β : G j, (c S γ * a j β) • f (Function.update γ j β) := by
        apply Finset.sum_congr rfl
        intro γ _
        by_cases hγ : γ j = 1
        · rw [← hf j γ hγ, Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro β _
          rw [mul_smul]
        · have : c S γ = 0 := Finset.prod_eq_zero (mem_univ j) (by simp [hj, hγ])
          simp [this]
      let e : (∀ i, G i) × G j ≃ (∀ i, G i) × G j :=
        { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
          invFun := fun p => (Function.update p.1 j p.2, p.1 j)
          left_inv := by intro p; simp
          right_inv := by intro p; simp }
      rw [step1, ← Fintype.sum_prod_type']
      rw [← Fintype.sum_equiv e
        (fun p => (c S (Function.update p.1 j p.2) * a j (p.1 j)) • f p.1) _ (by
          intro p
          simp [e])]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro γ _
      dsimp only
      rw [← Finset.sum_smul, ← Finset.sum_mul]
      simp_rw [cU]
      rw [← Finset.sum_mul, cI]
      have : ∑ β : G j, h j β = 1 := by simp [h, hj]
      rw [this, one_mul, mul_comm]
  have := key univ
  simpa [c] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableAndTsumLeOfBoxCount
section
open Finset

namespace GlobalTheory

theorem summable_and_tsum_le_of_box_count (ι Γ : Type) [Fintype ι] (D : Γ → ι → ℝ) (t : Γ → ℝ)
    (a A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (ha : Real.exp (-a) ≤ 1 / 2) (_hD : ∀ γ v, 0 ≤ D γ v)
    (ht : ∀ γ, 0 ≤ t γ ∧ t γ ≤ c * ∏ v, Real.exp (-(2 * a * (⌊D γ v⌋₊ : ℝ))))
    (hN : ∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.Finite ∧
      (({γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (a * ∑ v, r v)) :
    Summable t ∧ ∑' γ, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
  classical
  set q := Real.exp (-a) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by linarith
  have hgeom : ∀ M : ℕ, ∑ k ∈ Finset.range M, q ^ k ≤ 2 := by
    intro M
    calc ∑ k ∈ Finset.range M, q ^ k ≤ ∑' k, q ^ k :=
          (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum _ (fun k _ => pow_nonneg hq0 k)
      _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1
      _ ≤ 2 := by
          rw [inv_le_comm₀ (by linarith) (by norm_num)]
          linarith
  have hprod : ∀ F : Finset (ι → ℕ), ∑ n ∈ F, ∏ v, q ^ (n v) ≤ 2 ^ Fintype.card ι := by
    intro F
    set M := F.sup (fun n => ∑ v, n v) + 1 with hM
    have hsub : F ⊆ Fintype.piFinset (fun _ : ι => Finset.range M) := by
      intro n hn
      rw [Fintype.mem_piFinset]
      intro v
      rw [Finset.mem_range]
      have h1 : n v ≤ ∑ w, n w :=
        Finset.single_le_sum (fun w _ => Nat.zero_le (n w)) (Finset.mem_univ v)
      have h2 : ∑ w, n w ≤ F.sup (fun n => ∑ v, n v) := Finset.le_sup (f := fun n => ∑ v, n v) hn
      omega
    calc ∑ n ∈ F, ∏ v, q ^ (n v)
        ≤ ∑ n ∈ Fintype.piFinset (fun _ : ι => Finset.range M), ∏ v, q ^ (n v) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun n _ _ => Finset.prod_nonneg (fun v _ => pow_nonneg hq0 _))
      _ = ∏ _v : ι, ∑ k ∈ Finset.range M, q ^ k :=
          (Finset.prod_univ_sum (fun _ => Finset.range M) (fun _ k => q ^ k)).symm
      _ ≤ ∏ _v : ι, (2 : ℝ) :=
          Finset.prod_le_prod₀ (fun v _ => Finset.sum_nonneg (fun k _ => pow_nonneg hq0 k))
            (fun v _ => hgeom M)
      _ = 2 ^ Fintype.card ι := by simp
  have hB : 0 ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by positivity
  have hfin : ∀ s : Finset Γ, ∑ γ ∈ s, t γ ≤ c * A * (2 * Real.exp a) ^ Fintype.card ι := by
    intro s
    set φ : Γ → ι → ℕ := fun γ v => ⌊D γ v⌋₊ with hφ
    set s' := s.filter (fun γ => t γ ≠ 0) with hs'
    rw [← Finset.sum_filter_ne_zero]
    rw [← Finset.sum_fiberwise_of_maps_to (t := s'.image φ) (g := φ)
      (fun γ hγ => Finset.mem_image_of_mem φ hγ)]
    have hfib : ∀ n : ι → ℕ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ ≤
        c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
      intro n
      set Fn := s'.filter (fun γ => φ γ = n) with hFn
      set e : ℝ := c * ∏ v, Real.exp (-(2 * a * (n v : ℝ))) with he_def
      have he : 0 ≤ e := by positivity
      have h1 : ∑ γ ∈ Fn, t γ ≤ Fn.card * e := by
        calc ∑ γ ∈ Fn, t γ ≤ ∑ _γ ∈ Fn, e := by
              apply Finset.sum_le_sum
              intro γ hγ
              have hn : φ γ = n := (Finset.mem_filter.1 hγ).2
              have hfl : ∀ v, ⌊D γ v⌋₊ = n v := fun v => congrFun hn v
              have h := (ht γ).2
              simp only [hfl] at h
              exact h
          _ = Fn.card * e := by rw [Finset.sum_const, nsmul_eq_mul]
      set r : ι → ℝ := fun v => (n v : ℝ) + 1 with hr_def
      have hr : ∀ v, 0 ≤ r v := fun v => by positivity
      obtain ⟨hSf, hSc⟩ := hN r hr
      have hsub : (↑Fn : Set Γ) ⊆ {γ | t γ ≠ 0 ∧ ∀ v, D γ v ≤ r v} := by
        intro γ hγ
        have hm := Finset.mem_filter.1 (Finset.mem_coe.1 hγ)
        have hm' := Finset.mem_filter.1 hm.1
        refine ⟨hm'.2, fun v => ?_⟩
        have hfl : ⌊D γ v⌋₊ = n v := congrFun hm.2 v
        have hl := Nat.lt_floor_add_one (D γ v)
        rw [hfl] at hl
        exact hl.le
      have hcard : (Fn.card : ℝ) ≤ A * Real.exp (a * ∑ v, r v) := by
        have hc' := Set.ncard_le_ncard hsub hSf
        rw [Set.ncard_coe_finset] at hc'
        exact le_trans (by exact_mod_cast hc') hSc
      have hS2 : ∑ v, 2 * a * (n v : ℝ) = 2 * a * ∑ v, (n v : ℝ) := by rw [Finset.mul_sum]
      have hS3 : ∑ v, (n v : ℝ) * -a = (∑ v, (n v : ℝ)) * -a := by rw [Finset.sum_mul]
      have hS1 : ∑ v, r v = ∑ v, (n v : ℝ) + Fintype.card ι := by
        simp only [hr_def, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]
      calc ∑ γ ∈ Fn, t γ ≤ Fn.card * e := h1
        _ ≤ A * Real.exp (a * ∑ v, r v) * e := mul_le_mul_of_nonneg_right hcard he
        _ = c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) := by
            rw [he_def, hq]
            simp_rw [← Real.exp_nat_mul]
            rw [← Real.exp_sum, ← Real.exp_sum, Finset.sum_neg_distrib, hS2, hS3, hS1]
            rw [show A * Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
                  (c * Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) =
                c * A * (Real.exp (a * (∑ v, (n v : ℝ) + Fintype.card ι)) *
                  Real.exp (-(2 * a * ∑ v, (n v : ℝ)))) by ring,
              show c * A * Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a) =
                c * A * (Real.exp (a * Fintype.card ι) * Real.exp ((∑ v, (n v : ℝ)) * -a)) by ring,
              ← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
    calc ∑ n ∈ s'.image φ, ∑ γ ∈ s'.filter (fun γ => φ γ = n), t γ
        ≤ ∑ n ∈ s'.image φ, c * A * Real.exp (a * Fintype.card ι) * ∏ v, q ^ (n v) :=
          Finset.sum_le_sum (fun n _ => hfib n)
      _ = c * A * Real.exp (a * Fintype.card ι) * ∑ n ∈ s'.image φ, ∏ v, q ^ (n v) := by
          rw [Finset.mul_sum]
      _ ≤ c * A * Real.exp (a * Fintype.card ι) * 2 ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_left (hprod _) (by positivity)
      _ = c * A * (2 * Real.exp a) ^ Fintype.card ι := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_comm (Fintype.card ι : ℝ) a]
          ring
  exact ⟨summable_of_sum_le (fun γ => (ht γ).1) hfin, tsum_le_of_sum_le' hB hfin⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoOfSqueeze
section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.GaugeProd

def Asym {X : Type*} [MeasurableSpace X] (ν : Measure X) (f : X → ℝ) (d : ℕ) : Prop :=
  Tendsto (fun r : ℝ => ν {x | Real.sqrt (f x) ≤ r} / ENNReal.ofReal (r ^ d)) (𝓝[>] 0)
    (𝓝 (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)))

variable {X Y Z W : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]

theorem prod_le_right (ν : Measure X) (μ : Measure Y) (lam : Measure Z) [SFinite μ] [SFinite lam]
    {f : X → ℝ} {g : Y → ℝ} {h : Z → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (h0 : ∀ x, 0 ≤ f x) (b : ℝ≥0) {δ : ℝ} (H : ∀ s ≤ δ, μ {y | g y ≤ s} ≤ b * lam {z | h z ≤ s})
    {t : ℝ} (ht : t ≤ δ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} ≤ b * ν.prod lam {z | f z.1 + h z.2 ≤ t} := by
  have m1 : MeasurableSet {z : X × Y | f z.1 + g z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  have m2 : MeasurableSet {z : X × Z | f z.1 + h z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hh.comp measurable_snd)) measurable_const
  rw [Measure.prod_apply m1, Measure.prod_apply m2, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_mono fun x => ?_
  have e1 : Prod.mk x ⁻¹' {z : X × Y | f z.1 + g z.2 ≤ t} = {y | g y ≤ t - f x} := by
    ext y; simp only [mem_preimage, mem_setOf_eq]; constructor <;> intro <;> linarith
  have e2 : Prod.mk x ⁻¹' {z : X × Z | f z.1 + h z.2 ≤ t} = {y | h y ≤ t - f x} := by
    ext y; simp only [mem_preimage, mem_setOf_eq]; constructor <;> intro <;> linarith
  simp only [e1, e2]
  exact H _ (by linarith [h0 x])

theorem prod_swap_set (ν : Measure X) (μ : Measure Y) [SFinite ν] [SFinite μ]
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) (t : ℝ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} = μ.prod ν {z | g z.1 + f z.2 ≤ t} := by
  have m1 : MeasurableSet {z : X × Y | f z.1 + g z.2 ≤ t} :=
    measurableSet_le ((hf.comp measurable_fst).add (hg.comp measurable_snd)) measurable_const
  rw [← Measure.prod_swap, Measure.map_apply measurable_swap m1]
  congr 1
  ext z
  simp [add_comm]

theorem prod_le_both (ν : Measure X) (μ : Measure Y) (ν' : Measure W) (μ' : Measure Z)
    [SFinite ν] [SFinite μ] [SFinite ν'] [SFinite μ']
    {f : X → ℝ} {g : Y → ℝ} {f' : W → ℝ} {g' : Z → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf' : Measurable f') (hg' : Measurable g')
    (h0 : ∀ x, 0 ≤ f x) (h0' : ∀ x, 0 ≤ g' x) (a b : ℝ≥0) {δ : ℝ}
    (H1 : ∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * ν' {z | f' z ≤ s})
    (H2 : ∀ s ≤ δ, μ {y | g y ≤ s} ≤ b * μ' {z | g' z ≤ s})
    {t : ℝ} (ht : t ≤ δ) :
    ν.prod μ {z | f z.1 + g z.2 ≤ t} ≤ b * a * ν'.prod μ' {z | f' z.1 + g' z.2 ≤ t} := by
  refine (prod_le_right ν μ μ' hf hg hg' h0 b H2 ht).trans ?_
  rw [mul_assoc, prod_swap_set ν μ' hf hg', prod_swap_set ν' μ' hf' hg']
  gcongr
  exact prod_le_right μ' ν ν' hg' hf hf' h0' a H1 ht

theorem le_of_pos (ν : Measure X) (lam : Measure Z) {f : X → ℝ} {g : Z → ℝ} (hg : Measurable g)
    (h0 : ∀ x, 0 ≤ f x) (a : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (hfin : lam {z | g z ≤ δ} ≠ ⊤)
    (H : ∀ s, 0 < s → s ≤ δ → ν {y | f y ≤ s} ≤ a * lam {z | g z ≤ s}) :
    ∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * lam {z | g z ≤ s} := by
  intro s hs
  rcases lt_trichotomy s 0 with h | h | h
  · have : {y | f y ≤ s} = ∅ := by
      ext y; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]; linarith [h0 y]
    simp [this]
  · subst h
    have T := tendsto_measure_biInter_gt (μ := lam) (s := fun r : ℝ => {z | g z ≤ r}) (a := 0)
      (fun r _ => (measurableSet_le hg measurable_const).nullMeasurableSet)
      (fun i j _ hij z hz => le_trans hz hij) ⟨δ, hδ, hfin⟩
    have e : (⋂ r > (0 : ℝ), {z | g z ≤ r}) = {z | g z ≤ 0} := by
      ext z
      simp only [mem_iInter, mem_setOf_eq]
      exact ⟨fun h => le_of_forall_gt_imp_ge_of_dense fun r hr => h r hr, fun h r hr => h.trans hr.le⟩
    rw [e] at T
    refine ge_of_tendsto (ENNReal.Tendsto.const_mul T (Or.inr ENNReal.coe_ne_top)) ?_
    filter_upwards [Ioc_mem_nhdsGT hδ] with r hr
    have hsub : {y | f y ≤ 0} ⊆ {y | f y ≤ r} := by
      intro y hy
      simp only [mem_setOf_eq] at hy ⊢
      exact hy.trans hr.1.le
    exact (measure_mono hsub).trans (H r hr.1 hr.2)
  · exact H s h hs

theorem sqrt_set {A : Type*} (f : A → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    {x | Real.sqrt (f x) ≤ r} = {x | f x ≤ r ^ 2} := by
  ext x; simp only [mem_setOf_eq]; exact Real.sqrt_le_left hr

theorem vol_sq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {r : ℝ} (hr : 0 ≤ r) :
    volume {x : E | ‖x‖ ^ 2 ≤ r ^ 2} =
      ENNReal.ofReal (r ^ Module.finrank ℝ E) * volume (Metric.ball (0 : E) 1) := by
  rw [← Measure.addHaar_closedBall volume (0 : E) hr]
  congr 1
  ext x
  simp only [mem_setOf_eq, mem_closedBall_zero_iff]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) hr two_ne_zero

theorem Asym.compare {ν : Measure X} {f : X → ℝ} {d : ℕ} (h : Asym ν f d) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (a : ℝ≥0) (ha : 1 < a) : ∃ δ : ℝ, 0 < δ ∧
      (∀ s ≤ δ, ν {y | f y ≤ s} ≤ a * volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s}) ∧
      (∀ s ≤ δ, volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ≤ a * ν {y | f y ≤ s}) := by
  set ω := volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) with hω
  have ω0 : ω ≠ 0 := (Metric.measure_ball_pos _ _ one_pos).ne'
  have ωt : ω ≠ ⊤ := measure_ball_lt_top.ne
  have ha' : (1 : ℝ≥0∞) < a := by exact_mod_cast ha
  have lt1 : ω < a * ω := by
    conv_lhs => rw [← one_mul ω]
    exact ENNReal.mul_lt_mul_left ω0 ωt ha'
  have E1 := h.eventually (gt_mem_nhds lt1)
  have E2 := (ENNReal.Tendsto.const_mul (a := (a : ℝ≥0∞)) h (Or.inr ENNReal.coe_ne_top)).eventually
    (lt_mem_nhds lt1)
  obtain ⟨ρ, hρ, hE⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 (E1.and E2)
  have hρ' : (0 : ℝ) < ρ := hρ
  have key : ∀ s, 0 < s → s ≤ ρ ^ 2 →
      ν {y | f y ≤ s} ≤ a * volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ∧
      volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ s} ≤ a * ν {y | f y ≤ s} := by
    intro s hs hsρ
    obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ s = r ^ 2 :=
      ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
    have hrρ : r ≤ ρ := (pow_le_pow_iff_left₀ hr.le hρ'.le two_ne_zero).1 hsρ
    obtain ⟨e1, e2⟩ := hE ⟨hr, hrρ⟩
    rw [sqrt_set f hr.le] at e1 e2
    have p0 : ENNReal.ofReal (r ^ d) ≠ 0 := by simpa using pow_pos hr d
    rw [vol_sq _ hr.le, finrank_euclideanSpace_fin, ← hω]
    constructor
    · have := (ENNReal.div_le_iff p0 ENNReal.ofReal_ne_top).1 e1.le
      refine this.trans (le_of_eq ?_)
      ring
    · rw [← mul_div_assoc] at e2
      have := (ENNReal.le_div_iff_mul_le (Or.inl p0) (Or.inl ENNReal.ofReal_ne_top)).1 e2.le
      rwa [mul_comm] at this
  have fin1 : volume {z : EuclideanSpace ℝ (Fin d) | ‖z‖ ^ 2 ≤ ρ ^ 2} ≠ ⊤ := by
    rw [vol_sq _ hρ'.le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ωt
  refine ⟨ρ ^ 2, by positivity, ?_, ?_⟩
  · exact le_of_pos _ _ (by fun_prop) h0 a (by positivity) fin1 fun s h1 h2 => (key s h1 h2).1
  · refine le_of_pos _ _ hf (fun _ => by positivity) a (by positivity) ?_ fun s h1 h2 => (key s h1 h2).2
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top fin1) (key _ (by positivity) le_rfl).1

theorem vol_prod (d e : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).prod (volume : Measure (EuclideanSpace ℝ (Fin e)))
      {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ r ^ 2} =
      ENNReal.ofReal (r ^ (d + e)) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d + e))) 1) := by
  let P := WithLp 2 (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e))
  have hP : Module.finrank ℝ P = d + e := by
    rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq]; simp
  let T : P ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (d + e)) := ((stdOrthonormalBasis ℝ P).reindex (finCongr hP)).repr
  have m : MeasurableSet {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin e) |
      ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ r ^ 2} := measurableSet_le (by fun_prop) measurable_const
  have h1 := (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin d))
    (EuclideanSpace ℝ (Fin e))).measure_preimage m.nullMeasurableSet
  have m2 : MeasurableSet {z : EuclideanSpace ℝ (Fin (d + e)) | ‖z‖ ^ 2 ≤ r ^ 2} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 := T.measurePreserving.measure_preimage m2.nullMeasurableSet
  have h3 := vol_sq (EuclideanSpace ℝ (Fin (d + e))) hr
  rw [finrank_euclideanSpace_fin] at h3
  rw [← h3, ← h2]
  refine h1.symm.trans ?_
  congr 1
  ext z
  simp only [mem_preimage, mem_setOf_eq, LinearIsometryEquiv.norm_map]
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rfl

theorem tendsto_of_squeeze {ι : Type*} {l : Filter ι} {F : ι → ℝ≥0∞} {ω : ℝ≥0∞} (hω : ω ≠ ⊤)
    (H : ∀ a : ℝ≥0, 1 < a → ∀ᶠ i in l, F i ≤ a * a * ω ∧ ω ≤ a * a * F i) : Tendsto F l (𝓝 ω) := by
  have C : ∀ u : ℝ≥0∞, u ≠ ⊤ → Tendsto (fun a : ℝ≥0 => (a : ℝ≥0∞) * a * u) (𝓝[>] 1) (𝓝 u) := by
    intro u hu
    have h1 : Tendsto (fun a : ℝ≥0 => ((a * a : ℝ≥0) : ℝ≥0∞)) (𝓝 1) (𝓝 ((1 * 1 : ℝ≥0) : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.comp (continuous_id.mul continuous_id)).tendsto 1
    have h2 := ENNReal.Tendsto.mul_const (b := u) h1 (Or.inr hu)
    simpa using h2.mono_left nhdsWithin_le_nhds
  refine tendsto_order.2 ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨a, h1, h2⟩ := (((C u hu.ne_top).eventually (gt_mem_nhds hu)).and self_mem_nhdsWithin).exists
    filter_upwards [H a h2] with i hi
    by_contra hc
    exact absurd (hi.2.trans (mul_le_mul_right (not_lt.1 hc) _)) (not_le.2 h1)
  · obtain ⟨a, h1, h2⟩ := (((C ω hω).eventually (gt_mem_nhds hu)).and self_mem_nhdsWithin).exists
    filter_upwards [H a h2] with i hi
    exact hi.1.trans_lt h1

theorem Asym.prod {ν : Measure X} {μ : Measure Y} [SFinite ν] [SFinite μ] {f : X → ℝ} {g : Y → ℝ} {d e : ℕ}
    (h₁ : Asym ν f d) (h₂ : Asym μ g e) (hf : Measurable f) (hg : Measurable g)
    (f0 : ∀ x, 0 ≤ f x) (g0 : ∀ y, 0 ≤ g y) : Asym (ν.prod μ) (fun z => f z.1 + g z.2) (d + e) := by
  refine tendsto_of_squeeze measure_ball_lt_top.ne fun a ha => ?_
  obtain ⟨δ₁, p1, A1, B1⟩ := h₁.compare hf f0 a ha
  obtain ⟨δ₂, p2, A2, B2⟩ := h₂.compare hg g0 a ha
  have hδ : 0 < min δ₁ δ₂ := lt_min p1 p2
  filter_upwards [Ioc_mem_nhdsGT (Real.sqrt_pos.2 hδ)] with r hr
  have hr2 : r ^ 2 ≤ min δ₁ δ₂ := (Real.le_sqrt hr.1.le hδ.le).1 hr.2
  have p0 : ENNReal.ofReal (r ^ (d + e)) ≠ 0 := by simpa using pow_pos hr.1 (d + e)
  have U := prod_le_both ν μ volume volume hf hg (by fun_prop) (by fun_prop) f0 (fun _ => by positivity) a a
    (fun s hs => A1 s (hs.trans (min_le_left _ _))) (fun s hs => A2 s (hs.trans (min_le_right _ _))) hr2
  have L := prod_le_both volume volume ν μ (by fun_prop) (by fun_prop) hf hg (fun _ => by positivity) g0 a a
    (fun s hs => B1 s (hs.trans (min_le_left _ _))) (fun s hs => B2 s (hs.trans (min_le_right _ _))) hr2
  rw [vol_prod d e hr.1.le] at U L
  rw [sqrt_set _ hr.1.le]
  constructor
  · refine (ENNReal.div_le_iff p0 ENNReal.ofReal_ne_top).2 (U.trans (le_of_eq ?_))
    ring
  · rw [← mul_div_assoc]
    refine (ENNReal.le_div_iff_mul_le (Or.inl p0) (Or.inl ENNReal.ofReal_ne_top)).2 ?_
    rwa [mul_comm]

end GlobalTheory.GaugeProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumTransversalEqTsumOrbitQuotientGeneral
section
open scoped ENNReal Classical

namespace GlobalTheory

theorem tsum_transversal_eq_tsum_orbitQuotient_general {G X A M : Type} [Group G] [MulAction G X]
    [AddCommMonoid M] [TopologicalSpace M] (ι : A → X) (T : X → Prop)
    (hT : ∀ g : G, ∀ x, T x → T (g • x)) (hι : ∀ a, T (ι a))
    (hsurj : ∀ x, T x → ∃ a, ∃ g : G, g • ι a = x)
    (hinj : ∀ a b, (∃ g : G, g • ι a = ι b) → a = b)
    (φ : X → M) (hφ : ∀ g : G, ∀ x, T x → φ (g • x) = φ x) :
    ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  let c : A → MulAction.orbitRel.Quotient G X := fun a => Quotient.mk (MulAction.orbitRel G X) (ι a)
  have hc : Function.Injective c := by
    intro a b hab
    have h : (MulAction.orbitRel G X) (ι a) (ι b) := Quotient.exact hab
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := h
    exact (hinj b a ⟨g, hg⟩).symm
  have hout : ∀ a, ∃ g : G, g • ι a = (c a).out := by
    intro a
    have h : (MulAction.orbitRel G X) ((c a).out) (ι a) := Quotient.exact (Quotient.out_eq (c a))
    rw [MulAction.orbitRel_apply] at h
    exact h
  have hsupp : Function.support
      (fun o : MulAction.orbitRel.Quotient G X => if T o.out then φ o.out else 0) ⊆ Set.range c := by
    intro o ho
    have hTo : T o.out := by
      by_contra hn
      exact ho (if_neg hn)
    obtain ⟨a, g, hg⟩ := hsurj _ hTo
    refine ⟨a, ?_⟩
    rw [← Quotient.out_eq o]
    apply Quotient.sound
    have h : (MulAction.orbitRel G X) o.out (ι a) := by
      rw [MulAction.orbitRel_apply]
      exact ⟨g, hg⟩
    exact (MulAction.orbitRel G X).symm h
  rw [← hc.tsum_eq hsupp]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg⟩ := hout a
  rw [← hg, if_pos (hT g _ (hι a)), hφ g _ (hι a)]

theorem tsum_transversal_eq_tsum_orbitQuotient : ∀ {G X A : Type} [Group G] [MulAction G X] (ι : A → X) (T : X → Prop), (∀ g : G, ∀ x, T x → T (g • x)) → (∀ a, T (ι a)) → (∀ x, T x → ∃ a, ∃ g : G, g • ι a = x) → (∀ a b, (∃ g : G, g • ι a = ι b) → a = b) → (∀ φ : X → ℂ, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0) ∧ ∀ φ : X → ℝ≥0∞, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  intro G X A _ _ ι T hT hι hsurj hinj
  exact ⟨fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ,
    fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ⟩

end GlobalTheory
end

