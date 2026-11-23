module

public import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.HolNull
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem null_of_lines {n : ℕ} (Z : Set (Fin n → ℂ)) (hZ : MeasurableSet Z) (p : Fin n → ℂ)
    (h : ∀ x : Fin n → ℂ, ∀ᵐ t : ℝ, p + t • x ∉ Z) : volume Z = 0 := by
  have hm : MeasurableSet {u : (Fin n → ℂ) × ℝ | p + u.2 • u.1 ∉ Z} :=
    (hZ.compl).preimage (f := fun u : (Fin n → ℂ) × ℝ => p + u.2 • u.1) (Continuous.measurable (by fun_prop))
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ x : Fin n → ℂ, p + t • x ∉ Z :=
    (Measure.ae_ae_comm (p := fun (x : Fin n → ℂ) (t : ℝ) => p + t • x ∉ Z) hm).mp (Eventually.of_forall h)
  have h2 : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff]
  obtain ⟨t, ht, ht0⟩ := (h1.and h2).exists
  have h3 : volume ((t • ·) ⁻¹' ((p + ·) ⁻¹' Z)) = 0 := by
    rw [ae_iff] at ht
    simpa [Set.preimage] using ht
  rw [Measure.addHaar_preimage_smul volume ht0, measure_preimage_add, mul_eq_zero] at h3
  refine h3.resolve_left ?_
  rw [ENNReal.ofReal_eq_zero, not_le, abs_pos]
  exact inv_ne_zero (pow_ne_zero _ ht0)

theorem zero_set_null {n : ℕ} (V : Set (Fin n → ℂ)) (hV : IsOpen V) (hc : Convex ℝ V) (f : (Fin n → ℂ) → ℂ)
    (hf : DifferentiableOn ℂ f V) (p : Fin n → ℂ) (hp : p ∈ V) (hfp : f p ≠ 0) : volume {x ∈ V | f x = 0} = 0 := by
  have hm : MeasurableSet {x ∈ V | f x = 0} := by
    have : {x ∈ V | f x = 0} = V \ (V ∩ f ⁻¹' {0}ᶜ) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff]
      tauto
    rw [this]
    exact hV.measurableSet.diff (hf.continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton).measurableSet
  refine null_of_lines _ hm p fun x => ?_
  set S : Set ℝ := (fun t : ℝ => p + t • x) ⁻¹' V with hS
  have hSo : IsOpen S := hV.preimage (by fun_prop)
  have hSc : Convex ℝ S := by
    intro s hs t ht a b ha hb hab
    have := hc hs ht ha hb hab
    have e : a • (p + s • x) + b • (p + t • x) = p + (a • s + b • t) • x := by
      have : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
      conv_rhs => rw [this]
      simp only [smul_add, add_smul, smul_assoc]
      abel
    rw [e] at this
    exact this
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => f (p + s • x)) ((fun s : ℂ => p + s • x) ⁻¹' V) := by
    refine DifferentiableOn.analyticOnNhd ?_ (hV.preimage (by fun_prop))
    exact hf.comp (by fun_prop) fun s hs => hs
  have hh : AnalyticOnNhd ℝ (fun t : ℝ => f (p + t • x)) S := by
    intro t ht
    have h1 : AnalyticAt ℝ (fun s : ℂ => f (p + s • x)) (Complex.ofRealCLM t) :=
      (hg t (by simpa [hS] using ht)).restrictScalars
    have := h1.comp (Complex.ofRealCLM.analyticAt t)
    simpa [Function.comp_def] using this
  rcases hh.eqOn_zero_or_eventually_ne_zero_of_preconnected hSc.isPreconnected with h0 | h0
  · exact (hfp (by simpa using h0 (x := 0) (by simpa [hS] using hp))).elim
  · have h1 : ∀ᵐ t ∂(volume.restrict S), f (p + t • x) ≠ 0 := ae_restrict_le_codiscreteWithin hSo.measurableSet h0
    rw [ae_restrict_iff' hSo.measurableSet] at h1
    filter_upwards [h1] with t ht hz using ht hz.1 hz.2

theorem top_le_iff_pt {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (q : Sp ℂ) : ⊤ ≤ x ⁻¹ᵁ U ↔ x q ∈ U := by
  refine ⟨fun h => h (x := q) trivial, fun h q' _ => ?_⟩
  have : q' = q := Subsingleton.elim (α := PrimeSpectrum ℂ) q' q
  rw [this]
  exact h

theorem local_null {X : Scheme.{0}} {n : ℕ} {B : Set (Fin n → ℂ)} {y : (Fin n → ℂ) → (Sp ℂ ⟶ X)} (U : X.Opens)
    (hy : IsHolTo B y) {b : Fin n → ℂ} (hb : b ∈ B) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ b ∈ V ∧ V ⊆ B ∧
      ((∃ b' ∈ V, ⊤ ≤ y b' ⁻¹ᵁ U) → volume {b' ∈ V | ¬ ⊤ ≤ y b' ⁻¹ᵁ U} = 0) := by
  let q : Sp ℂ := (default : PrimeSpectrum ℂ)
  obtain ⟨W, hW, hbW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y b q) (U := ⊤) trivial
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hy W 0).1 b ⟨hb, (top_le_iff_pt _ _ q).mpr hbW⟩
  refine ⟨Metric.ball b ε, Metric.isOpen_ball, Metric.mem_ball_self hε, fun z hz => (hball hz).1, ?_⟩
  rintro ⟨b', hb', hU⟩
  obtain ⟨f, hfU, hf⟩ := hW.exists_basicOpen_le (V := U) ⟨y b' q, (top_le_iff_pt _ _ q).mp hU⟩
    ((top_le_iff_pt _ _ q).mp (hball hb').2)
  refine measure_mono_null ?_ (zero_set_null (Metric.ball b ε) Metric.isOpen_ball (convex_ball b ε)
    (fun z => valAt' (y z) W f) ((hy W f).2.mono hball) b' hb' ((valAt'_ne_zero_iff _ _ (hball hb').2 f q).mpr hf))
  rintro z ⟨hz, hzU⟩
  refine ⟨hz, ?_⟩
  by_contra hne
  exact hzU ((top_le_iff_pt _ _ q).mpr (hfU ((valAt'_ne_zero_iff _ _ (hball hz).2 f q).mp hne)))

theorem holNull : HolNull := by
  intro X n B y U _ hBc hy ⟨b₀, hb₀, hU₀⟩
  choose! V hVo hVb hVB hV using fun b (hb : b ∈ B) => local_null U hy hb
  set G : Set (Fin n → ℂ) := {b | ⊤ ≤ y b ⁻¹ᵁ U} with hG
  have hsub : B ⊆ interior (closure G) := by
    refine hBc.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
      (Set.disjoint_left.mpr fun z hz hz' => hz' (interior_subset hz)) (fun b hb => ?_) ?_ |>.trans le_rfl
    · by_cases hcl : b ∈ closure G
      · left
        refine interior_maximal (t := V b) (fun z hz => ?_) (hVo b hb) (hVb b hb)
        obtain ⟨b', hb'V, hb'G⟩ := mem_closure_iff.mp hcl (V b) (hVo b hb) (hVb b hb)
        have hnull := hV b hb ⟨b', hb'V, hb'G⟩
        by_contra hz'
        have ho : IsOpen (V b ∩ (closure G)ᶜ) := (hVo b hb).inter isClosed_closure.isOpen_compl
        refine (ho.measure_pos volume ⟨z, hz, hz'⟩).ne' (measure_mono_null ?_ hnull)
        exact fun w hw => ⟨hw.1, fun h => hw.2 (subset_closure h)⟩
      · exact Or.inr hcl
    · refine ⟨b₀, hb₀, interior_maximal (t := {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}) (fun z hz => subset_closure hz.2) (hy U 0).1 ⟨hb₀, hU₀⟩⟩
  refine measure_null_of_locally_null _ fun b hb => ?_
  obtain ⟨b', hb'V, hb'G⟩ := mem_closure_iff.mp (interior_subset (hsub hb.1)) (V b) (hVo b hb.1) (hVb b hb.1)
  refine ⟨{b' ∈ V b | ¬ ⊤ ≤ y b' ⁻¹ᵁ U}, ?_, hV b hb.1 ⟨b', hb'V, hb'G⟩⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ((hVo b hb.1).mem_nhds (hVb b hb.1))] with z hz hz'
    using ⟨hz', hz.2⟩

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.RootBr
section
noncomputable section

namespace SheetDecomposition

open Filter Topology Polynomial

theorem eval_monicOf {d : ℕ} (a : Fin d → ℂ) (x : ℂ) : (monicOf a).eval x = x ^ d + ∑ i, a i * x ^ (i : ℕ) := by
  simp [monicOf, eval_finsetSum]

theorem degree_low_lt {d : ℕ} (a : Fin d → ℂ) : (∑ i, C (a i) * X ^ (i : ℕ) : ℂ[X]).degree < d :=
  degree_sum_fin_lt a

theorem monic_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).Monic :=
  monic_X_pow_add (degree_low_lt a)

theorem natDegree_monicOf {d : ℕ} (a : Fin d → ℂ) : (monicOf a).natDegree = d := by
  apply natDegree_eq_of_degree_eq_some
  unfold monicOf
  rw [degree_add_eq_left_of_degree_lt, degree_X_pow]
  rw [degree_X_pow]
  exact degree_low_lt a

theorem root_branch {d : ℕ} (a₀ : Fin d → ℂ) (x₀ : ℂ) (h0 : (monicOf a₀).IsRoot x₀)
    (h1 : (derivative (monicOf a₀)).eval x₀ ≠ 0) :
    ∃ ψ : (Fin d → ℂ) → ℂ, ψ a₀ = x₀ ∧ ∀ᶠ a in 𝓝 a₀, DifferentiableAt ℂ ψ a ∧ (monicOf a).IsRoot (ψ a) := by
  set f : (Fin d → ℂ) × ℂ → ℂ := fun u => u.2 ^ d + ∑ i, u.1 i * u.2 ^ (i : ℕ) with hf
  have cdf : ContDiffAt ℂ 1 f (a₀, x₀) := by
    rw [hf]
    fun_prop
  have hD : fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      ContinuousLinearMap.toSpanSingleton ℂ ((derivative (monicOf a₀)).eval x₀) := by
    have e1 : HasFDerivAt (f ∘ fun x : ℂ => (a₀, x))
        (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) x₀ :=
      HasFDerivAt.comp x₀ (cdf.differentiableAt one_ne_zero).hasFDerivAt (hasFDerivAt_prodMk_right a₀ x₀)
    have e2 : (f ∘ fun x : ℂ => (a₀, x)) = fun x => (monicOf a₀).eval x := by
      funext x
      simp [hf, eval_monicOf]
    rw [e2] at e1
    exact e1.unique ((monicOf a₀).hasDerivAt x₀).hasFDerivAt
  have if₂ : (fderiv ℂ f (a₀, x₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hD]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext
    simp
  refine ⟨cdf.implicitFunction one_ne_zero if₂, cdf.implicitFunction_apply_self one_ne_zero if₂, ?_⟩
  have hc := cdf.contDiffAt_implicitFunction one_ne_zero if₂
  have hv := cdf.eventually_apply_implicitFunction one_ne_zero if₂
  filter_upwards [hc.eventually (by simp), hv] with a ha hb
  refine ⟨ha.differentiableAt one_ne_zero, ?_⟩
  have : f (a₀, x₀) = 0 := by
    have := h0
    rw [IsRoot.def, eval_monicOf] at this
    exact this
  rw [this] at hb
  rw [IsRoot.def, eval_monicOf]
  exact hb

theorem root_iff_of_injective {d : ℕ} (a : Fin d → ℂ) (r : Fin d → ℂ) (hr : Function.Injective r)
    (h : ∀ i, (monicOf a).IsRoot (r i)) (x : ℂ) : (monicOf a).IsRoot x ↔ ∃ i, x = r i := by
  classical
  refine ⟨fun hx => ?_, fun ⟨i, hi⟩ => hi ▸ h i⟩
  by_contra hne
  push Not at hne
  have hsub : insert x (Finset.univ.image r) ⊆ (monicOf a).roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hx
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
      exact h i
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by
    intro hz
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
    exact hne i hi.symm), Finset.card_image_of_injective _ hr, Finset.card_univ, Fintype.card_fin] at h1
  have h2 := (Multiset.toFinset_card_le (monicOf a).roots).trans (card_roots' (monicOf a))
  rw [natDegree_monicOf] at h2
  omega

theorem exists_roots {d : ℕ} (a : Fin d → ℂ) (hs : (monicOf a).Separable) :
    ∃ r : Fin d → ℂ, Function.Injective r ∧ ∀ i, (monicOf a).IsRoot (r i) := by
  classical
  have hc : (monicOf a).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree, natDegree_monicOf]
  let e := Finset.equivFinOfCardEq hc
  refine ⟨fun i => (e.symm i : ℂ), Subtype.val_injective.comp e.symm.injective, fun i => ?_⟩
  have := (e.symm i).2
  rw [Multiset.mem_toFinset, mem_roots (monic_monicOf a).ne_zero] at this
  exact this

theorem rootBranches : RootBranches := by
  intro n d T a hT ha hs t₀ ht₀
  obtain ⟨r, hr, hroot⟩ := exists_roots (a t₀) (hs t₀ ht₀)
  have hder : ∀ i, (derivative (monicOf (a t₀))).eval (r i) ≠ 0 := fun i => by
    have := (hs t₀ ht₀).aeval_derivative_ne_zero (x := r i) (by simpa using hroot i)
    simpa using this
  choose ψ hψ0 hψ using fun i => root_branch (a t₀) (r i) (hroot i) (hder i)
  have hca : ContinuousAt a t₀ := (ha.differentiableAt (hT.mem_nhds ht₀)).continuousAt
  have hcθ : ∀ i, ContinuousAt (fun t => ψ i (a t)) t₀ := fun i =>
    ContinuousAt.comp (f := a) (hψ i).self_of_nhds.1.continuousAt hca
  have hev : ∀ᶠ t in 𝓝 t₀, t ∈ T ∧ (∀ i, DifferentiableAt ℂ (ψ i) (a t) ∧ (monicOf (a t)).IsRoot (ψ i (a t))) ∧
      ∀ i j, i ≠ j → ψ i (a t) ≠ ψ j (a t) := by
    refine (hT.eventually_mem ht₀).and (Eventually.and (eventually_all.mpr fun i => hca.tendsto.eventually (hψ i)) ?_)
    refine eventually_all.mpr fun i => eventually_all.mpr fun j => ?_
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => (h hij).elim
    · have : ∀ᶠ t in 𝓝 t₀, ψ i (a t) - ψ j (a t) ≠ 0 :=
        ((hcθ i).sub (hcθ j)).eventually_ne (by
          show ψ i (a t₀) - ψ j (a t₀) ≠ 0
          rw [hψ0, hψ0]
          exact sub_ne_zero.mpr (hr.ne hij))
      filter_upwards [this] with t ht _ using sub_ne_zero.mp ht
  obtain ⟨V, hV, hVo, hVt⟩ := eventually_nhds_iff.mp hev
  refine ⟨V, fun i t => ψ i (a t), hVo, hVt, fun t ht => (hV t ht).1, fun i t ht => ?_, fun t ht => ?_⟩
  · exact (((hV t ht).2.1 i).1.comp t (ha.differentiableAt (hT.mem_nhds (hV t ht).1))).differentiableWithinAt
  · have hi : Function.Injective fun i => ψ i (a t) := fun i j h => by
      by_contra hij
      exact (hV t ht).2.2 i j hij h
    exact ⟨hi, root_iff_of_injective (a t) _ hi fun i => ((hV t ht).2.1 i).2⟩

end SheetDecomposition
end
end

