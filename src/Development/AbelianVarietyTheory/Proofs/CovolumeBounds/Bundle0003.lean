module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsQr
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.QRDecomp


open Matrix in
open scoped ComplexOrder in
theorem _root_.GlobalTheory.QRDecomp.exists_qr (n m : ℕ) (A : Matrix (Fin n) (Fin m) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    ∃ (Q : Matrix (Fin n) (Fin m) ℂ) (u : Matrix (Fin m) (Fin m) ℂ),
      Qᴴ * Q = 1 ∧ u.BlockTriangular id ∧ IsUnit u.det ∧ A = Q * u := by
  classical
  have hinj : Function.Injective A.mulVec := by
    intro v w h
    have h2 : (Aᴴ * A) *ᵥ v = (Aᴴ * A) *ᵥ w := by rw [← mulVec_mulVec, ← mulVec_mulVec, h]
    exact (mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hA)) h2
  have hS : (Aᴴ * A).PosDef := PosDef.conjTranspose_mul_self A hinj
  set L := LDL.lowerInv hS
  set d := LDL.diagEntries hS
  haveI : Invertible L := LDL.invertibleLowerInv hS
  have hLu : IsUnit L.det := isUnit_det_of_invertible L
  have hD : diagonal d = L * (Aᴴ * A) * Lᴴ := LDL.diag_eq_lowerInv_conj hS
  have hDpos : (diagonal d).PosDef := by
    rw [hD]
    exact hS.mul_mul_conjTranspose_same
      (vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hLu))
  have hd : ∀ i, 0 < d i := fun i => by simpa using hDpos.diag_pos (i := i)
  have hdre : ∀ i, d i = ((d i).re : ℂ) ∧ 0 < (d i).re := fun i => by
    have h := hd i
    rw [Complex.pos_iff] at h
    exact ⟨Complex.ext (by simp) (by simp [h.2]), h.1⟩
  let r : Fin m → ℂ := fun i => ((Real.sqrt (d i).re : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i => by
    simp only [r, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (hdre i).2).ne'
  have hrr : ∀ i, star (r i) * r i = d i := fun i => by
    simp only [r, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hdre i).2.le, ← (hdre i).1]
  have hLt : Lᴴ.BlockTriangular id := fun i j hij => by
    have h : LDL.lowerInv hS j i = 0 := LDL.isLowerTriangular_lowerInv hS hij
    simp [conjTranspose_apply, L, h]
  refine ⟨A * Lᴴ * diagonal (fun i => (r i)⁻¹), diagonal r * (Lᴴ)⁻¹, ?_, ?_, ?_, ?_⟩
  · have h1 : (A * Lᴴ * diagonal fun i => (r i)⁻¹)ᴴ * (A * Lᴴ * diagonal fun i => (r i)⁻¹)
        = (diagonal fun i => star (r i)⁻¹) * (L * (Aᴴ * A) * Lᴴ) * diagonal fun i => (r i)⁻¹ := by
      simp only [conjTranspose_mul, diagonal_conjTranspose, conjTranspose_conjTranspose,
        Matrix.mul_assoc]
      rfl
    rw [h1, ← hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← hrr i]
    have h0 := hr0 i
    have h0' : star (r i) ≠ 0 := star_ne_zero.mpr h0
    rw [star_inv₀]
    field_simp
  · exact (blockTriangular_diagonal r).mul (blockTriangular_inv_of_blockTriangular hLt)
  · rw [det_mul, det_diagonal]
    exact (IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hr0 i)).mul
      (isUnit_nonsing_inv_det _ (isUnit_det_of_invertible Lᴴ))
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have h1 : (fun i => (r i)⁻¹ * r i) = fun _ => (1 : ℂ) :=
      funext fun i => inv_mul_cancel₀ (hr0 i)
    rw [h1, diagonal_one, Matrix.one_mul, mul_inv_of_invertible, Matrix.mul_one]

end GlobalTheory.QRDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
section
open MeasureTheory Filter Metric Set
open scoped Topology Interval

namespace GlobalTheory

variable {T : Type*} [MeasurableSpace T] {μ : Measure T}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem aestronglyMeasurable_fderiv_apply_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) (v : E) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀ v) μ := by
  classical
  let f : ℂ → T → V := fun c t =>
    if AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ then
      c⁻¹ • (F t (x₀ + c • v) - F t x₀) else 0
  have h0 : AEStronglyMeasurable (fun t => F t x₀) μ := hmeas.self_of_nhds
  have hev : ∀ᶠ c : ℂ in 𝓝[≠] 0, AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ := by
    have hc : Tendsto (fun c : ℂ => x₀ + c • v) (𝓝 0) (𝓝 x₀) := by
      have : Continuous (fun c : ℂ => x₀ + c • v) := by fun_prop
      simpa using this.tendsto 0
    exact (hc.eventually hmeas).filter_mono nhdsWithin_le_nhds
  refine aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℂ)) (f := f) (fun c => ?_) ?_
  · by_cases h : AEStronglyMeasurable (fun t => F t (x₀ + c • v)) μ
    · simp only [f, if_pos h]
      exact (h.sub h0).const_smul c⁻¹
    · simp only [f, if_neg h]
      exact aestronglyMeasurable_const
  · filter_upwards [hdiff] with t ht
    have h1 := hasLineDerivAt_iff_tendsto_slope_zero.1 (ht.hasFDerivAt.hasLineDerivAt v)
    refine h1.congr' ?_
    filter_upwards [hev] with c hc
    simp only [f, if_pos hc]

variable [FiniteDimensional ℂ E]

theorem aestronglyMeasurable_fderiv_of_param {F : T → E → V} {x₀ : E}
    (hmeas : ∀ᶠ y in 𝓝 x₀, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀) :
    AEStronglyMeasurable (fun t => fderiv ℂ (F t) x₀) μ := by
  let b := Module.finBasis ℂ E
  have key : (fun t => fderiv ℂ (F t) x₀) = fun t =>
      ∑ i, ContinuousLinearMap.smulRightL ℂ E V
        (LinearMap.toContinuousLinearMap (b.coord i)) (fderiv ℂ (F t) x₀ (b i)) := by
    funext t
    ext v
    have h : fderiv ℂ (F t) x₀ v = ∑ i, (b.repr v) i • fderiv ℂ (F t) x₀ (b i) := by
      conv_lhs => rw [← b.sum_repr v]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul]
    simpa using h
  rw [key]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  exact (ContinuousLinearMap.smulRightL ℂ E V
    (LinearMap.toContinuousLinearMap (b.coord i))).continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_fderiv_apply_of_param hmeas hdiff (b i))

set_option linter.unusedSectionVars false

variable [CompleteSpace V]

theorem hasFDerivAt_integral_of_holomorphic_of_dominated {F : T → E → V} {x₀ : E} {s : Set E}
    {bound : T → ℝ} (hs : s ∈ 𝓝 x₀)
    (hmeas : ∀ y ∈ s, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) s)
    (hbound : ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) (hint : Integrable bound μ) :
    Integrable (fun t => F t x₀) μ ∧ Integrable (fun t => fderiv ℂ (F t) x₀) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x₀ ∂μ) x₀ := by
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 hs
  have hx₀ : x₀ ∈ s := mem_of_mem_nhds hs
  have hat : ∀ᵐ t ∂μ, DifferentiableAt ℂ (F t) x₀ := hdiff.mono fun t ht => ht.differentiableAt hs
  have hF₀ : Integrable (fun t => F t x₀) μ :=
    hint.mono' (hmeas x₀ hx₀) (hbound.mono fun t ht => ht x₀ hx₀)
  refine ⟨hF₀, ?_⟩
  refine hasFDerivAt_integral_of_dominated_loc_of_lip' (𝕜 := ℂ) (F := fun y t => F t y)
    (F' := fun t => fderiv ℂ (F t) x₀) (bound := fun t => 2 * bound t / r)
    (ball_mem_nhds x₀ hr) (fun y hy => hmeas y (hrs hy)) hF₀
    (aestronglyMeasurable_fderiv_of_param (Filter.mem_of_superset hs hmeas) hat) ?_
    ((hint.const_mul 2).div_const r) (hat.mono fun t ht => ht.hasFDerivAt)
  filter_upwards [hdiff, hbound] with t ht hb y hy
  have hmaps : MapsTo (F t) (ball x₀ r) (closedBall (F t x₀) (2 * bound t)) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hb z (hrs hz)
    have h2 := hb x₀ hx₀
    linarith [norm_sub_le (F t z) (F t x₀)]
  simpa [dist_eq_norm] using
    Complex.dist_le_div_mul_dist_of_mapsTo_ball (ht.mono hrs) hmaps hy

theorem differentiableOn_integral_of_holomorphic_of_locally_dominated {F : T → E → V}
    {U : Set E} (hU : IsOpen U)
    (hmeas : ∀ y ∈ U, AEStronglyMeasurable (fun t => F t y) μ)
    (hdiff : ∀ᵐ t ∂μ, DifferentiableOn ℂ (F t) U)
    (hdom : ∀ x ∈ U, ∃ s ∈ 𝓝 x, ∃ bound : T → ℝ, Integrable bound μ ∧
      ∀ᵐ t ∂μ, ∀ y ∈ s, ‖F t y‖ ≤ bound t) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  have key : ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
      HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
    intro x hx
    obtain ⟨s, hs, bound, hint, hb⟩ := hdom x hx
    exact hasFDerivAt_integral_of_holomorphic_of_dominated (s := s ∩ U)
      (inter_mem hs (hU.mem_nhds hx)) (fun y hy => hmeas y hy.2)
      (hdiff.mono fun t ht => ht.mono inter_subset_right)
      (hb.mono fun t ht y hy => ht y hy.1) hint
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩

theorem differentiableOn_setIntegral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] {F : T → E → V} {U : Set E} (hU : IsOpen U) {S K : Set T}
    (hK : IsCompact K) (hSK : S ⊆ K) (hS : MeasurableSet S) (hfin : μ S ≠ ⊤)
    (hcont : ContinuousOn (Function.uncurry F) (K ×ˢ U))
    (hdiff : ∀ t ∈ S, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in S, F t y ∂μ) U ∧
      ∀ x ∈ U, IntegrableOn (fun t => F t x) S μ ∧
        IntegrableOn (fun t => fderiv ℂ (F t) x) S μ ∧
        HasFDerivAt (fun y => ∫ t in S, F t y ∂μ) (∫ t in S, fderiv ℂ (F t) x ∂μ) x := by
  have : ProperSpace E := FiniteDimensional.proper ℂ E
  have : IsFiniteMeasure (μ.restrict S) := ⟨by simpa using hfin.lt_top⟩
  refine differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := μ.restrict S) hU
    (fun y hy => ?_) (ae_restrict_of_forall_mem hS hdiff) (fun x hx => ?_)
  · have : ContinuousOn (fun t => F t y) K :=
      hcont.comp (f := fun t => (t, y)) (by fun_prop) fun t ht => ⟨ht, hy⟩
    exact this.aestronglyMeasurable_of_subset_isCompact hK hS hSK
  · obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
    obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall x r)).exists_bound_of_continuousOn
      (hcont.mono (prod_mono subset_rfl hrU))
    refine ⟨closedBall x r, closedBall_mem_nhds x hr, fun _ => C, integrable_const C, ?_⟩
    exact ae_restrict_of_forall_mem hS fun t ht y hy => hC (t, y) ⟨hSK ht, hy⟩

theorem differentiableOn_integral_of_holomorphic_of_continuousOn [TopologicalSpace T]
    [OpensMeasurableSpace T] [CompactSpace T] [IsFiniteMeasure μ] {F : T → E → V} {U : Set E}
    (hU : IsOpen U) (hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ U))
    (hdiff : ∀ t, DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t, F t y ∂μ) U ∧
      ∀ x ∈ U, Integrable (fun t => F t x) μ ∧ Integrable (fun t => fderiv ℂ (F t) x) μ ∧
        HasFDerivAt (fun y => ∫ t, F t y ∂μ) (∫ t, fderiv ℂ (F t) x ∂μ) x := by
  simpa only [Measure.restrict_univ, integrableOn_univ] using
    differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := μ) hU isCompact_univ
      subset_rfl MeasurableSet.univ (measure_ne_top μ _) hcont fun t _ => hdiff t

theorem differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn {F : ℝ → E → V}
    {U : Set E} (hU : IsOpen U) {a b : ℝ}
    (hcont : ContinuousOn (Function.uncurry F) ([[a, b]] ×ˢ U))
    (hdiff : ∀ t ∈ [[a, b]], DifferentiableOn ℂ (F t) U) :
    DifferentiableOn ℂ (fun y => ∫ t in a..b, F t y) U ∧
      ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
        IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
        HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
  have h := differentiableOn_setIntegral_of_holomorphic_of_continuousOn (μ := volume) hU
    (isCompact_uIcc (a := a) (b := b)) uIoc_subset_uIcc measurableSet_uIoc
    (by simp [uIoc]) hcont fun t ht => hdiff t (uIoc_subset_uIcc ht)
  have key : ∀ x ∈ U, IntervalIntegrable (fun t => F t x) volume a b ∧
      IntervalIntegrable (fun t => fderiv ℂ (F t) x) volume a b ∧
      HasFDerivAt (fun y => ∫ t in a..b, F t y) (∫ t in a..b, fderiv ℂ (F t) x) x := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := h.2 x hx
    refine ⟨intervalIntegrable_iff.2 h1, intervalIntegrable_iff.2 h2, ?_⟩
    simp only [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    split_ifs
    · simpa using h3
    · simpa using h3.fun_neg
  exact ⟨fun x hx => (key x hx).2.2.differentiableAt.differentiableWithinAt, key⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe
section
open Module

namespace GlobalTheory

section Subgroups

variable {M : Type*} [AddCommGroup M]

theorem exists_ker_eq_of_index_prime {p : ℕ} (hp : p.Prime) (H : AddSubgroup M)
    (hH : H.index = p) : ∃ f : M →ₗ[ℤ] ZMod p, f.toAddMonoidHom.ker = H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have e : (M ⧸ H) ≃+ ZMod p := addEquivOfPrimeCardEq (p := p) hH (Nat.card_zmod p)
  refine ⟨(e.toAddMonoidHom.comp (QuotientAddGroup.mk' H)).toIntLinearMap, ?_⟩
  ext x
  simp [AddMonoidHom.mem_ker]

theorem encard_setOf_index_prime_le [Module.Free ℤ M] [Module.Finite ℤ M] {p : ℕ}
    (hp : p.Prime) :
    {H : AddSubgroup M | H.index = p}.encard ≤ ((p ^ finrank ℤ M : ℕ) : ℕ∞) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let b := Module.finBasis ℤ M
  let φ : (Fin (finrank ℤ M) → ZMod p) → AddSubgroup M :=
    fun w => (b.constr ℤ w).toAddMonoidHom.ker
  have hsub : {H : AddSubgroup M | H.index = p} ⊆ φ '' Set.univ := by
    intro H hH
    obtain ⟨f, hf⟩ := exists_ker_eq_of_index_prime hp H hH
    refine ⟨(b.constr ℤ).symm f, Set.mem_univ _, ?_⟩
    simp only [φ, LinearEquiv.apply_symm_apply]
    exact hf
  refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
  rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
  simp

theorem exists_le_relIndex_eq_prime {p : ℕ} (hp : p.Prime) (H : AddSubgroup M)
    (h0 : H.index ≠ 0) (hd : p ∣ H.index) :
    ∃ K : AddSubgroup M, H ≤ K ∧ H.relIndex K = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : H.FiniteIndex := ⟨h0⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := M ⧸ H) p hd
  refine ⟨(AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H), ?_, ?_⟩
  · intro y hy
    simp only [AddSubgroup.mem_comap, QuotientAddGroup.mk'_apply]
    rw [(QuotientAddGroup.eq_zero_iff y).2 hy]
    exact zero_mem _
  · have h1 : H = (⊥ : AddSubgroup (M ⧸ H)).comap (QuotientAddGroup.mk' H) := by
      ext y; simp
    have h2 := AddSubgroup.relIndex_comap (⊥ : AddSubgroup (M ⧸ H)) (QuotientAddGroup.mk' H)
      ((AddSubgroup.zmultiples x).comap (QuotientAddGroup.mk' H))
    rw [← h1, AddSubgroup.map_comap_eq_self_of_surjective (QuotientAddGroup.mk'_surjective H),
      AddSubgroup.relIndex_bot_left, Nat.card_zmultiples, hx] at h2
    exact h2

theorem encard_biUnion_le_mul {α β : Type*} (s : Set α) (t : α → Set β) (a b : ℕ)
    (hs : s.encard ≤ a) (ht : ∀ i ∈ s, (t i).encard ≤ b) :
    (⋃ i ∈ s, t i).encard ≤ ((a * b : ℕ) : ℕ∞) := by
  have hfin : s.Finite := Set.finite_of_encard_le_coe hs
  have key : (⋃ i ∈ s, t i).encard ≤ s.encard * b := by
    clear hs
    induction s, hfin using Set.Finite.induction_on with
    | empty => simp
    | @insert i s hi _ ih =>
      rw [Set.biUnion_insert, Set.encard_insert_of_notMem hi, add_mul, one_mul, add_comm]
      exact (Set.encard_union_le _ _).trans (add_le_add (ht i (Set.mem_insert _ _))
        (ih fun j hj => ht j (Set.mem_insert_of_mem _ hj)))
  refine key.trans ?_
  push_cast
  gcongr

theorem setOf_le_relIndex_eq_image (K : AddSubgroup M) (m : ℕ) :
    {H : AddSubgroup M | H ≤ K ∧ H.relIndex K = m} =
      (fun H' : AddSubgroup K => H'.map K.subtype) '' {H' | H'.index = m} := by
  ext H
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨H.addSubgroupOf K, h2, by simp [AddSubgroup.addSubgroupOf_map_subtype, h1]⟩
  · rintro ⟨H', h, rfl⟩
    refine ⟨AddSubgroup.map_subtype_le _, ?_⟩
    rw [AddSubgroup.relIndex, AddSubgroup.addSubgroupOf,
      AddSubgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact h

theorem encard_setOf_index_eq_le [Module.Free ℤ M] [Module.Finite ℤ M] {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H.index = m}.encard ≤ ((m ^ finrank ℤ M : ℕ) : ℕ∞) := by
  induction m using induction_on_primes with
  | zero => exact absurd rfl hm
  | one =>
    have : {H : AddSubgroup M | H.index = 1} = {⊤} := by ext H; simp
    simp [this]
  | prime_mul p a hp ih =>
    have ha : a ≠ 0 := fun h => hm (by simp [h])
    have hsub : {H : AddSubgroup M | H.index = p * a} ⊆
        ⋃ K ∈ {K : AddSubgroup M | K.index = a}, {H | H ≤ K ∧ H.relIndex K = p} := by
      intro H hH
      have hH' : H.index = p * a := hH
      obtain ⟨K, hK, hr⟩ := exists_le_relIndex_eq_prime hp H (hH' ▸ hm) (hH' ▸ dvd_mul_right _ _)
      have := AddSubgroup.relIndex_mul_index hK
      rw [hr, hH'] at this
      exact Set.mem_biUnion (x := K) (Nat.eq_of_mul_eq_mul_left hp.pos this) ⟨hK, hr⟩
    refine (Set.encard_le_encard hsub).trans
      ((encard_biUnion_le_mul _ _ _ (p ^ finrank ℤ M) (ih ha) ?_).trans ?_)
    · intro K _
      rw [setOf_le_relIndex_eq_image]
      refine (Set.encard_image_le _ _).trans ?_
      haveI : Module.Finite ℤ K := inferInstanceAs (Module.Finite ℤ K.toIntSubmodule)
      haveI : Module.Free ℤ K := inferInstanceAs (Module.Free ℤ K.toIntSubmodule)
      refine (encard_setOf_index_prime_le hp).trans ?_
      have : finrank ℤ K ≤ finrank ℤ M := Submodule.finrank_le K.toIntSubmodule
      exact_mod_cast Nat.pow_le_pow_right hp.pos this
    · rw [mul_pow, mul_comm]

theorem encard_setOf_le_relIndex_eq_le (K : AddSubgroup M) [Module.Free ℤ K] [Module.Finite ℤ K]
    {m : ℕ} (hm : m ≠ 0) :
    {H : AddSubgroup M | H ≤ K ∧ H.relIndex K = m}.encard ≤ ((m ^ finrank ℤ K : ℕ) : ℕ∞) := by
  rw [setOf_le_relIndex_eq_image]
  exact (Set.encard_image_le _ _).trans (encard_setOf_index_eq_le hm)

theorem encard_setOf_submodule_le_relIndex_eq_le {R : Type*} [Ring R] [Module R M]
    (L : Submodule R M) [Module.Free ℤ L] [Module.Finite ℤ L] {m : ℕ} (hm : m ≠ 0) :
    {H : Submodule R M | H ≤ L ∧ H.toAddSubgroup.relIndex L.toAddSubgroup = m}.encard ≤
      ((m ^ finrank ℤ L : ℕ) : ℕ∞) := by
  haveI : Module.Free ℤ L.toAddSubgroup := inferInstanceAs (Module.Free ℤ L)
  haveI : Module.Finite ℤ L.toAddSubgroup := inferInstanceAs (Module.Finite ℤ L)
  refine le_trans ?_ (encard_setOf_le_relIndex_eq_le L.toAddSubgroup hm)
  refine Set.encard_le_encard_of_injOn (f := Submodule.toAddSubgroup) ?_
    Submodule.toAddSubgroup_injective.injOn
  rintro H ⟨h1, h2⟩
  exact ⟨h1, h2⟩

end Subgroups

section DeterminedMaps

open MeasureTheory Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end DeterminedMaps

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteInterClosedBallOfSeparated
section
open Metric MeasureTheory Module Set

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finset_card_le_of_separated (s : Finset E) {d R : ℝ} (hd : 0 < d) (hR : 0 ≤ R) (x : E)
    (hs : ∀ a ∈ s, dist a x ≤ R) (hsep : (s : Set E).Pairwise fun a b => d ≤ dist a b) :
    (s.card : ℝ) ≤ (1 + 2 * R / d) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hδ : 0 < d / 2 := by positivity
  have hρ : 0 < R + d / 2 := by positivity
  have D : Set.Pairwise (s : Set E) (Function.onFun Disjoint fun c => ball (c : E) (d / 2)) := by
    intro a ha b hb hab
    exact ball_disjoint_ball (by have := hsep ha hb hab; linarith)
  have hsub : (⋃ c ∈ s, ball (c : E) (d / 2)) ⊆ ball x (R + d / 2) := by
    refine iUnion₂_subset fun a ha => ball_subset_ball' ?_
    have := hs a ha
    linarith
  have I : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) * μ (ball 0 1)
        = μ (⋃ c ∈ s, ball (c : E) (d / 2)) := by
          rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
          simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball x (R + d / 2)) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have J : (s.card : ENNReal) * ENNReal.ofReal ((d / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + d / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (d / 2) ^ finrank ℝ E ≤ (R + d / 2) ^ finrank ℝ E := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at this
  have e : 1 + 2 * R / d = (R + d / 2) / (d / 2) := by field_simp; ring
  rw [e, div_pow, le_div_iff₀ (by positivity)]
  exact K

theorem one_add_two_mul_div_pow_le {d R : ℝ} (hd : 0 < d) (hR : d ≤ R) (n : ℕ) :
    (1 + 2 * R / d) ^ n ≤ (3 * R / d) ^ n := by
  have hR0 : 0 ≤ R := hd.le.trans hR
  refine pow_le_pow_left₀ (by positivity) ?_ n
  have h1 : 1 ≤ R / d := (one_le_div hd).2 hR
  have : 3 * R / d = R / d + 2 * R / d := by ring
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummablePiProd
section
namespace GlobalTheory.SummablePiProd

universe u_1 u_2

theorem summable_pi_prod {ι : Type u_1} [inst : Fintype ι] {J : ι → Type u_2}
    {u : (i : ι) → J i → ℝ} (h0 : ∀ (i : ι) (j : J i), (0 : ℝ) ≤ u i j)
    (hs : ∀ (i : ι), Summable (u i)) :
    Summable fun (t : (i : ι) → J i) ↦ ∏ i : ι, u i (t i) := by
  classical
  refine summable_of_sum_le (c := ∏ i, ∑' j, u i j)
    (fun t => Finset.prod_nonneg fun i _ => h0 i (t i)) ?_
  intro s
  calc ∑ t ∈ s, ∏ i, u i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, u i (t i) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun t _ _ => Finset.prod_nonneg fun i _ => h0 i (t i))
        intro t ht
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ j ∈ s.image (fun t => t i), u i j := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ i, ∑' j, u i j := by
        refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => h0 i j) ?_
        intro i _
        exact (hs i).sum_le_tsum _ (fun j _ => h0 i j)

end GlobalTheory.SummablePiProd
end

