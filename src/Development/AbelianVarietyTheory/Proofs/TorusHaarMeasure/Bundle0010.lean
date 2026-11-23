module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSelectForms
section
open ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff Matrix

namespace GlobalTheory.LeviRank

theorem exists_select_forms {K M : Type} [Field K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {n N : ℕ} (hn : Module.finrank K M = n)
    (φ : Fin N → Module.Dual K M) (hφ : ∀ x, (∀ k, φ k x = 0) → x = 0) :
    ∃ jj : Fin n → Fin N, ∀ x, (∀ k, φ (jj k) x = 0) → x = 0 := by
  classical
  have hspan : Submodule.span K (Set.range φ) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    apply mem_span_of_iInf_ker_le_ker
    intro x hx
    have : x = 0 := hφ x (fun k => by simpa using (Submodule.mem_iInf _).1 hx k)
    simp [this]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K φ
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = n := by
    have h := finrank_span_eq_card hli
    rw [hsp, hspan, finrank_top, Subspace.dual_finrank_eq, hn] at h
    exact h.symm
  let e : κ ≃ Fin n := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k => a (e.symm k), fun x hx => hφ x fun k => ?_⟩
  have hk : φ k ∈ Submodule.span K (Set.range (φ ∘ a)) := by rw [hsp, hspan]; trivial
  refine Submodule.span_induction (p := fun f _ => f x = 0) ?_ ?_ ?_ ?_ hk
  · rintro _ ⟨i, rfl⟩
    simpa using hx (e i)
  · simp
  · intro f g _ _ hf hg; simp [hf, hg]
  · intro c f _ hf; simp [hf]

theorem wJac_mulVec {n N : ℕ} (w : Fin N → V n → ℂ) (x : V n)
    (hw : ∀ k, DifferentiableAt ℂ (w k) x) (ξ : V n) (k : Fin N) :
    (wJac n N w x *ᵥ ξ.ofLp) k = fderiv ℂ (w k) x ξ := by
  have hξ : ξ = ∑ j, ξ.ofLp j • bas n j := by
    ext i
    simp [bas, Pi.single_apply]
  conv_rhs => rw [hξ]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [wJac, Matrix.mulVec, dotProduct, wd_of_differentiableAt (hw k), map_sum, map_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem main : ∀ (n N : ℕ) (w : Fin N → V n → ℂ) (U : Set (V n)), IsOpen U → (0 : V n) ∈ U →
    (∀ k, DifferentiableOn ℂ (w k) U) → (∃ k, w k 0 ≠ 0) →
    (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) 0 ξ).re) →
    ∃ (j0 : Fin N) (jj : Fin n → Fin N), w j0 0 ≠ 0 ∧
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0).det ≠ 0 := by
  intro n N w U hU h0 hw ⟨j0, hj0⟩ hL
  have hC : ∀ k, ContDiffAt ℂ 2 (w k) 0 := fun k =>
    ((contDiffOn_of_differentiableOn n (w k) U hU (hw k)).contDiffAt (hU.mem_nhds h0)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hD : ∀ k, DifferentiableAt ℂ (w k) 0 := fun k => (hw k).differentiableAt (hU.mem_nhds h0)
  have hne : (fun i => w i 0) ≠ 0 := fun h => hj0 (congrFun h j0)
  have hQ : ∀ k, DifferentiableAt ℂ (fun z => w k z / w j0 z) 0 := fun k => by
    simp only [div_eq_mul_inv]
    exact (hD k).mul ((differentiableAt_inv hj0).comp (0 : V n) (hD j0))
  have hker : ∀ x : V n, (∀ k, fderiv ℂ (fun z => w k z / w j0 z) 0 x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    have hξ : x.ofLp ≠ 0 := fun h => hx0 (by ext i; simpa using congrFun h i)
    have h1 := hL _ hξ
    have e1 : (fun z => ((Real.log (∑ k, ‖w k z‖ ^ 2) : ℝ) : ℂ)) =
        fun y => ((Real.log (sqNorm (fun i => w i y)) : ℝ) : ℂ) := by
      funext y; simp [sqNorm, Complex.normSq_eq_norm_sq]
    rw [e1, leviLogNormSq n N w 0 x.ofLp hC hne] at h1
    have hJ : wJac n N w 0 *ᵥ x.ofLp = (fderiv ℂ (w j0) 0 x / w j0 0) • fun i => w i 0 := by
      funext k
      rw [wJac_mulVec w 0 hD]
      have hev : w k =ᶠ[𝓝 0] fun z => (w k z / w j0 z) * w j0 z := by
        filter_upwards [(hD j0).continuousAt.eventually_ne hj0] with z hz
        rw [div_mul_cancel₀ _ hz]
      rw [hev.fderiv_eq, fderiv_fun_mul (hQ k) (hD j0)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hx k, smul_eq_mul,
        Pi.smul_apply]
      ring
    have hs : ((sqNorm (fun i => w i 0) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (sqNorm_pos hne).ne'
    have hP : projPerp (fun i => w i 0) *ᵥ (fun i => w i 0) = 0 := by
      rw [projPerp_mulVec, star_dotProduct_self, inv_mul_cancel₀ hs, one_smul, sub_self]
    rw [hJ, Matrix.mulVec_smul, hP, smul_zero] at h1
    simp [sqNorm] at h1
  obtain ⟨jj, hjj⟩ := exists_select_forms (K := ℂ) (M := V n) (n := n) (by simp)
    (fun k => (fderiv ℂ (fun z => w k z / w j0 z) 0 : V n →L[ℂ] ℂ).toLinearMap) hker
  refine ⟨j0, jj, hj0, ?_⟩
  have hF : DifferentiableAt ℂ
      (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0 :=
    differentiableAt_euclidean.2 fun k => hQ (jj k)
  rw [ContinuousLinearMap.det, Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not,
    LinearMap.ker_eq_bot']
  intro x hx
  refine hjj x fun k => ?_
  have h2 := ((EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ).hasFDerivAt.comp (0 : V n)
    hF.hasFDerivAt).fderiv
  have h3 : (fun z => w (jj k) z / w j0 z) = (EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ) ∘
      (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) := rfl
  change fderiv ℂ (fun z => w (jj k) z / w j0 z) 0 x = 0
  rw [h3, h2, ContinuousLinearMap.comp_apply]
  change (EuclideanSpace.proj (𝕜 := ℂ) k : V n →L[ℂ] ℂ) (((fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => w (jj k) z / w j0 z : V n)) 0 : V n →L[ℂ] V n) : V n →ₗ[ℂ] V n) x) = 0
  rw [hx, map_zero]

end GlobalTheory.LeviRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeOfSection
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameSplit

theorem lintegral_le_of_section {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    [ProperSpace A] [ProperSpace B]
    (μ : Measure A) [μ.IsAddHaarMeasure] (ν : Measure B) [ν.IsAddHaarMeasure]
    (L : A → B) (hL : Continuous L) (hadd : ∀ x y, L (x + y) = L x + L y)
    (s : B → A) (hs : ∀ b, L (s b) = b) (S : Set A) (hS : MeasurableSet S)
    (hinv : ∀ b x, s b + x ∈ S ↔ x ∈ S)
    (hb : ∀ C : ℝ, ∃ D : ℝ, ∀ x ∈ S, ‖L x‖ ≤ C → ‖x‖ ≤ D) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : B → ℝ≥0∞, Measurable g →
      ∫⁻ y in S, g (L y) ∂μ ≤ K * ∫⁻ z, g z ∂ν := by
  have hLm : Measurable L := hL.measurable
  set ρ : Measure B := (μ.restrict S).map L with hρ
  have happ : ∀ T : Set B, MeasurableSet T → ρ T = μ (L ⁻¹' T ∩ S) := by
    intro T hT
    rw [hρ, Measure.map_apply hLm hT, Measure.restrict_apply (hLm hT)]
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun T hT => ?_⟩
    obtain ⟨C, hC⟩ := hT.isBounded.exists_norm_le
    obtain ⟨D, hD⟩ := hb C
    rw [happ T hT.measurableSet]
    refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 D) ?_)
      (isCompact_closedBall (0 : A) D).measure_lt_top
    intro x hx
    simpa using hD x hx.2 (hC _ hx.1)
  haveI : ρ.IsAddLeftInvariant := by
    refine ⟨fun b => ?_⟩
    ext T hT
    have hm : Measurable fun z : B => b + z := (continuous_const.add continuous_id).measurable
    rw [Measure.map_apply hm hT, happ _ (hm hT), happ _ hT,
      ← measure_preimage_add μ (s b) (L ⁻¹' T ∩ S)]
    congr 1
    ext x
    simp [hadd, hs, hinv]
  refine ⟨(ρ.addHaarScalarFactor ν : ℝ≥0∞), ENNReal.coe_lt_top, fun g hg => le_of_eq ?_⟩
  rw [← lintegral_map hg hLm, ← hρ]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ρ ν]
  rw [lintegral_smul_measure]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem frameSplit : (∀ (r : ℕ) (X : Data E r) (R : ℝ), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : V (nd X) → ℝ≥0∞, Measurable g → ∫⁻ y in {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R}, g (WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1 ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2) ≤ K * ∫⁻ z, g z) := by
  intro r X R
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := inferInstance
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI h3 : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  refine lintegral_le_of_section (volume : Measure (Frame X.Ψ r)) (volume : Measure (V (nd X)))
    (fun y => WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1
      ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2)
    ?_ ?_
    (fun z τ a c => if h : c < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) else 0)
    ?_ _ ?_ ?_ ?_
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    fun_prop
  · intro x y
    ext j
    simp
  · intro z
    ext j
    have h := ((Fintype.equivFin (Ent X)).symm j).2.2
    simp only [dif_pos h]
    exact congrArg (fun k => z k) ((Fintype.equivFin (Ent X)).apply_symm_apply j)
  · apply IsClosed.measurableSet
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    fun_prop
  · intro z x
    simp only [Set.mem_setOf_eq, Pi.add_apply]
    refine forall_congr' fun τ => forall_congr' fun a => forall_congr' fun c =>
      forall_congr' fun h => ?_
    rw [dite_eq_right h, zero_add]
  · intro C
    refine ⟨max (max C R) 0, fun x hx hC => ?_⟩
    have h0 : 0 ≤ max (max C R) 0 := le_max_right _ _
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun a =>
      (pi_norm_le_iff_of_nonneg h0).2 fun c => ?_
    by_cases h : c < a
    · have := (PiLp.norm_apply_le _ ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).trans hC
      have h' : ‖x τ a c‖ ≤ C := by
        have e := (Fintype.equivFin (Ent X)).symm_apply_apply ⟨τ, ⟨(a, c), h⟩⟩
        simp only at this
        erw [e] at this
        exact this
      exact h'.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hx τ a c h).trans ((le_max_right _ _).trans (le_max_left _ _))

end GlobalTheory.FrameSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormFderivLeOfClosedBallSubset
section
open Metric

namespace GlobalTheory

theorem norm_fderiv_le_of_closedBall_subset {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {U : Set H} {f : H → ℂ} {C r : ℝ} {y : H} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hr : 0 < r) (hy : closedBall y r ⊆ U) (hC : ∀ x ∈ U, ‖f x‖ ≤ C) :
    ‖fderiv ℂ f y‖ ≤ C / r := by
  have hyU : y ∈ U := hy (mem_closedBall_self hr.le)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC y hyU)
  refine ContinuousLinearMap.opNorm_le_bound' _ (div_nonneg hC0 hr.le) fun v hv => ?_
  have hv0 : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have hR : 0 < r / ‖v‖ := div_pos hr hv0
  have hmem : ∀ t ∈ closedBall (0 : ℂ) (r / ‖v‖), y + t • v ∈ U := by
    intro t ht
    apply hy
    rw [mem_closedBall_zero_iff] at ht
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact (le_div_iff₀ hv0).1 ht
  have hlin : ∀ t : ℂ, HasDerivAt (fun s : ℂ => y + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add y
  have hd : DifferentiableOn ℂ (fun s : ℂ => f (y + s • v)) (closedBall 0 (r / ‖v‖)) := by
    intro t ht
    exact ((hf.differentiableAt (hU.mem_nhds (hmem t ht))).comp t
      (hlin t).differentiableAt).differentiableWithinAt
  have hdc : DiffContOnCl ℂ (fun s : ℂ => f (y + s • v)) (ball 0 (r / ‖v‖)) :=
    DifferentiableOn.diffContOnCl (by rwa [closure_ball _ hR.ne'])
  have hb := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdc
    (fun z hz => hC _ (hmem z (sphere_subset_closedBall hz)))
  have hder : HasDerivAt (fun s : ℂ => f (y + s • v)) (fderiv ℂ f y v) 0 := by
    have h1 : HasFDerivAt f (fderiv ℂ f y) (y + (0 : ℂ) • v) := by
      simpa using (hf.differentiableAt (hU.mem_nhds hyU)).hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hlin 0)
  rw [hder.deriv] at hb
  refine hb.trans (le_of_eq ?_)
  field_simp

theorem differentiableOn_tsum_of_norm_le :
    ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (ι : Type) (U : Set H)
      (f : ι → H → ℂ) (u : ι → ℝ), IsOpen U → (∀ i, DifferentiableOn ℂ (f i) U) → Summable u →
      (∀ i, ∀ x ∈ U, ‖f i x‖ ≤ u i) → DifferentiableOn ℂ (fun x => ∑' i, f i x) U := by
  intro H _ _ ι U f u hU hf hu hb x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hr : 0 < ε / 2 := half_pos hε
  have hsub : ∀ y ∈ ball x (ε / 2), closedBall y (ε / 2) ⊆ U := by
    intro y hy z hz
    apply hball
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hz
    linarith [dist_triangle z y x]
  have h := hasFDerivAt_tsum_of_isPreconnected (𝕜 := ℂ) (f := f)
    (f' := fun i y => fderiv ℂ (f i) y) (u := fun i => u i / (ε / 2)) (s := ball x (ε / 2))
    (x₀ := x) (x := x) (hu.div_const _) isOpen_ball (convex_ball x _).isPreconnected
    (fun i y hy => ((hf i).differentiableAt
      (hU.mem_nhds (hsub y hy (mem_closedBall_self hr.le)))).hasFDerivAt)
    (fun i y hy => norm_fderiv_le_of_closedBall_subset hU (hf i) hr (hsub y hy) (hb i))
    (mem_ball_self hr) (Summable.of_norm_bounded hu (fun i => hb i x hx)) (mem_ball_self hr)
  exact h.differentiableAt.differentiableWithinAt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one {r : ℕ} (G x : Matrix (Fin r) (Fin r) ℂ) (s : ℂ)
    (hs : s * s = 1) (h : xᵀ * G * x.map (starRingEnd ℂ) = s • (1 : Matrix (Fin r) (Fin r) ℂ))
    (a b : Fin r) : ‖x a b‖ ≤ 1 + ‖G⁻¹ a a‖ := by
  set y := x.map (starRingEnd ℂ) with hy
  have h1 : xᵀ * (s • (G * y)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, h, smul_smul, hs, one_smul]
  have h2 : (s • (G * y)) * xᵀ = 1 := mul_eq_one_comm.1 h1
  have h3 : G * (s • (y * xᵀ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul]; exact h2
  have hinv : G⁻¹ = s • (y * xᵀ) := Matrix.inv_eq_right_inv h3
  have hentry : G⁻¹ a a = s * ((∑ c, ‖x a c‖ ^ 2 : ℝ) : ℂ) := by
    rw [hinv, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hy, Matrix.transpose_apply, Complex.conj_mul']
  have hsn : ‖s‖ = 1 := by
    have h4 := congrArg norm hs
    rw [norm_mul, norm_one] at h4
    nlinarith [norm_nonneg s]
  have hsum : 0 ≤ ∑ c, ‖x a c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hnorm : ‖G⁻¹ a a‖ = ∑ c, ‖x a c‖ ^ 2 := by
    rw [hentry, norm_mul, hsn, one_mul, Complex.norm_of_nonneg hsum]
  have hle : ‖x a b‖ ^ 2 ≤ ∑ c, ‖x a c‖ ^ 2 :=
    Finset.single_le_sum (f := fun c => ‖x a c‖ ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ b)
  rw [hnorm]
  nlinarith [sq_nonneg (‖x a b‖ - 1), norm_nonneg (x a b)]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.orthonormal_frames_bounded_of_definite :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ X.p0 = r) →
      ∃ R : ℝ, ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ τ a b, ‖x τ a b‖ ≤ R) := by
  intro r X hp
  refine ⟨1 + ∑ τ : X.Ψ, ∑ a : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖,
    fun x hx τ a b => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx
  have hτ := hx τ
  obtain ⟨s, hs, hdiag⟩ : ∃ s : ℂ, s * s = 1 ∧
      Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = s • 1 := by
    rcases hp with h | h
    · refine ⟨-1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
    · refine ⟨1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
  have key : (Matrix.of (x τ))ᵀ * X.Gm.map (τ : E →+* ℂ) * (Matrix.of (x τ)).map (starRingEnd ℂ)
      = s • 1 := by
    rw [← hdiag, ← hτ]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hb := _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one _ _ s hs key a b
  have h1 : ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖ ≤ ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun a' => ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 : ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ ≤
      ∑ τ' : X.Ψ, ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun τ' : X.Ψ => ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hx' : ‖x τ a b‖ = ‖Matrix.of (x τ) a b‖ := rfl
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanNeZero
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SpanIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.SpanIndex.relIndex_span_ne_zero : (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) ≠ 0) := by
  classical
  intro r X ι _ _ w _ hw
  set V := Submodule.span E (Set.range w)
  set N := Submodule.span (𝓞 E) (Set.range w)
  set M : Submodule (𝓞 E) (Fin r → E) := X.Λ ⊓ V.restrictScalars (𝓞 E)
  have hK : X.Λ.toAddSubgroup ⊓ V.toAddSubgroup = M.toAddSubgroup := rfl
  rw [hK]
  have hMfg : M.FG := by
    haveI : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
    exact Submodule.FG.of_le_of_isNoetherian inf_le_left
  haveI : Module.Finite (𝓞 E) M := Module.Finite.iff_fg.mpr hMfg
  haveI : Module.Finite ℤ (M ⧸ N.comap M.subtype) := Module.Finite.trans (𝓞 E) _
  have htors : Module.IsTorsion ℤ (M ⧸ N.comap M.subtype) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨v, hv⟩ := x
      have hvV : v ∈ V := (Submodule.mem_inf.mp hv).2
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hvV
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image c)
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_comap]
      have hint : ∀ a, IsIntegral ℤ (y • c a) := fun a =>
        hy _ (Finset.mem_image_of_mem c (Finset.mem_univ a))
      have hsum : y • v = ∑ a, (⟨y • c a, hint a⟩ : 𝓞 E) • w a := by
        rw [← hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ext i
        change _ = ((⟨y • c a, hint a⟩ : 𝓞 E) : E) * w a i
        simp [zsmul_eq_mul, mul_assoc]
      change y • v ∈ N
      rw [hsum]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  haveI : Finite (M ⧸ N.comap M.subtype) := Module.finite_of_fg_torsion _ htors
  exact AddSubgroup.index_ne_zero_of_finite (hH := this)

end GlobalTheory.SpanIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SpanImageInfSpanImageOfLinearIndependent
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

theorem span_image_inf_span_image_of_linearIndependent {R V ι : Type} [CommRing R]
    [AddCommGroup V] [Module R V] {w : ι → V} (hw : LinearIndependent R w) (s t : Set ι) :
    Submodule.span R (w '' s) ⊓ Submodule.span R (w '' t) = Submodule.span R (w '' (s ∩ t)) := by
  apply le_antisymm
  · rintro x ⟨hs, ht⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hs
    obtain ⟨m, hm, hmx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 ht
    have hlm : l = m := hw (hlx.trans hmx.symm)
    subst hlm
    refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨l, ?_, hlx⟩
    rw [Finsupp.mem_supported] at hl hm ⊢
    exact Set.subset_inter hl hm
  · exact le_inf (Submodule.span_mono (Set.image_mono Set.inter_subset_left))
      (Submodule.span_mono (Set.image_mono Set.inter_subset_right))

theorem span_inf_sup_overlapping_parts :
    ∀ (R V α β γ : Type) [CommRing R] [AddCommGroup V] [Module R V] (w : α ⊕ β ⊕ γ → V),
      LinearIndependent R w →
      Submodule.span R (Set.range (w ∘ Sum.map id Sum.inl)) ⊓
          Submodule.span R (Set.range (w ∘ Sum.map id Sum.inr)) =
        Submodule.span R (Set.range (w ∘ Sum.inl)) ∧
      Submodule.span R (Set.range (w ∘ Sum.map id Sum.inl)) ⊔
          Submodule.span R (Set.range (w ∘ Sum.map id Sum.inr)) =
        Submodule.span R (Set.range w) := by
  intro R V α β γ _ _ _ w hw
  constructor
  · rw [Set.range_comp, Set.range_comp, Set.range_comp,
      span_image_inf_span_image_of_linearIndependent hw]
    congr 2
    ext x
    rcases x with a | b | c <;> simp
  · rw [← Submodule.span_union, Set.range_comp, Set.range_comp, ← Set.image_union,
      show (Set.range (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ) ∪
          Set.range (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) = Set.univ from by
        ext x
        rcases x with a | b | c <;> simp, Set.image_univ]

end GlobalTheory
end

