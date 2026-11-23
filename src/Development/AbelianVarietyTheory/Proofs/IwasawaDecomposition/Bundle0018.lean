module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatMemSpanOfRealMemSpanFin
section
open Matrix

namespace GlobalTheory

theorem rat_mem_span_of_real_mem_span (k r : ℕ) (w : Fin k → Fin r → ℚ) (v : Fin r → ℚ)
    (hv : (fun j => ((v j : ℚ) : ℝ)) ∈ Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ))) :
    v ∈ Submodule.span ℚ (Set.range w) := by
  by_contra hnot
  obtain ⟨f, hfv, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  classical
  set a : Fin r → ℚ := fun j => f (fun k => if j = k then 1 else 0) with ha
  have hf : ∀ x : Fin r → ℚ, f x = ∑ j, x j * a j := by
    intro x
    conv_lhs => rw [pi_eq_sum_univ x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  have hw : ∀ i, f (w i) = 0 := by
    intro i
    have : f (w i) ∈ (Submodule.span ℚ (Set.range w)).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    rw [hfp] at this
    exact (Submodule.mem_bot ℚ).mp this
  let L : (Fin r → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ j, x j * (a j : ℝ)
      map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.mul_sum, mul_assoc] }
  have hle : Submodule.span ℝ (Set.range fun i j => ((w i j : ℚ) : ℝ)) ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    show ∑ j, ((w i j : ℚ) : ℝ) * (a j : ℝ) = 0
    have h := hw i
    rw [hf] at h
    have h' : ((∑ j, w i j * a j : ℚ) : ℝ) = 0 := by rw [h]; simp
    push_cast at h'
    exact h'
  have h0 : L (fun j => ((v j : ℚ) : ℝ)) = 0 := LinearMap.mem_ker.mp (hle hv)
  have h1 : ((f v : ℚ) : ℝ) = 0 := by
    rw [hf]
    push_cast
    exact h0
  exact hfv (by exact_mod_cast h1)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RightTranslationCurveSqLeAndIntegralDerivEqZeroA
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem integral_intervalIntegral_mul_right_curve {K : Type} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsMulRightInvariant] [IsProbabilityMeasure μ]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E]
    (c : ℝ → K) (hc : Continuous c) (g : K → E) (hg : Continuous g) :
    ∫ x, (∫ t in (0:ℝ)..1, g (x * c t)) ∂μ = ∫ x, g x ∂μ := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hg).isBounded.exists_norm_le
  have hcont : Continuous (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t)) := by
    unfold Function.uncurry
    fun_prop
  have hint : Integrable (Function.uncurry fun (x : K) (t : ℝ) => g (x * c t))
      (μ.prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable C (Eventually.of_forall fun p => ?_)
    exact hC _ ⟨_, Set.mem_univ _, rfl⟩
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  rw [integral_integral_swap hint]
  simp_rw [integral_mul_right_eq_self g]
  simp

theorem norm_intervalIntegral_unit_sq_le (h : ℝ → ℂ) (hh : Continuous h) :
    ‖∫ t in (0:ℝ)..1, h t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1, ‖h t‖ ^ 2 := by
  set a : ℝ := ∫ t in (0:ℝ)..1, ‖h t‖ with ha
  have h1 : ‖∫ t in (0:ℝ)..1, h t‖ ≤ a :=
    intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have h2 : 0 ≤ ∫ t in (0:ℝ)..1, (‖h t‖ - a) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
  have hn : Continuous fun t => ‖h t‖ := hh.norm
  have h3 : ∫ t in (0:ℝ)..1, (‖h t‖ - a) ^ 2
      = (∫ t in (0:ℝ)..1, ‖h t‖ ^ 2) - a ^ 2 := by
    have e : ∀ t, (‖h t‖ - a) ^ 2 = (‖h t‖ ^ 2 - 2 * a * ‖h t‖) + a ^ 2 := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, ← ha]
    · simp; ring
    all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _
  have h4 : ‖∫ t in (0:ℝ)..1, h t‖ ^ 2 ≤ a ^ 2 := by
    gcongr
  linarith

theorem right_translation_curve_sq_le_and_integral_deriv_eq_zero :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [T2Space K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure]
      [μ.IsMulRightInvariant] [IsProbabilityMeasure μ] (c : ℝ → K), Continuous c → c 0 = 1 →
      ∀ f f' : K → ℂ, Continuous f → Continuous f' →
      (∀ x t, HasDerivAt (fun t : ℝ => f (x * c t)) (f' (x * c t)) t) →
      (∫ x, ‖f (x * c 1) - f x‖ ^ 2 ∂μ ≤ ∫ x, ‖f' x‖ ^ 2 ∂μ) ∧ ∫ x, f' x ∂μ = 0 := by
  intro K _ _ _ _ _ _ _ μ _ _ _ c hc h0 f f' hf hf' hd
  have key : ∀ x, f (x * c 1) - f x = ∫ t in (0:ℝ)..1, f' (x * c t) := by
    intro x
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd x t)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp [h0]
  have hI : ∀ {E : Type} [NormedAddCommGroup E] [SecondCountableTopology E] (g : K → E),
      Continuous g → Integrable g μ :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  constructor
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc (fun x => ‖f' x‖ ^ 2) (by fun_prop)]
    refine integral_mono (hI _ (by fun_prop)) (hI _ ?_) fun x => ?_
    · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun (x : K) (t : ℝ) => ‖f' (x * c t)‖ ^ 2)
        (by unfold Function.uncurry; fun_prop) 0 1
    · simp only [key]
      exact norm_intervalIntegral_unit_sq_le _ (by fun_prop)
  · rw [← integral_intervalIntegral_mul_right_curve μ c hc f' hf']
    simp_rw [← key]
    rw [integral_sub (hI _ (by fun_prop)) (hI _ hf), integral_mul_right_eq_self f, sub_self]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLtTopOfEssFiniteType
section
open IsLocalRing

namespace GlobalTheory

open IsLocalRing in
private theorem ringKrullDim_le_of_isLocalization (A D : Type) [CommRing A] [CommRing D]
    [Algebra A D] (M : Submonoid A) [IsLocalization M D] :
    ringKrullDim D ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A D)) ?_
  refine Monotone.strictMono_of_injective (fun p q h => ?_)
    (PrimeSpectrum.localization_comap_injective D M)
  exact Ideal.comap_mono h

open IsLocalRing in
private theorem ringKrullDim_finite_of_finiteType_int (A : Type) [CommRing A]
    [Algebra.FiniteType ℤ A] : ringKrullDim A < ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective f.toRingHom hf) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have h : ((1 + Nat.card (Fin n) : ℕ) : WithBot ℕ∞) < ⊤ :=
    WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  push_cast [ENat.card_eq_coe_natCard]
  exact h


open IsLocalRing in
theorem _root_.GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D] :
    ringKrullDim D < ⊤ :=
  lt_of_le_of_lt
    (ringKrullDim_le_of_isLocalization (Algebra.EssFiniteType.subalgebra ℤ D) D
      (Algebra.EssFiniteType.submonoid ℤ D))
    (ringKrullDim_finite_of_finiteType_int _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurComplementBlockQuadraticLowerBound
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory

theorem schur_scalar_bound (u w C₀ c₀ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) :
    u ^ 2 + w ^ 2 ≤ (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) *
      ((1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2) := by
  set α := C₀ / c₀ with hα
  have hα0 : 0 ≤ α := div_nonneg hC hc.le
  set p := w - α * u with hp
  have e : (1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2 = u ^ 2 + c₀ * p ^ 2 := by
    rw [hp, hα]; field_simp; ring
  have hw : w = p + α * u := by rw [hp]; ring
  have h1 : u ^ 2 + w ^ 2 ≤ (1 + α) ^ 2 * (u ^ 2 + p ^ 2) := by
    rw [hw]
    nlinarith [mul_nonneg hα0 (sq_nonneg (p - u)), mul_nonneg hα0 (sq_nonneg u),
      mul_nonneg (mul_nonneg hα0 hα0) (sq_nonneg u), mul_nonneg hα0 (sq_nonneg p),
      mul_nonneg (mul_nonneg hα0 hα0) (sq_nonneg p)]
  set M := max 1 (1 / c₀) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMc : 1 ≤ M * c₀ := by
    have : 1 / c₀ ≤ M := le_max_right _ _
    rw [div_le_iff₀ hc] at this; linarith
  have h2 : u ^ 2 + p ^ 2 ≤ M * (u ^ 2 + c₀ * p ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hM1 (sq_nonneg u),
      mul_le_mul_of_nonneg_right hMc (sq_nonneg p)]
  rw [e]
  calc u ^ 2 + w ^ 2 ≤ (1 + α) ^ 2 * (u ^ 2 + p ^ 2) := h1
    _ ≤ (1 + α) ^ 2 * (M * (u ^ 2 + c₀ * p ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = _ := by ring

theorem dot_sq_le (n : ℕ) (x v : Fin n → ℝ) : (x ⬝ᵥ v) ^ 2 ≤ (x ⬝ᵥ x) * (v ⬝ᵥ v) := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x v
  simpa [dotProduct, sq] using this

theorem dot_self_nonneg' (n : ℕ) (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

theorem schur_block_lower_bound : ∀ (k l : ℕ) (a bt : Matrix (Fin k) (Fin k) ℝ) (b : Matrix (Fin k) (Fin l) ℝ) (d : Matrix (Fin l) (Fin l) ℝ) (C₀ c₀ b₀ : ℝ), 0 ≤ C₀ → 0 < c₀ → 0 < b₀ → a.IsSymm → d.IsSymm → bt.IsSymm → (∀ x, |x ⬝ᵥ a.mulVec x| ≤ C₀ * (x ⬝ᵥ x)) → (∀ y, (b.mulVec y) ⬝ᵥ (b.mulVec y) ≤ C₀ ^ 2 * (y ⬝ᵥ y)) → (∀ y, c₀ * (y ⬝ᵥ y) ≤ y ⬝ᵥ d.mulVec y) → (∀ x, b₀ * (x ⬝ᵥ x) ≤ x ⬝ᵥ bt.mulVec x) → ∀ z : Fin k ⊕ Fin l → ℝ, ((1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀))⁻¹ * (z ⬝ᵥ z) ≤ z ⬝ᵥ (Matrix.fromBlocks (a + ((1 + C₀ + C₀ ^ 2 / c₀) / b₀) • bt) b b.transpose d).mulVec z := by
  intro k l a bt b d C₀ c₀ b₀ hC hc hb _ _ _ ha hbb hd hbt z
  set x : Fin k → ℝ := z ∘ Sum.inl with hx
  set y : Fin l → ℝ := z ∘ Sum.inr with hy
  set L := (1 + C₀ + C₀ ^ 2 / c₀) / b₀ with hL
  have hsum : ∀ (f g : Fin k ⊕ Fin l → ℝ), f ⬝ᵥ g = (f ∘ Sum.inl) ⬝ᵥ (g ∘ Sum.inl) + (f ∘ Sum.inr) ⬝ᵥ (g ∘ Sum.inr) := by
    intro f g; simp [dotProduct, Fintype.sum_sum_type]
  have htr : y ⬝ᵥ b.transpose.mulVec x = x ⬝ᵥ b.mulVec y := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hexp : z ⬝ᵥ (Matrix.fromBlocks (a + L • bt) b b.transpose d).mulVec z
      = x ⬝ᵥ a.mulVec x + L * (x ⬝ᵥ bt.mulVec x) + 2 * (x ⬝ᵥ b.mulVec y) + y ⬝ᵥ d.mulVec y := by
    rw [hsum, fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [← hx, ← hy, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_add, dotProduct_add,
      dotProduct_smul, htr, smul_eq_mul]
    ring
  have hzz : z ⬝ᵥ z = x ⬝ᵥ x + y ⬝ᵥ y := hsum z z
  rw [hexp, hzz]
  set U := x ⬝ᵥ x
  set W := y ⬝ᵥ y
  have hU : 0 ≤ U := dot_self_nonneg' k x
  have hW : 0 ≤ W := dot_self_nonneg' l y
  set u := Real.sqrt U
  set w := Real.sqrt W
  have hu : u ^ 2 = U := Real.sq_sqrt hU
  have hw : w ^ 2 = W := Real.sq_sqrt hW
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _

  have hQ : |x ⬝ᵥ b.mulVec y| ≤ C₀ * u * w := by
    have h1 := dot_sq_le k x (b.mulVec y)
    have h2 := hbb y
    have h3 : (x ⬝ᵥ b.mulVec y) ^ 2 ≤ (C₀ * u * w) ^ 2 := by
      calc (x ⬝ᵥ b.mulVec y) ^ 2 ≤ U * (b.mulVec y ⬝ᵥ b.mulVec y) := h1
        _ ≤ U * (C₀ ^ 2 * W) := mul_le_mul_of_nonneg_left h2 hU
        _ = (C₀ * u * w) ^ 2 := by rw [← hu, ← hw]; ring
    exact abs_le_of_sq_le_sq' h3 (by positivity) |>.2 |> fun h => abs_le.mpr ⟨(abs_le_of_sq_le_sq' h3 (by positivity)).1, h⟩
  have hT : -(C₀ * U) ≤ x ⬝ᵥ a.mulVec x := by
    have := ha x; exact (abs_le.mp this).1
  have hB : (1 + C₀ + C₀ ^ 2 / c₀) * U ≤ L * (x ⬝ᵥ bt.mulVec x) := by
    have h := hbt x
    have hL0 : 0 ≤ L := by rw [hL]; positivity
    calc (1 + C₀ + C₀ ^ 2 / c₀) * U = L * (b₀ * U) := by rw [hL]; field_simp
      _ ≤ L * (x ⬝ᵥ bt.mulVec x) := mul_le_mul_of_nonneg_left h hL0
  have hD := hd y
  have hQ' := (abs_le.mp hQ).1
  have key := schur_scalar_bound u w C₀ c₀ hC hc
  have hK : 0 < (1 + C₀ / c₀) ^ 2 * max 1 (1 / c₀) := by
    have : 0 < 1 + C₀ / c₀ := by have := div_nonneg hC hc.le; linarith
    exact mul_pos (pow_pos this 2) (lt_of_lt_of_le one_pos (le_max_left _ _))
  rw [inv_mul_le_iff₀ hK]
  have hS : (1 + C₀ ^ 2 / c₀) * u ^ 2 - 2 * C₀ * u * w + c₀ * w ^ 2 ≤
      x ⬝ᵥ a.mulVec x + L * (x ⬝ᵥ bt.mulVec x) + 2 * (x ⬝ᵥ b.mulVec y) + y ⬝ᵥ d.mulVec y := by
    rw [hu, hw]; nlinarith
  calc U + W = u ^ 2 + w ^ 2 := by rw [hu, hw]
    _ ≤ _ := key
    _ ≤ _ := mul_le_mul_of_nonneg_left hS hK.le

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurOrthogonalitySubgroupMeasureOne
section
open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.SchurOrthOnSubgroup

theorem setIntegral_subgroup_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G) (hΩ : MeasurableSet (Ω : Set G))
    (f : G → ℂ) {h : G} (hh : h ∈ Ω) :
    ∫ g in (Ω : Set G), f (h * g) ∂ν = ∫ g in (Ω : Set G), f g ∂ν := by
  rw [← integral_indicator hΩ, ← integral_indicator hΩ]
  have : (Ω : Set G).indicator (fun g => f (h * g)) = fun g => (Ω : Set G).indicator f (h * g) := by
    funext g
    by_cases hg : g ∈ Ω
    · have hg' : h * g ∈ Ω := Ω.mul_mem hh hg
      simp [Set.indicator_of_mem, hg, hg']
    · have hg' : h * g ∉ Ω := fun H => hg ((Ω.mul_mem_cancel_left hh).1 H)
      simp [Set.indicator_of_notMem, hg, hg']
  rw [this, integral_mul_left_eq_self]

variable {G : Type} [Group G] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem rep_apply_inv_apply (ρ : G →* Module.End ℂ W) (g : G) (v : W) : ρ g (ρ g⁻¹ v) = v := by
  show (ρ g * ρ g⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]; rfl

theorem inner_rep_inv (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (x y : W) : ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
  rw [← hU g (ρ g⁻¹ x) y, rep_apply_inv_apply]

theorem inner_rep_inv' (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (x y : W) : ⟪x, ρ g⁻¹ y⟫_ℂ = ⟪ρ g x, y⟫_ℂ := by
  rw [← hU g x (ρ g⁻¹ y), rep_apply_inv_apply]

theorem norm_rep (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (v : W) : ‖ρ g v‖ = ‖v‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hU]

end GlobalTheory.SchurOrthOnSubgroup

namespace GlobalTheory.SchurOrthOnSubgroup

theorem schur_orthogonality {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G) (hΩ : MeasurableSet (Ω : Set G))
    (hν : ν (Ω : Set G) = 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W)
    (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hM : ∀ x y : W, Measurable fun g => ⟪x, ρ g y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ W, (∀ g ∈ Ω, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤)
    (a a' x x' : W) :
    IntegrableOn (fun g => star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ) Ω ν ∧
      (Module.finrank ℂ W : ℂ) * ∫ g in (Ω : Set G), star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ ∂ν
        = ⟪a', a⟫_ℂ * ⟪x, x'⟫_ℂ := by

  set F : W → W → G → ℂ := fun y y' g => star ⟪a, ρ g⁻¹ y⟫_ℂ * ⟪a', ρ g⁻¹ y'⟫_ℂ with hF
  have hfin : ν (Ω : Set G) < ⊤ := by rw [hν]; exact ENNReal.one_lt_top
  have hint : ∀ y y', IntegrableOn (F y y') Ω ν := by
    intro y y'
    have hmeas : Measurable (F y y') := by
      have h1 : Measurable fun g : G => ⟪a, ρ g⁻¹ y⟫_ℂ := (hM a y).comp measurable_inv
      have h2 : Measurable fun g : G => ⟪a', ρ g⁻¹ y'⟫_ℂ := (hM a' y').comp measurable_inv
      exact (continuous_star.measurable.comp h1).mul h2
    refine Integrable.mono' (g := fun _ => (‖a‖ * ‖y‖) * (‖a'‖ * ‖y'‖)) ?_
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    · exact integrableOn_const hfin.ne
    · simp only [hF, norm_mul, norm_star]
      gcongr
      · exact (norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])
      · exact (norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])
  refine ⟨hint x x', ?_⟩

  set B : W → W → ℂ := fun y y' => ∫ g in (Ω : Set G), F y y' g ∂ν with hB
  let b := stdOrthonormalBasis ℂ W
  have hBadd : ∀ y y1 y2, B y (y1 + y2) = B y y1 + B y y2 := by
    intro y y1 y2
    simp only [hB]
    rw [← integral_add (hint y y1) (hint y y2)]
    congr 1; funext g
    simp only [hF, map_add (f := _), inner_add_right, mul_add]
  have hBsmul : ∀ y (c : ℂ) y', B y (c • y') = c * B y y' := by
    intro y c y'
    simp only [hB]
    rw [← integral_const_mul]
    congr 1; funext g
    simp only [hF, map_smul, inner_smul_right]; ring
  have hBexp : ∀ y y', B y y' = ∑ i, ⟪y, b i⟫_ℂ * B (b i) y' := by
    intro y y'
    simp only [hB]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ => (hint (b i) y').const_mul _)]
    congr 1; funext g
    simp only [hF]
    have hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ := by
      intro z
      rw [inner_rep_inv' ρ hU]
      exact inner_conj_symm _ _
    simp_rw [hs, ← mul_assoc, ← Finset.sum_mul]
    rw [b.sum_inner_mul_inner]
  have hBinv : ∀ h ∈ Ω, ∀ y y', B (ρ h y) (ρ h y') = B y y' := by
    intro h hh y y'
    simp only [hB]
    rw [← setIntegral_subgroup_mul_left ν Ω hΩ (F y y') (Ω.inv_mem hh)]
    congr 1; funext g
    have hg : ∀ z, ρ g⁻¹ (ρ h z) = ρ (h⁻¹ * g)⁻¹ z := by
      intro z
      rw [mul_inv_rev, inv_inv, map_mul]; rfl
    simp only [hF, hg]

  let T : W →ₗ[ℂ] W :=
    { toFun := fun y' => ∑ i, B (b i) y' • b i
      map_add' := by
        intro y1 y2
        simp only [hBadd, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c y'
        simp only [hBsmul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hT : ∀ y y', ⟪y, T y'⟫_ℂ = B y y' := by
    intro y y'
    rw [hBexp y y']
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]
    congr 1; funext i; ring
  have hcomm : ∀ h ∈ Ω, ∀ v, T (ρ h v) = ρ h (T v) := by
    intro h hh v
    apply ext_inner_left ℂ
    intro y
    rw [hT, ← inner_rep_inv ρ hU, hT]
    conv_lhs => rw [← rep_apply_inv_apply ρ h y]
    exact hBinv h hh _ _
  have hsum : ∑ i, B (b i) (b i) = ⟪a', a⟫_ℂ := by
    simp only [hB]
    rw [← integral_finsetSum _ (fun i _ => hint (b i) (b i))]
    have : ∀ g, ∑ i, F (b i) (b i) g = ⟪a', a⟫_ℂ := by
      intro g
      simp only [hF]
      have hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ := by
        intro z
        rw [inner_rep_inv' ρ hU]
        exact inner_conj_symm _ _
      simp_rw [hs, inner_rep_inv' ρ hU]
      simp_rw [mul_comm (⟪b _, ρ g a⟫_ℂ)]
      rw [b.sum_inner_mul_inner, hU]
    simp_rw [this]
    rw [setIntegral_const, Measure.real, hν]
    simp
  rcases subsingleton_or_nontrivial W with hW | hW
  · have ha : a = 0 := Subsingleton.elim _ _
    simp [Module.finrank_zero_of_subsingleton, ha]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ W)
  have hU' : Module.End.eigenspace (T : Module.End ℂ W) c = ⊤ := by
    rcases hirr (Module.End.eigenspace (T : Module.End ℂ W) c) (by
      intro g hg
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
      rw [Module.End.mem_eigenspace_iff, hcomm g hg, hv, map_smul]) with h0 | h0
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have : v ∈ Module.End.eigenspace (T : Module.End ℂ W) c := hv.1
      rw [h0, Submodule.mem_bot] at this
      exact hv.2 this
    · exact h0
  have hTc : ∀ v, T v = c • v := fun v =>
    Module.End.mem_eigenspace_iff.1 (hU' ▸ Submodule.mem_top)
  have hBc : ∀ y y', B y y' = c * ⟪y, y'⟫_ℂ := by
    intro y y'
    rw [← hT, hTc, inner_smul_right]
  have hnc : (Module.finrank ℂ W : ℂ) * c = ⟪a', a⟫_ℂ := by
    rw [← hsum]
    have h1 : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
      simpa using orthonormal_iff_ite.1 b.orthonormal i i
    simp only [hBc, h1, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  show (Module.finrank ℂ W : ℂ) * B x x' = _
  rw [hBc, ← mul_assoc, hnc]

end GlobalTheory.SchurOrthOnSubgroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanMkQOneTmul
section
namespace GlobalTheory.SpanQuotientTensor

theorem span_mkQ_one_tmul {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (F : Type) [Field F] [Algebra K F] (N : Submodule F (TensorProduct K F D)) :
    Submodule.span F (Set.range (fun x : D => N.mkQ ((1 : F) ⊗ₜ[K] x))) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := N.mkQ_surjective q
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : (a ⊗ₜ[K] x : TensorProduct K F D) = a • ((1 : F) ⊗ₜ[K] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add y z hy hz =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz

theorem main : (let d1 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (U →+* F) → Submodule F (TensorProduct LL F D) := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ ⨆ (c : U), LinearMap.range (LinearMap.baseChange F ((m : U → Module.End LL D) c) - (τ : U → F) c • LinearMap.id)); let d2 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [Algebra LL F] → (U →+* F) → Type := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ TensorProduct LL F D ⧸ d1 m F τ); let d3 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → TensorProduct LL F D →ₗ[F] d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ Submodule.mkQ (d1 m F τ)); let d4 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → D → d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) (x : D) ↦ (d3 m F τ : TensorProduct LL F D → d2 m F τ) ((1 : F) ⊗ₜ[LL] x)); ∀ {LL U D : Type} [inst : Field LL] [inst_1 : Field U] [inst_2 : AddCommGroup D] [inst_3 : Module LL D] (m : U →+* Module.End LL D) (F : Type) [inst_4 : Field F] [inst_5 : Algebra LL F] (τ : U →+* F), Submodule.span F (Set.range (d4 m F τ)) = ⊤) := by
  intro d1 d2 d3 d4 LL U D _ _ _ _ m F _ _ τ
  exact span_mkQ_one_tmul F (d1 m F τ)

end GlobalTheory.SpanQuotientTensor
end

