module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.AbsTwoMulInnerLeOfNormSubEqInfDist
section
noncomputable section

open Module Submodule
open scoped InnerProductSpace

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem exists_int_comb_norm_sub_sq_le (k : ℕ) (v : Fin k → E) {x : E}
    (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  induction k generalizing x with
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | succ k ih =>
    set U : Submodule ℝ E := span ℝ (Set.range (Fin.init v)) with hU
    have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℝ).1 hx
    set a := c (Fin.last k)
    set u := v (Fin.last k)
    set y := ∑ i : Fin k, c i.castSucc • v i.castSucc with hy
    have hyU : y ∈ U := sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
    set p := U.starProjection u
    have hpU : p ∈ U := U.starProjection_apply_mem u
    have hq : u - p ∈ Uᗮ := U.sub_starProjection_mem_orthogonal u
    set t : ℝ := a - round a
    have ht : |t| ≤ 1 / 2 := abs_sub_round a
    obtain ⟨w, hw, hle⟩ := ih (Fin.init v) (x := y + t • p) (add_mem hyU (smul_mem _ _ hpU))
    have hwU : w ∈ U := span_subset_span ℤ ℝ _ hw
    refine ⟨w + round a • u, add_mem (span_mono ?_ hw) (smul_mem _ _ (subset_span ⟨_, rfl⟩)), ?_⟩
    · rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩
    have e : ∑ i, c i • v i - (w + round a • u) = (y + t • p - w) + t • (u - p) := by
      rw [Fin.sum_univ_castSucc, ← Int.cast_smul_eq_zsmul ℝ]
      simp only [t]; module
    have hz : y + t • p - w ∈ U := sub_mem (add_mem hyU (smul_mem _ _ hpU)) hwU
    have horth : ⟪y + t • p - w, t • (u - p)⟫_ℝ = 0 :=
      U.inner_right_of_mem_orthogonal hz (smul_mem _ _ hq)
    have hup : ‖u - p‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have h1 : ⟪p, u - p⟫_ℝ = 0 := U.inner_right_of_mem_orthogonal hpU hq
      have h2 := norm_add_sq_real p (u - p)
      rw [add_sub_cancel, h1] at h2
      nlinarith [sq_nonneg ‖p‖]
    have ht2 : t ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    rw [e, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Fin.sum_univ_castSucc]
    have : t ^ 2 * ‖u - p‖ ^ 2 ≤ 1 / 4 * ‖u‖ ^ 2 :=
      mul_le_mul ht2 hup (sq_nonneg _) (by norm_num)
    have hle' : ‖y + t • p - w‖ ^ 2 ≤ (∑ i : Fin k, ‖v i.castSucc‖ ^ 2) / 4 := hle
    linarith

variable {L : Submodule ℤ E}

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EventuallyIteratedFDerivEqZeroOfRealSubspace
section
open Metric Set Filter
open scoped Topology

namespace GlobalTheory.SCV

section General

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem fderiv_apply_eq_zero_of_frequently {f : E → V} {x s : E} (hf : DifferentiableAt ℂ f x)
    (h : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (x + t • s) = f x) : fderiv ℂ f x s = 0 := by
  have h1 : HasDerivAt (fun t : ℂ => f (x + t • s)) (fderiv ℂ f x s) 0 :=
    hf.hasFDerivAt.hasLineDerivAt s
  rw [hasDerivAt_iff_tendsto_slope_zero] at h1
  refine tendsto_nhds_unique_of_frequently_eq h1 tendsto_const_nhds (h.mono fun t ht => ?_)
  simp [ht]

theorem frequently_nhdsNE_of_eventually_ofReal {p : ℂ → Prop}
    (h : ∀ᶠ t : ℝ in 𝓝 0, p t) : ∃ᶠ t in 𝓝[≠] (0 : ℂ), p t := by
  have h1 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  exact h1.frequently (h.filter_mono nhdsWithin_le_nhds).frequently

theorem fderiv_eq_zero_of_real_lines {f : E → V} {x : E} {S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hf : DifferentiableAt ℂ f x)
    (h : ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (x + (t : ℂ) • s) = f x) : fderiv ℂ f x = 0 := by
  have : (fderiv ℂ f x : E →ₗ[ℂ] V) = 0 :=
    LinearMap.ext_on hS fun s hs => fderiv_apply_eq_zero_of_frequently hf
      (frequently_nhdsNE_of_eventually_ofReal (p := fun t => f (x + t • s) = f x) (h s hs))
  ext v
  exact LinearMap.congr_fun this v

theorem eq_of_eventually_real_lines {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ᶠ t : ℝ in 𝓝 0, f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w :=
  hU.is_const_of_fderiv_eq_zero hU' hf
    (fun x hx => fderiv_eq_zero_of_real_lines hS (hf.differentiableAt (hU.mem_nhds hx)) (h x hx))
    hz hw

theorem eq_of_invariant_real_lines {f : E → V} {U S : Set E}
    (hS : Submodule.span ℂ S = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ s ∈ S, ∀ t : ℝ, z + (t : ℂ) • s ∈ U → f (z + (t : ℂ) • s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_eventually_real_lines hS hU hU' hf (fun x hx s hs => ?_) hz hw
  have h1 : Tendsto (fun t : ℝ => x + (t : ℂ) • s) (𝓝 0) (𝓝 x) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  exact (h1.eventually (hU.mem_nhds hx)).mono fun t ht => h x hx s hs t ht

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem eq_of_invariant_realSubspace {f : E → V} {U : Set E} {S : Submodule ℝ E}
    (hS : Submodule.span ℂ (S : Set E) = ⊤) (hU : IsOpen U) (hU' : IsPreconnected U)
    (hf : DifferentiableOn ℂ f U) (h : ∀ z ∈ U, ∀ s ∈ S, z + s ∈ U → f (z + s) = f z)
    {z w : E} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_real_lines hS hU hU' hf (fun x hx s hs t ht => h x hx _ ?_ ht) hz hw
  rw [show (t : ℂ) • s = t • s from algebraMap_smul ℂ t s]
  exact S.smul_mem t hs

variable [FiniteDimensional ℂ E] [CompleteSpace V]

end General

section Coordinates

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]

noncomputable def scaledRealPoints (ι : Type*) (a : ℂ) : Submodule ℝ (ι → ℂ) where
  carrier := {z | ∃ x : ι → ℝ, z = fun i => a * x i}
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by ext i; simp [mul_add]⟩
  zero_mem' := ⟨0, by ext i; simp⟩
  smul_mem' := by
    rintro t _ ⟨x, rfl⟩
    exact ⟨t • x, by ext i; simp [mul_left_comm]⟩


omit [Fintype ι] in
theorem span_scaledRealPoints {a : ℂ} (ha : a ≠ 0) :
    Submodule.span ℂ (scaledRealPoints ι a : Set (ι → ℂ)) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  have e : z = a⁻¹ • (fun i => a * ((z i).re : ℂ))
      + (a⁻¹ * Complex.I) • (fun i => a * ((z i).im : ℂ)) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Complex.re_add_im (z i)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
      Complex.mul_im, zero_add]
    field_simp
  rw [e]
  exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

theorem eq_of_invariant_real {f : (ι → ℂ) → V} {U : Set (ι → ℂ)}
    (hU : IsOpen U) (hU' : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (h : ∀ z ∈ U, ∀ x : ι → ℝ, (z + fun i => (x i : ℂ)) ∈ U → f (z + fun i => (x i : ℂ)) = f z)
    {z w : ι → ℂ} (hz : z ∈ U) (hw : w ∈ U) : f z = f w := by
  refine eq_of_invariant_realSubspace (span_scaledRealPoints one_ne_zero) hU hU' hf ?_ hz hw
  rintro y hy _ ⟨x, rfl⟩
  simpa only [one_mul] using h y hy x

variable [CompleteSpace V]

end Coordinates

end GlobalTheory.SCV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsLinearIndependentSqrtEqSuccMinQuad
section
noncomputable section

open Module Submodule

namespace GlobalTheory

section General

variable {K : Type*} [DivisionRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {N : V → ℝ} {S : Set V} {n : ℕ}

theorem mem_span_of_lt_succMinOf {v : Fin n → V} (hv : LinearIndependent K v) (hS : ∀ j, v j ∈ S)
    (hN : ∀ j : Fin n, N (v j) ≤ succMinOf K N S (j + 1)) {i : ℕ} (hi : i ≤ n) {x : V}
    (hx : x ∈ S) (hx0 : 0 ≤ N x) (h : N x < succMinOf K N S (i + 1)) :
    x ∈ span K (v '' {j | (j : ℕ) < i}) := by
  have hrank : (n : Cardinal) ≤ Module.rank K (span K S) :=
    natCast_le_rank_span_iff.2 ⟨v, hv, hS⟩
  have key : ∀ i ≤ n, succMinOf K N S i ≤ N x → N x < succMinOf K N S (i + 1) →
      x ∈ span K (v '' {j | (j : ℕ) < i}) := by
    intro i hi h1 h2
    by_contra hx'
    have hw : LinearIndependent K (fun j : Fin i => v (Fin.castLE hi j)) :=
      hv.comp _ (Fin.castLE_injective hi)
    have hr : Set.range (fun j : Fin i => v (Fin.castLE hi j)) = v '' {j | (j : ℕ) < i} := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨_, j.2, rfl⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨⟨j, hj⟩, rfl⟩
    have hli : LinearIndependent K
        (Fin.cons x (fun j : Fin i => v (Fin.castLE hi j)) : Fin (i + 1) → V) :=
      linearIndependent_finCons.2 ⟨hw, by rwa [hr]⟩
    refine absurd (succMinOf_le_of_linearIndependent (N := N) (S := S) (i := i + 1) hli (by simp)
      hx0 ?_ ?_) (not_le.2 h2)
    · intro k
      refine Fin.cases hx (fun j => hS _) k
    · intro k
      refine Fin.cases le_rfl (fun j => ?_) k
      exact (hN _).trans ((succMinOf_mono (show (j : ℕ) + 1 ≤ i from j.2)
        ((Nat.cast_le.2 hi).trans hrank)).trans h1)
  induction i with
  | zero => exact key 0 hi (succMinOf_zero.le.trans hx0) h
  | succ m ih =>
    rcases lt_or_ge (N x) (succMinOf K N S (m + 1)) with h1 | h1
    · have hsub : {j : Fin n | (j : ℕ) < m} ⊆ {j : Fin n | (j : ℕ) < m + 1} :=
        fun j hj => Nat.lt_succ_of_lt hj
      exact span_mono (Set.image_mono hsub) (ih (Nat.le_of_succ_le hi) h1)
    · exact key (m + 1) hi h1 h

theorem exists_linearIndependent_eq_succMinOf (hfin : ∀ R, {x | x ∈ S ∧ N x ≤ R}.Finite)
    (hN : ∀ x ∈ S, 0 ≤ N x) (hn : (n : Cardinal) ≤ Module.rank K (span K S)) :
    ∃ v : Fin n → V, LinearIndependent K v ∧ (∀ j, v j ∈ S) ∧
      ∀ j : Fin n, N (v j) = succMinOf K N S (j + 1) := by
  induction n with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0, fun j => j.elim0⟩
  | succ m ih =>
    obtain ⟨v, hv, hS, hvN⟩ := ih ((Nat.cast_le.2 (Nat.le_succ m)).trans hn)
    obtain ⟨-, w, hw, hwS⟩ := mem_succMinRadii_iff.1 (succMinOf_mem hfin hn)
    obtain ⟨k, hk⟩ : ∃ k, w k ∉ span K (Set.range v) := by
      by_contra! h
      have h1 : span K (Set.range w) ≤ span K (Set.range v) :=
        span_le.2 (Set.range_subset_iff.2 h)
      have : Module.Finite K (span K (Set.range v)) :=
        Module.Finite.span_of_finite K (Set.finite_range v)
      have h2 := Submodule.finrank_mono h1
      rw [finrank_span_eq_card hw, finrank_span_eq_card hv] at h2
      simp at h2
    have hk' : N (w k) = succMinOf K N S (m + 1) := by
      refine le_antisymm (hwS k).2 (not_lt.1 fun h => hk ?_)
      exact span_mono (Set.image_subset_range _ _)
        (mem_span_of_lt_succMinOf hv hS (fun j => (hvN j).le) le_rfl (hwS k).1
          (hN _ (hwS k).1) h)
    refine ⟨Fin.snoc v (w k), linearIndependent_finSnoc.2 ⟨hv, hk⟩, fun j => ?_, fun j => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using (hwS k).1
      · simpa using hS j
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using hk'
      · simpa using hvN j

end General

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}

theorem mem_span_of_norm_lt_succMin {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : ‖x‖ < succMin L (i + 1)) : x ∈ span ℝ (v '' {j | (j : ℕ) < i}) :=
  mem_span_of_lt_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E)) hv hL hN hi hx
    (norm_nonneg x) h

theorem succMin_le_norm_of_notMem_span {v : Fin n → E} (hv : LinearIndependent ℝ v)
    (hL : ∀ j, v j ∈ L) (hN : ∀ j : Fin n, ‖v j‖ ≤ succMin L (j + 1)) {i : ℕ} (hi : i ≤ n) {x : E}
    (hx : x ∈ L) (h : x ∉ span ℝ (v '' {j | (j : ℕ) < i})) : succMin L (i + 1) ≤ ‖x‖ :=
  not_lt.1 fun h' => h (mem_span_of_norm_lt_succMin hv hL hN hi hx h')

variable [FiniteDimensional ℝ E] [DiscreteTopology L]

theorem exists_linearIndependent_norm_eq_succMin (hn : n ≤ finrank ℝ (span ℝ (L : Set E))) :
    ∃ v : Fin n → E, LinearIndependent ℝ v ∧ (∀ j, v j ∈ L) ∧
      ∀ j : Fin n, ‖v j‖ = succMin L (j + 1) :=
  exists_linearIndependent_eq_succMinOf (N := fun x : E => ‖x‖) (S := (L : Set E))
    (finite_mem_and_norm_le L) (fun x _ => norm_nonneg x) (natCast_le_rank_of_le_finrank hn)

variable (L) [IsZLattice ℝ L]

theorem exists_basis_norm_eq_succMin :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, (∀ j, b j ∈ L) ∧
      ∀ j : Fin (finrank ℝ E), ‖b j‖ = succMin L (j + 1) := by
  obtain ⟨v, hv, hL, hN⟩ :=
    exists_linearIndependent_norm_eq_succMin (L := L) (finrank_span_of_isZLattice L).ge
  have htop : ⊤ ≤ span ℝ (Set.range v) := by
    rw [top_le_iff]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  exact ⟨Basis.mk hv htop, by simpa using hL, by simpa using hN⟩

end Normed

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {Q : QuadraticForm ℝ V} {L : Submodule ℤ V}
  {n : ℕ}

end Quadratic

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsNeZeroForallNormLeOfCovolumeLe
section
open NumberField Module MeasureTheory Metric Set
open scoped Real ENNReal

namespace GlobalTheory

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]


set_option backward.isDefEq.respectTransparency.types false in
theorem covolume_eq_relIndex_mul_of_haar (L' L : Submodule ℤ V) [DiscreteTopology L']
    [IsZLattice ℝ L'] [DiscreteTopology L] [IsZLattice ℝ L] (h : L' ≤ L) :
    ZLattice.covolume L' μ =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L μ := by
  classical
  let b : Basis (Fin (finrank ℝ V)) ℤ L := finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)
  let b' : Basis (Fin (finrank ℝ V)) ℤ L' := finBasisOfFinrankEq ℤ L' (ZLattice.rank ℝ L')
  rw [AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b,
    Nat.cast_natAbs, Int.cast_abs,
    ZLattice.covolume_eq_det_mul_measureReal L' μ b' (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)]
  congr 2
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b.ofZLatticeBasis_repr_apply ℝ L ⟨b' j, h (SetLike.coe_mem _)⟩ i)

end Lattice

section Strip

end Strip

section TotallyComplex

open InfinitePlace

end TotallyComplex

section CM

open InfinitePlace IsCMField
open scoped nonZeroDivisors

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

end CM

section Constant

end Constant

section Balls

variable {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℝ (W i)] [∀ i, FiniteDimensional ℝ (W i)]
  [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

end Balls

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.GaussianSumOfOneSeparatedOfLe
section
open Metric MeasureTheory Module Set Real

namespace GlobalTheory

theorem finset_sum_exp_neg_le_of_card_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {t C : ℝ}
    (hf : ∀ i ∈ s, t ≤ f i)
    (hc : ∀ u, t ≤ u → ((s.filter fun i => f i ≤ u).card : ℝ) ≤ C * exp ((u - t) / 2)) :
    ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := by
  have hint : IntegrableOn (fun u : ℝ => exp (-u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi t)
  have h1 : ∀ i ∈ s, exp (-f i) =
      ∫ u in Ici t, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u := by
    intro i hi
    rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, sup_eq_right.2 (hf i hi),
      integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi]
  have hint2 : IntegrableOn (fun u : ℝ => exp (-(1 / 2) * u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (exp_neg_integrableOn_Ioi t (by norm_num))
  rw [Finset.sum_congr rfl h1, ← MeasureTheory.integral_finsetSum _
    (fun i _ => hint.indicator measurableSet_Ici)]
  calc ∫ u in Ici t, ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u
      ≤ ∫ u in Ici t, (C * exp (-t / 2)) * exp (-(1 / 2) * u) := by
        refine setIntegral_mono_on
          (MeasureTheory.integrable_finsetSum _ fun i _ => hint.indicator measurableSet_Ici)
          (hint2.const_mul _) measurableSet_Ici fun u hu => ?_
        have e : ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u =
            ((s.filter fun i => f i ≤ u).card : ℝ) * exp (-u) := by
          simp only [indicator, mem_Ici]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [e]
        calc _ ≤ C * exp ((u - t) / 2) * exp (-u) :=
              mul_le_mul_of_nonneg_right (hc u hu) (exp_pos _).le
          _ = _ := by
              rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add]; congr 2; ring
    _ = 2 * C * exp (-t) := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
          integral_exp_mul_Ioi (by norm_num)]
        have : exp (-t) = exp (-t / 2) * exp (-(1 / 2) * t) := by
          rw [← exp_add]; congr 1; ring
        rw [this]; ring

theorem summable_exp_neg_of_card_le {ι : Type*} (f : ι → ℝ) {t C : ℝ} (hf : ∀ i, t ≤ f i)
    (hc : ∀ (s : Finset ι) u, t ≤ u → (∀ i ∈ s, f i ≤ u) → (s.card : ℝ) ≤ C * exp ((u - t) / 2)) :
    Summable (fun i => exp (-f i)) ∧ ∑' i, exp (-f i) ≤ 2 * C * exp (-t) := by
  have key : ∀ s : Finset ι, ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := fun s =>
    finset_sum_exp_neg_le_of_card_le s f (fun i _ => hf i) fun u hu =>
      hc _ u hu fun i hi => (Finset.mem_filter.1 hi).2
  have hs := summable_of_sum_le (fun i => (exp_pos (-f i)).le) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end GlobalTheory
end

