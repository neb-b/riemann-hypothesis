module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddSubgroupFiniteQuotOfCommensurable
section
namespace GlobalTheory

theorem addSubgroup_finite_quot_of_commensurable : ∀ (V : Type) [AddCommGroup V] (A L : AddSubgroup V) (N M : ℕ), 0 < N → 0 < M → (∀ v : V, N • v = 0 → v = 0) → (∀ a ∈ A, N • a ∈ L) → (∀ l ∈ L, M • l ∈ A) → (∀ j : ℕ, 0 < j → ∃ R : Finset V, ∀ u ∈ L, ∃ r ∈ R, ∃ v ∈ L, u = r + j • v) → ∀ k : ℕ, 0 < k → ∃ R : Finset V, ∀ u ∈ A, ∃ r ∈ R, ∃ v ∈ A, u = r + k • v := by
  classical
  intro V _ A L N M hN hM htf hAL hLA hfin k hk
  obtain ⟨R₀, hR₀⟩ := hfin (k * N * M) (by positivity)
  let P : V → Prop := fun r₀ => ∃ a ∈ A, ∃ w ∈ L, N • a = r₀ + (k * N * M) • w
  let f : V → V := fun r₀ => if h : P r₀ then h.choose else 0
  refine ⟨R₀.image f, ?_⟩
  intro u hu
  obtain ⟨r₀, hr₀, v, hv, huv⟩ := hR₀ (N • u) (hAL u hu)
  have hP : P r₀ := ⟨u, hu, v, hv, huv⟩
  have hf : f r₀ = hP.choose := dif_pos hP
  obtain ⟨haA, w, hwL, haw⟩ := hP.choose_spec
  refine ⟨f r₀, Finset.mem_image_of_mem f hr₀, M • (v - w), hLA _ (L.sub_mem hv hwL), ?_⟩
  rw [hf]
  have key : N • (u - (hP.choose + k • M • (v - w))) = 0 := by
    have e : N • k • M • (v - w) = (k * N * M) • (v - w) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [smul_sub, smul_add, huv, haw, e, smul_sub]
    abel
  exact sub_eq_zero.mp (htf _ key)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdicCompletionValuationMapUniformiser
section
open ValuativeRel NumberField IsDedekindDomain

namespace GlobalTheory

theorem adicCompletion_valuation_map_uniformiser : ∀ (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (φ : k ≃+* v.adicCompletion F), (∀ a, Valued.v (φ a) ≤ 1 ↔ a ∈ 𝒪[k]) → ∀ ϖ : 𝒪[k], Irreducible ϖ → Valued.v (φ (ϖ : k)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  intro F _ _ v k _ _ _ _ φ hφ ϖ hϖ

  have hnu : ∀ c : 𝒪[k], Valued.v (φ (c : k)) < 1 → ¬ IsUnit c := by
    intro c hc hu
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hw' : φ (c : k) * φ (w : k) = 1 := by
      rw [← map_mul, ← map_one φ]
      congr 1
      exact_mod_cast congrArg (fun t : 𝒪[k] => (t : k)) hw
    have h1 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) = 1 := by
      rw [← map_mul, hw', map_one]
    have h2 : Valued.v (φ (w : k)) ≤ 1 := (hφ _).2 w.2
    have h3 : Valued.v (φ (c : k)) * Valued.v (φ (w : k)) ≤ Valued.v (φ (c : k)) * 1 :=
      by gcongr
    rw [h1, mul_one] at h3
    exact absurd hc (not_lt.2 h3)
  set x := φ (ϖ : k) with hxdef
  have hϖ0 : (ϖ : k) ≠ 0 := by
    intro h; exact hϖ.ne_zero (Subtype.ext h)
  have hx0 : x ≠ 0 := by
    simpa [hxdef] using hϖ0
  have hvx0 : Valued.v x ≠ 0 := by
    simpa using hx0
  have hvx1 : Valued.v x < 1 := by
    have hle : Valued.v x ≤ 1 := (hφ _).2 ϖ.2
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hϖ.not_isUnit
    have hinv : ((ϖ : k))⁻¹ ∈ 𝒪[k] := by
      refine (hφ _).1 ?_
      rw [map_inv₀, map_inv₀, ← hxdef, heq, inv_one]
    refine IsUnit.of_mul_eq_one (b := (⟨_, hinv⟩ : 𝒪[k])) ?_
    apply Subtype.ext
    simp [mul_inv_cancel₀ hϖ0]
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  have hlt1 : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe]
    show (-1 : ℤ) < 0
    norm_num
  have hvπ0 : Valued.v π₀ ≠ 0 := by rw [hπ₀]; exact WithZero.coe_ne_zero
  have hπ0 : π₀ ≠ 0 := by
    intro h; apply hvπ0; rw [h, map_zero]
  set a := φ.symm π₀ with hadef
  have hφa : φ a = π₀ := by simp [hadef]
  have ha0 : a ≠ 0 := by
    intro h; apply hπ0; rw [← hφa, h, map_zero]
  have ha : a ∈ 𝒪[k] := (hφ a).1 (by rw [hφa, hπ₀]; exact hlt1.le)
  apply le_antisymm
  · obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 hvx0
    rw [← hm] at hvx1 ⊢
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hvx1
    rw [WithZero.coe_le_coe]
    have h1 : Multiplicative.toAdd m < 0 := hvx1
    show Multiplicative.toAdd m ≤ -1
    omega
  · by_contra hcon
    rw [not_le] at hcon
    set b := (ϖ : k) / a with hbdef
    have hφb : Valued.v (φ b) < 1 := by
      rw [hbdef, map_div₀, hφa, map_div₀, ← hxdef, div_lt_one₀ (pos_iff_ne_zero.2 hvπ0), hπ₀]
      exact hcon
    have hb : b ∈ 𝒪[k] := (hφ b).1 hφb.le
    have hprod : ϖ = (⟨a, ha⟩ : 𝒪[k]) * ⟨b, hb⟩ := by
      apply Subtype.ext
      show (ϖ : k) = a * ((ϖ : k) / a)
      rw [mul_div_cancel₀ _ ha0]
    rcases hϖ.isUnit_or_isUnit hprod with h | h
    · exact hnu ⟨a, ha⟩ (by rw [hφa, hπ₀]; exact hlt1) h
    · exact hnu ⟨b, hb⟩ hφb h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CardValLt
section
namespace GlobalTheory.CardValuationLt

theorem card_val_lt : ∀ (N n : ℕ), n ≤ N → Finset.card {i : Fin N | (↑i : ℕ) < n} = n := by
  intro N n h
  have hmap : ({i : Fin N | (↑i : ℕ) < n} : Finset (Fin N)).map Fin.valEmbedding = Finset.range n := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hm
      exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]

end GlobalTheory.CardValuationLt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspace
section
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuous_rankOne_self : Continuous fun w : H => rankOne ℂ w w := by
  have h : (fun w : H => rankOne ℂ w w) =
      fun w => ContinuousLinearMap.smulRightL ℂ H H (innerSL ℂ w) w := by
    funext w
    ext z
    simp [rankOne_apply]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℂ H H).continuous₂.comp
    ((innerSL ℂ).continuous.prodMk continuous_id)

theorem isCompactOperator_rankOne_self (w : H) : IsCompactOperator (rankOne ℂ w w) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ w)).comp_clm (innerSL ℂ w)

theorem convex_compactOperators : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := by
  exact ((compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ).convex

variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}

theorem isCompactOperator_integral [IsProbabilityMeasure μ] {F : X → H →L[ℂ] H}
    (hFi : Integrable F μ) (hF : ∀ k, IsCompactOperator (F k)) :
    IsCompactOperator (∫ k, F k ∂μ : H →L[ℂ] H) := by
  have hs : IsClosed {f : H →L[ℂ] H | IsCompactOperator f} := isClosed_setOfPred_isCompactOperator
  have hc : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := convex_compactOperators
  have hae : ∀ᵐ k ∂μ, F k ∈ {f : H →L[ℂ] H | IsCompactOperator f} := Filter.Eventually.of_forall hF
  have hm := hc.integral_mem hs hae hFi
  exact hm

theorem inner_integral_rankOne {w : X → H} (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ)
    (x y : H) : ⟪y, (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) x⟫_ℂ =
      ∫ k, ⟪w k, x⟫_ℂ * ⟪y, w k⟫_ℂ ∂μ := by
  have hix : Integrable (fun k => rankOne ℂ (w k) (w k) x) μ :=
    (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
  rw [ContinuousLinearMap.integral_apply hFi x, ← integral_inner hix y]
  simp only [rankOne_apply, inner_smul_right]

theorem isSymmetric_integral_rankOne {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_integral_rankOne hFi x y, inner_integral_rankOne hFi y x,
    ← integral_conj]
  congr 1
  funext k
  rw [map_mul, inner_conj_symm, inner_conj_symm, mul_comm]

theorem integral_rankOne_ne_zero {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) (v : H)
    (hpos : 0 < ∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) ≠ 0 := by
  intro h0
  have h := inner_integral_rankOne hFi v v
  rw [h0, zero_apply, inner_zero_right] at h
  have h3 : ∫ k, ⟪w k, v⟫_ℂ * ⟪v, w k⟫_ℂ ∂μ = ((∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext k
    rw [← inner_conj_symm (w k) v, Complex.conj_mul']
    push_cast
    rfl
  rw [h3] at h
  exact hpos.ne' (by exact_mod_cast h.symm)

end

theorem exists_finiteDimensional_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
      [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] (π : K →* (H →L[ℂ] H)), (∀ k x, ‖π k x‖ = ‖x‖) →
      (∀ x, Continuous fun k => π k x) →
      ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ ∀ k, ∀ x ∈ S, π k x ∈ S := by
  intro K _ _ _ _ _ _ H _ _ _ _ π hnorm hcont
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ : ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant ∧
      μ.IsOpenPosMeasure := by
    refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance, inferInstance⟩
    simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hw : Continuous fun k => π k v := hcont v
  have hFc : Continuous fun k => rankOne ℂ (π k v) (π k v) := continuous_rankOne_self.comp hw
  have hFi : Integrable (fun k => rankOne ℂ (π k v) (π k v)) μ :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTc : IsCompactOperator (∫ k, rankOne ℂ (π k v) (π k v) ∂μ : H →L[ℂ] H) :=
    isCompactOperator_integral hFi (fun k => isCompactOperator_rankOne_self _)
  have hTs := isSymmetric_integral_rankOne hFi
  have hpos : 0 < ∫ k, ‖⟪v, π k v⟫_ℂ‖ ^ 2 ∂μ := by
    have hc : Continuous fun k => ‖⟪v, π k v⟫_ℂ‖ ^ 2 :=
      ((continuous_const.inner hw).norm).pow 2
    refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (x := 1) ?_
    simp [hv]
  have hT0 := integral_rankOne_ne_zero hFi v hpos
  set T : H →L[ℂ] H := ∫ k, rankOne ℂ (π k v) (π k v) ∂μ with hT
  obtain ⟨c, hc, hc0⟩ : ∃ c, Module.End.HasEigenvalue (T : Module.End ℂ H) c ∧ c ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hT0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).mp hno)
  have hinner : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    LinearIsometry.inner_map_map ⟨(π g).toLinearMap, hnorm g⟩ x y
  have hcomm : ∀ g x, T (π g x) = π g (T x) := by
    intro g x
    have hix : Integrable (fun k => rankOne ℂ (π k v) (π k v) x) μ :=
      (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
    have hsh := integral_mul_left_eq_self (μ := μ)
      (fun k => rankOne ℂ (π k v) (π k v) (π g x)) g
    rw [hT, ContinuousLinearMap.integral_apply hFi, ContinuousLinearMap.integral_apply hFi,
      ← ContinuousLinearMap.integral_comp_comm (π g) hix, ← hsh]
    congr 1
    funext k
    have hm : ∀ a b : K, ∀ y, π (a * b) y = π a (π b y) := fun a b y => by rw [map_mul]; rfl
    simp only [rankOne_apply, hm, hinner, map_smul]
  refine ⟨Module.End.eigenspace (T : Module.End ℂ H) c, Module.End.hasEigenvalue_iff.mp hc,
    ContinuousLinearMap.finite_dimensional_eigenspace hTc c hc0, ?_⟩
  intro k x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  change T (π k x) = c • π k x
  change T x = c • x at hx
  rw [hcomm, hx, map_smul]

end GlobalTheory.CompactRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffCompactAverageOfClosedPartials
section
open MeasureTheory
open scoped ContDiff

noncomputable section

namespace GlobalTheory.AvgSmooth

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] {n : ℕ}

theorem integrable_cont (μ : Measure K) [IsFiniteMeasure μ] {f : K → ℂ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))

def coordC (n : ℕ) (i : Fin n) : (Fin n → ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).smulRight (1 : ℂ)

theorem clm_expand (L : (Fin n → ℝ) →L[ℝ] ℂ) : L = ∑ i, L (Pi.single i 1) • coordC n i := by
  ext1 u
  have e : L u = ∑ i, u i • L (Pi.single i 1) := by
    conv_lhs => rw [← Finset.univ_sum_single u]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_smul]
    congr 1
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [e]
  simp [coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]

theorem hasFDerivAt_avg (μ : Measure K) [IsFiniteMeasure μ] {F : K → (Fin n → ℝ) → ℂ}
    {G : Fin n → K → (Fin n → ℝ) → ℂ} (hF : Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2)
    (hG : ∀ i, Continuous fun p : K × (Fin n → ℝ) => G i p.1 p.2) (hd : ∀ k, Differentiable ℝ (F k))
    (he : ∀ i k t, fderiv ℝ (F k) t (Pi.single i 1) = G i k t) (t₀ : Fin n → ℝ) :
    HasFDerivAt (fun t => ∫ k, F k t ∂μ) (∑ i, (∫ k, G i k t₀ ∂μ) • coordC n i) t₀ := by
  have hFk : ∀ t, Continuous fun k => F k t := fun t => hF.comp (continuous_id.prodMk continuous_const)
  have hGk : ∀ i t, Continuous fun k => G i k t := fun i t => (hG i).comp (continuous_id.prodMk continuous_const)
  have hM : ∀ i, ∃ M : ℝ, ∀ p ∈ (Set.univ : Set K) ×ˢ Metric.closedBall t₀ 1, ‖G i p.1 p.2‖ ≤ M := fun i =>
    (isCompact_univ.prod (isCompact_closedBall t₀ 1)).exists_bound_of_continuousOn (hG i).continuousOn
  choose M hM using hM
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun t k => F k t) (F' := fun t k => ∑ i, G i k t • coordC n i)
    (bound := fun _ => ∑ i, M i * ‖coordC n i‖) (Metric.ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall fun t => (hFk t).aestronglyMeasurable)
    (integrable_cont μ (hFk t₀))
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hGk i t₀).aestronglyMeasurable.smul_const _)
    (Filter.Eventually.of_forall fun k t ht => by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul]
      gcongr
      exact hM i (k, t) ⟨Set.mem_univ _, Metric.ball_subset_closedBall ht⟩)
    (integrable_const _)
    (Filter.Eventually.of_forall fun k t _ => by
      have h := (hd k t).hasFDerivAt
      rw [clm_expand (fderiv ℝ (F k) t)] at h
      simpa only [he] using h)
  refine key.congr_fderiv ?_
  rw [MeasureTheory.integral_finsetSum _ fun i _ => (integrable_cont μ (hGk i t₀)).smul_const _]
  exact Finset.sum_congr rfl fun i _ => integral_smul_const _ _

end GlobalTheory.AvgSmooth


open GlobalTheory.AvgSmooth in
theorem GlobalTheory.AvgSmooth.main : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  intro K _ _ _ _ μ _ n φ hφ 𝒢 hc hd hder
  have hk : ∀ F ∈ 𝒢, ∀ t, Integrable (fun k => F k t) μ := fun F hF t =>
    integrable_cont μ ((hc F hF).comp (continuous_id.prodMk continuous_const))
  have hD : ∀ F ∈ 𝒢, ∃ F' : Fin n → K → (Fin n → ℝ) → ℂ, (∀ i, F' i ∈ 𝒢) ∧ ∀ t₀,
      HasFDerivAt (fun t => ∫ k, F k t ∂μ)
        (∑ i, ((∫ k, F' i k t₀ ∂μ) + φ i t₀ * ∫ k, F k t₀ ∂μ) • coordC n i) t₀ := by
    intro F hF
    choose F' hF' he using hder F hF
    refine ⟨F', hF', fun t₀ => ?_⟩
    have h := hasFDerivAt_avg μ (G := fun i k t => F' i k t + φ i t * F k t) (hc F hF)
      (fun i => (hc _ (hF' i)).add (((hφ i).continuous.comp continuous_snd).mul (hc F hF))) (hd F hF) he t₀
    refine h.congr_fderiv (Finset.sum_congr rfl fun i _ => ?_)
    rw [integral_add (hk _ (hF' i) t₀) ((hk F hF t₀).const_mul _), integral_const_mul]
  have main : ∀ m : ℕ, ∀ F ∈ 𝒢, ContDiff ℝ m fun t => ∫ k, F k t ∂μ := by
    intro m
    induction m with
    | zero =>
      intro F hF
      obtain ⟨F', -, h⟩ := hD F hF
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (h t).continuousAt)
    | succ m ih =>
      intro F hF
      obtain ⟨F', hF', h⟩ := hD F hF
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]
      refine ⟨_, ?_, h⟩
      refine ContDiff.sum fun i _ => ContDiff.smul_const ?_ _
      exact (ih _ (hF' i)).add ((contDiff_infty.1 (hφ i) m).mul (ih F hF))
  intro F hF
  exact contDiff_infty.2 fun m => main m F hF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DifferentiableAtLimitOfDirectionalDerivsConverge
section
open scoped ContDiff Topology

namespace GlobalTheory

open Filter

theorem tendstoLocallyUniformly_sum_smul_const {E : Type} [TopologicalSpace E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {A : Type} (s : Finset A) (L : A → F)
    (f : A → ℕ → E → ℂ) (ψ : A → E → ℂ)
    (h : ∀ a, TendstoLocallyUniformly (f a) (ψ a) atTop) :
    TendstoLocallyUniformly (fun j y => ∑ a ∈ s, f a j y • L a)
      (fun y => ∑ a ∈ s, ψ a y • L a) atTop := by
  classical
  have hterm : ∀ a, TendstoLocallyUniformly (fun j y => f a j y • L a)
      (fun y => ψ a y • L a) atTop := by
    intro a
    have hu : UniformContinuous (fun z : ℂ => z • L a) :=
      ((ContinuousLinearMap.id ℂ ℂ).smulRight (L a)).uniformContinuous
    exact hu.comp_tendstoLocallyUniformly (h a)
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact fun u hu x => ⟨Set.univ, Filter.univ_mem,
      Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hterm a).add ih

theorem differentiableAt_of_tendstoLocallyUniformly_directional :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  intro E _ _ A _ v c hvc φ g ψ hg hφ hψ y
  classical
  have hdecomp : (fun j z => fderiv ℝ (g j) z) =
      fun j z => ∑ a, fderiv ℝ (g j) z (v a) • (c a).smulRight (1 : ℂ) := by
    funext j z
    refine ContinuousLinearMap.ext fun x => ?_
    conv_lhs => rw [← hvc x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.real_smul, mul_comm]
  have hconv : TendstoLocallyUniformly (fun j z => fderiv ℝ (g j) z)
      (fun z => ∑ a, ψ a z • (c a).smulRight (1 : ℂ)) Filter.atTop := by
    rw [hdecomp]
    exact tendstoLocallyUniformly_sum_smul_const Finset.univ (fun a => (c a).smulRight (1 : ℂ))
      (fun a j z => fderiv ℝ (g j) z (v a)) ψ hψ
  have hfd : HasFDerivAt φ (∑ a, ψ a y • (c a).smulRight (1 : ℂ)) y :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (hconv.tendstoLocallyUniformlyOn (s := Set.univ))
      (fun n z _ => (hg n z).hasFDerivAt)
      (fun z _ => (hφ.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ z))
      (Set.mem_univ y)
  refine ⟨hfd.differentiableAt, fun a => ?_⟩
  rw [hfd.fderiv]
  have h1 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop
      (𝓝 ((∑ b, ψ b y • (c b).smulRight (1 : ℂ)) (v a))) :=
    ((ContinuousLinearMap.apply ℝ ℂ (v a)).continuous.tendsto _).comp
      ((hconv.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y))
  have h2 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop (𝓝 (ψ a y)) :=
    ((hψ a).tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y)
  exact tendsto_nhds_unique h1 h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOneOfNormPowTwoPowSubOneLt
section
namespace GlobalTheory.NormPowerTwoUnity

lemma norm_sq_sub_one_ge (w : ℂ) (h : ‖w - 1‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w + 1) * (w - 1) := by ring
  have h2 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    rw [this]
    exact norm_sub_le _ _
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith

theorem eq_one_of_norm_pow_two_pow_sub_one_lt (z : ℂ)
    (h : ∀ (m : ℕ), ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖ < (1 / 2 : ℝ)) : z = (1 : ℂ) := by
  have key : ∀ m : ℕ, (3 / 2 : ℝ) ^ m * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖ := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      have h1 := norm_sq_sub_one_ge _ (h n)
      rw [← pow_mul, ← pow_succ] at h1
      calc (3 / 2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2 : ℝ) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3 / 2) * ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ := by linarith
        _ ≤ _ := h1
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (show (1 : ℝ) < 3 / 2 by norm_num)
  rw [div_lt_iff₀ hpos] at hm
  have := key m
  have := h m
  linarith

end GlobalTheory.NormPowerTwoUnity
end

