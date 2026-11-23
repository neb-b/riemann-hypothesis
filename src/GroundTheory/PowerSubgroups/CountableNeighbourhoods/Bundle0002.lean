module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.UnitMulPowAdic
section
namespace GroundTheory.Variant₂.N1

open IsLocalRing

theorem exists_eq_unit_mul_pow_adicCompletion {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ϖ : R} (hϖ : Irreducible ϖ)
    {x : AdicCompletion (maximalIdeal R) R} (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : (AdicCompletion (maximalIdeal R) R)ˣ),
      x = ↑u * (algebraMap R (AdicCompletion (maximalIdeal R) R)) ϖ ^ n := by

  have hM : maximalIdeal (AdicCompletion (maximalIdeal R) R) =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ} := by
    have e := congrArg (Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)))
      hϖ.maximalIdeal_eq
    rw [AdicCompletion.maximalIdeal_eq_map, e, Ideal.map_span, Set.image_singleton]
  have hMpow : ∀ k : ℕ, maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k =
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ ^ k} := fun k => by
    rw [hM, Ideal.span_singleton_pow]

  have hex : ∃ k : ℕ, x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ k := by
    by_contra h
    push Not at h
    apply hx
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff
      (I := maximalIdeal (AdicCompletion (maximalIdeal R) R))
      (M := AdicCompletion (maximalIdeal R) R)) x
    intro k
    simpa only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero] using h k
  classical
  have hk : x ∉ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ Nat.find hex :=
    Nat.find_spec hex
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hk
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hxn : x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ^ n := by
    have := Nat.find_min hex (show n < Nat.find hex by omega)
    simpa using this
  rw [hMpow, Ideal.mem_span_singleton'] at hxn
  obtain ⟨y, hy⟩ := hxn
  have hyu : IsUnit y := by
    rw [← notMem_maximalIdeal]
    intro hyM
    apply hk
    rw [hn, hMpow, Ideal.mem_span_singleton']
    rw [hM, Ideal.mem_span_singleton'] at hyM
    obtain ⟨z, hz⟩ := hyM
    exact ⟨z, by rw [← hy, ← hz, pow_succ]; ring⟩
  exact ⟨n, hyu.unit, by rw [IsUnit.unit_spec, hy]⟩

end GroundTheory.Variant₂.N1
end

-- bundled from GroundTheory.PowerSubgroups.CountableNeighbourhoods.UnramifiedClosureCountableNeighbourhoods
section
namespace GroundTheory.Variant₂.N1

theorem exists_lt_norm_pow_sub_pow_lt {p : ℕ} [hp : Fact (Nat.Prime p)] {c : PadicAlgCl p}
    (hc : ‖c‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) (f : ℕ → ℕ) :
    ∃ (k₀ : ℕ) (k₁ : ℕ), k₀ < k₁ ∧ ‖c ^ f k₁ - c ^ f k₀‖ < ε := by
  set S : Submodule ℚ_[p] (PadicAlgCl p) :=
    Subalgebra.toSubmodule (Algebra.adjoin ℚ_[p] {c}) with hS
  have hint : IsIntegral ℚ_[p] c := Algebra.IsIntegral.isIntegral c
  have : FiniteDimensional ℚ_[p] S := Module.Finite.iff_fg.mpr hint.fg_adjoin_singleton
  have : ProperSpace S := FiniteDimensional.proper ℚ_[p] S
  have hmem : ∀ n : ℕ, c ^ n ∈ S := fun n =>
    Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℚ_[p] c) n
  let x : ℕ → S := fun k => ⟨c ^ f k, hmem _⟩
  have hx : ∀ k, x k ∈ Metric.closedBall (0 : S) 1 := by
    intro k
    rw [mem_closedBall_zero_iff]
    change ‖c ^ f k‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hc
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : S) 1).tendsto_subseq hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  have h1 : dist (x (φ (N + 1))) a < ε / 2 := hN (N + 1) (Nat.le_succ N)
  have h2 : dist (x (φ N)) a < ε / 2 := hN N le_rfl
  have h3 : dist (x (φ (N + 1))) (x (φ N)) < ε :=
    calc dist (x (φ (N + 1))) (x (φ N)) ≤ dist (x (φ (N + 1))) a + dist (x (φ N)) a :=
          dist_triangle_right _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h1 h2
      _ = ε := add_halves ε
  rw [dist_eq_norm] at h3
  exact h3

end GroundTheory.Variant₂.N1
end

